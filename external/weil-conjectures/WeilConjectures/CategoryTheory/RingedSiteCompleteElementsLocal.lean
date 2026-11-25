/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestriction
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-! # Restriction of complete local sections

Source: Stacks Project, Tags 0997 and 0998.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

namespace CategoryTheory

noncomputable local instance sliceDerivedCategory
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [hU : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))] :
    Category.{w} (@DerivedCategory
      (SheafOfModules.{u}
        ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U))) _ _ hU) :=
  inferInstanceAs (Category.{w} (DerivedCategory
    (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))))

private theorem overMap_preservesColimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{u}) {U V : C} (a : V ⟶ U) :
    PreservesColimitsOfShape ℕ (SheafOfModules.overMap.{u} O a) := by
  let G := Over.map a
  let H := G.sheafPushforwardContinuous AddCommGrpCat.{u} (J.over V) (J.over U)
  have : PreservesColimitsOfSize.{u, u} H :=
    (G.sheafAdjunctionCocontinuous AddCommGrpCat.{u} (J.over V)
      (J.over U)).leftAdjoint_preservesColimits
  let T := SheafOfModules.toSheaf.{u} (O.over V)
  have : PreservesColimitsOfShape ℕ (SheafOfModules.toSheaf.{u} (O.over U)) := by
    infer_instance
  have : PreservesColimitsOfSize.{0, 0} H :=
    preservesSmallestColimits_of_preservesColimits H
  have : PreservesColimitsOfShape ℕ (SheafOfModules.overMap.{u} O a ⋙ T) := by
    change PreservesColimitsOfShape ℕ (SheafOfModules.toSheaf.{u} (O.over U) ⋙ H)
    infer_instance
  have : ReflectsColimitsOfShape ℕ T :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _ T

private noncomputable def localization_overMap_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{u}) {U V : C} (a : V ⟶ U) (f : O.obj.obj (op U)) :
    (SheafOfModules.overMap.{u} O a).obj (ringedSiteSectionLocalization O U f) ≅
      ringedSiteSectionLocalization O V (O.obj.map a.op f) := by
  let F := SheafOfModules.overMap.{u} O a
  let M := SheafOfModules.unit (O.over U)
  let N := SheafOfModules.unit (O.over V)
  let t : M ⟶ M := M.unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun W ↦ O.obj.map W.unop.hom.op f)
      (fun {W W'} b ↦ ringedSiteSectionLocalization_compatible O U f W W' b))
  let t' : N ⟶ N := N.unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun W ↦ O.obj.map W.unop.hom.op (O.obj.map a.op f))
      (fun {W W'} b ↦ ringedSiteSectionLocalization_compatible O V
        (O.obj.map a.op f) W W' b))
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ t)
  let E := Functor.ofSequence (X := fun _ : ℕ ↦ N) (fun _ ↦ t')
  have ht : F.map t = t' := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change O.obj.obj (op W.unop.left) at x
    change x * O.obj.map (W.unop.hom ≫ a).op f =
      x * O.obj.map W.unop.hom.op (O.obj.map a.op f)
    rw [op_comp, O.obj.map_comp]
    rfl
  let α : D ⋙ F ⟶ E := NatTrans.ofSequence (fun _ ↦ 𝟙 _)
    (fun n ↦ by simpa [D, E] using ht)
  let e : D ⋙ F ≅ E := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun b ↦ α.naturality b)
  have := overMap_preservesColimits O a
  exact preservesColimitIso F D ≪≫ HasColimit.isoOfNatIso e

private theorem module_zero_of_cover
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{u}) (U : C) (S : Sieve U) (hS : S ∈ J U)
    (M : SheafOfModules.{u} (O.over U))
    (hM : ∀ (V : C) (a : V ⟶ U), S a →
      IsZero ((SheafOfModules.overMap.{u} O a).obj M)) : IsZero M := by
  have hpoint (B : Over U) (hB : S B.hom) :
      Subsingleton (M.val.obj (op B)) := by
    obtain ⟨V, a, rfl⟩ := B.mk_surjective
    have hz := ((SheafOfModules.forget (O.over V)) ⋙
      (PresheafOfModules.evaluation (O.over V).obj (op (Over.mk (𝟙 V))))).map_isZero
        (hM V a hB)
    have hs := ModuleCat.isZero_iff_subsingleton.mp hz
    change Subsingleton (M.val.obj (op (Over.mk (𝟙 V ≫ a)))) at hs
    have hs' : Subsingleton (M.val.obj (op (Over.mk (𝟙 V ≫ a)))) := hs
    rw [Category.id_comp] at hs'
    exact hs'
  apply (IsZero.iff_id_eq_zero M).mpr
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change x = 0
  let T := (Sieve.overEquiv W.unop).symm (S.pullback W.unop.hom)
  have hT : T ∈ (J.over U) W.unop :=
    J.overEquiv_symm_mem_over W.unop _ (J.pullback_stable W.unop.hom hS)
  apply M.isSheaf.isSeparated W.unop T hT
  intro B b hb
  have hB : S B.hom := by
    have hh : S (b.left ≫ W.unop.hom) := hb
    simpa only [Over.w b] using hh
  exact (hpoint B hB).elim _ _

private theorem derived_zero_of_cover
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (U : C) (S : Sieve U) (hS : S ∈ J U)
    (N : DerivedCategory (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)))
    (hN : ∀ (V : C) (a : V ⟶ U), S a →
      IsZero ((SheafOfModules.overMap.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) a).mapDerivedCategory.obj N)) :
    IsZero N := by
  apply (DerivedCategory.isZero_iff N).mpr
  intro n
  apply module_zero_of_cover _ U S hS
  intro V a ha
  let e := ((SheafOfModules.overMap.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) a).mapDerivedCategoryHomologyFunctorIso
      n).app N
  exact ((DerivedCategory.homologyFunctor _ n).map_isZero (hN V a ha)).of_iso e

private noncomputable def completeElementHom
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (U : C) (f : R.obj.obj (op U)) :
    DerivedCategory (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) :=
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U))) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)))
  (derivedInternalHom (J.over U) (R.over U)).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSiteSectionLocalization
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U f)),
    ringedSiteDerivedRestriction ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U K)

private theorem completeElementHom_comparison
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (U V : C) (a : V ⟶ U) (f : R.obj.obj (op U)) :
    Nonempty ((SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) a).mapDerivedCategory.obj
        (completeElementHom J R K U f) ≅
      completeElementHom J R K V (R.obj.map a.op f)) := by
  let O := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let A := ringedSiteModules.{u} O
  let F := SheafOfModules.overMap.{u} O a
  let FU := SheafOfModules.overFunctor.{u} O U
  let FV := SheafOfModules.overFunctor.{u} O V
  let : ∀ W : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over W) (forget₂ CommRingCat RingCat)).obj (R.over W))) :=
    fun W ↦ inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (O.over W)))
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  have eK (W : C) :
      (SheafOfModules.overFunctor.{u} O W).mapDerivedCategory.obj K ≅
        ringedSiteDerivedRestriction O W K :=
    (SheafOfModules.overFunctor.{u} O W).mapDerivedCategory.mapIso
      (Q.objObjPreimageIso K).symm ≪≫
        (SheafOfModules.overFunctor.{u} O W).mapDerivedCategoryFactors.app
          (Q.objPreimage K)
  let eN : F.mapDerivedCategory.obj (ringedSiteDerivedRestriction O U K) ≅
      ringedSiteDerivedRestriction O V K := by
    let e₁ : F.mapDerivedCategory.obj (ringedSiteDerivedRestriction O U K) ≅
        F.mapDerivedCategory.obj (FU.mapDerivedCategory.obj K) :=
      F.mapDerivedCategory.mapIso (eK U).symm
    let e₂ : F.mapDerivedCategory.obj (FU.mapDerivedCategory.obj K) ≅
        (FU ⋙ F).mapDerivedCategory.obj K :=
      (Functor.mapDerivedCategoryCompIso FU F).app K
    let e₃ : (FU ⋙ F).mapDerivedCategory.obj K ≅ FV.mapDerivedCategory.obj K :=
      (Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u} O a)).app K
    exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ eK V
  let LU := (DerivedCategory.singleFunctor _ 0).obj (ringedSiteSectionLocalization O U f)
  let LV := (DerivedCategory.singleFunctor _ 0).obj
    (ringedSiteSectionLocalization O V (R.obj.map a.op f))
  let eL : F.mapDerivedCategory.obj LU ≅ LV :=
    (F.mapDerivedCategorySingleFunctor 0).app (ringedSiteSectionLocalization O U f) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (localization_overMap_iso O a f)
  obtain ⟨_, s, _⟩ := ringedInternalHom_restriction J R
  let e := (s U V a).app (op LU, ringedSiteDerivedRestriction O U K) ≪≫
    (derivedInternalHom (J.over V) (R.over V)).mapIso (eL.op.symm.prod eN)
  exact ⟨e⟩

/-- The vanishing-localization criterion is preserved by restrictions and descends
through every covering sieve.

Source: Stacks Project, algebraization.tex, Tags 0997 and 0998;
sites-cohomology.tex, Tag 08JB.
(auxiliary; not a blueprint node).

Proof: Exact slice restriction preserves the defining sequential colimit: its
unit module and multiplication maps restrict to the unit and restricted section.
The derived internal-Hom restriction comparison, the comparison with degree-zero
objects, and composition of derived restriction identify restricted RHom with the
RHom for the restricted section. Additive restriction preserves a zero object.
Conversely, the comparison makes RHom vanish after each arrow of a covering
sieve. Restriction commutes with cohomology. A section of each cohomology sheaf
over W vanishes after every arrow of the pulled-back covering sieve, since the
corresponding restricted sheaf is zero. The sheaf uniqueness axiom makes this
section zero. All cohomology sheaves thus vanish, so the derived object is zero.
This includes identity arrows, the zero ring, and empty covering sieves. -/
theorem ringedSite_completeElements_locality
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    : (∀ (U V : C) (a : V ⟶ U) (f : R.obj.obj (op U)),
        IsRingedSiteCompleteElement J R K U f →
          IsRingedSiteCompleteElement J R K V (R.obj.map a.op f)) ∧
      (∀ (U : C) (S : Sieve U), S ∈ J U → ∀ f : R.obj.obj (op U),
        (∀ (V : C) (a : V ⟶ U), S a →
          IsRingedSiteCompleteElement J R K V (R.obj.map a.op f)) →
        IsRingedSiteCompleteElement J R K U f) := by
  constructor
  · intro U V a f hf
    obtain ⟨e⟩ := completeElementHom_comparison J R K U V a f
    have hz := (SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) a).mapDerivedCategory.map_isZero hf
    exact hz.of_iso e.symm
  · intro U S hS f hf
    change IsZero (completeElementHom J R K U f)
    apply derived_zero_of_cover J R U S hS
    intro V a ha
    obtain ⟨e⟩ := completeElementHom_comparison J R K U V a f
    exact (hf V a ha).of_iso e

end CategoryTheory
