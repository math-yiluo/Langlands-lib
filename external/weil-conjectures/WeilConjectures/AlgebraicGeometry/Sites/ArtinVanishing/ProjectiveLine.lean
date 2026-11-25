/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
public import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf

/-!
# Higher direct images on the projective line

Let `B` be a scheme, `j : 𝔸¹_B ⟶ ℙ¹_B` the affine chart, `i : B ⟶ ℙ¹_B` the section at infinity
and `g : ℙ¹_B ⟶ B` the projection. We record the facts about these maps used in the proof of
the affine Artin vanishing theorem:

* `i` is a closed immersion, with image the complement of the affine chart;
* for `q > 0` the higher direct image `Rᵠj_* M` vanishes on `𝔸¹_B`, hence is `i_* i^*` of itself;
* `Rᵖg_* (i_* N) = 0` for `p > 0`, since `g ∘ i = 𝟙` and `i_*` is exact;
* for a torsion sheaf `G` on `ℙ¹_B`, the geometric stalks of `Rᵖg_* G` vanish for `p > 2`: by
  proper base change they are the cohomology groups of the projective line over a separably
  closed field, a curve.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasInjectiveResolutions C]

/-- The higher right derived functors of an exact functor vanish. -/
lemma isZero_rightDerived_succ_obj_of_exact (H : C ⥤ D) [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] (X : C) (n : ℕ) :
    IsZero ((H.rightDerived (n + 1)).obj X) := by
  have hX : (((𝟭 C).mapHomologicalComplex _).obj (injectiveResolution X).cocomplex).ExactAt
      (n + 1) := (injectiveResolution X).cocomplex_exactAt_succ n
  have h : IsZero (((𝟭 C).rightDerived (n + 1)).obj X) :=
    hX.isZero_homology.of_iso ((injectiveResolution X).isoRightDerivedObj (𝟭 C) (n + 1))
  exact (H.map_isZero h).of_iso (rightDerivedCompObjIsoOfExact (𝟭 C) H X (n + 1))

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProjectiveLine

open Etale

variable (B : Scheme.{u})

/-- The section at infinity of `ℙ¹_B ⟶ B` is a closed immersion. -/
instance isClosedImmersion_infinity : IsClosedImmersion (infinity B) := by
  have : IsClosedImmersion (infinity B ≫ ProjectiveLine B ↘ B) := by
    rw [infinity_over]
    infer_instance
  exact .of_comp _ (ProjectiveLine B ↘ B)

/-- A sheaf on `ℙ¹_B` which vanishes on the affine chart is supported at infinity: the unit
`G ⟶ i_* i^* G` is an isomorphism. -/
lemma isIso_unit_app_infinity_of_isZero
    (G : Sheaf (ProjectiveLine B).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsZero ((affineChart B)^*[AddCommGrpCat.{u + 1}].obj G)) :
    IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (infinity B)).unit.app G) := by
  have hS := Etale.shortExact_openClosedShortComplex AddCommGrpCat.{u + 1} (affineChart B)
    (infinity B) G (by simpa using range_infinity B)
  have : ((affineChart B)_!open[AddCommGrpCat.{u + 1}]).IsLeftAdjoint :=
    (Etale.openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
      (affineChart B)).isLeftAdjoint
  exact hS.isIso_g_iff.2 (Functor.map_isZero ((affineChart B)_!open[AddCommGrpCat.{u + 1}]) hG)

/-- For `q > 0`, the higher direct image `Rᵠj_* M` along the affine chart `j : 𝔸¹_B ⟶ ℙ¹_B`
is supported at infinity: the unit `Rᵠj_* M ⟶ i_* i^* Rᵠj_* M` is an isomorphism. -/
theorem isIso_unit_app_rightDerived_lowerStar_affineChart
    (M : Sheaf 𝔸(PUnit.{u + 1}; B).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hq : 0 < q) :
    IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (infinity B)).unit.app
      ((((affineChart B)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj M)) := by
  apply isIso_unit_app_infinity_of_isZero
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have : PreservesFiniteColimits (affineChart B)^*[AddCommGrpCat.{u + 1}] :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  have : IsIso (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (affineChart B)).counit :=
    NatIso.isIso_of_isIso_app _
  refine IsZero.of_iso ?_ (Functor.rightDerivedCompObjIsoOfExact
    (affineChart B)_*[AddCommGrpCat.{u + 1}] (affineChart B)^*[AddCommGrpCat.{u + 1}] M
      (q + 1)).symm
  refine IsZero.of_iso ?_ ((NatIso.rightDerived
    (asIso (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (affineChart B)).counit)
      (q + 1)).app M)
  exact (𝟭 _).isZero_rightDerived_succ_obj_of_exact M q

/-- `Rᵖg_* (i_* N) = 0` for `p > 0`, where `g : ℙ¹_B ⟶ B` is the projection and `i` the section
at infinity. -/
theorem isZero_rightDerived_lowerStar_obj_lowerStar_infinity
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) (hp : 0 < p) :
    IsZero ((((ProjectiveLine B ↘ B)_*[AddCommGrpCat.{u + 1}]).rightDerived p).obj
      (((infinity B)_*[AddCommGrpCat.{u + 1}]).obj N)) := by
  obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  refine IsZero.of_iso ?_ ((Functor.rightDerivedCompIsoOfExact
    ((infinity B)_*[AddCommGrpCat.{u + 1}]) ((ProjectiveLine B ↘ B)_*[AddCommGrpCat.{u + 1}])
      (p + 1)).app N).symm
  refine IsZero.of_iso ?_ ((NatIso.rightDerived
    (Etale.lowerStarComp AddCommGrpCat.{u + 1} (infinity B) (ProjectiveLine B ↘ B) (𝟙 B)
      (by simp) ≪≫ Etale.lowerStarId AddCommGrpCat.{u + 1} B) (p + 1)).app N)
  exact (𝟭 _).isZero_rightDerived_succ_obj_of_exact N p

/-- Being torsion is invariant under isomorphisms of abelian sheaves. -/
private lemma isTorsion_of_iso {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {F G : Sheaf J AddCommGrpCat.{u + 1}} (e : F ≅ G)
    (hF : F.IsTorsion) : G.IsTorsion := by
  intro U s
  obtain ⟨S, hS, h⟩ := hF (e.inv.hom.app U s)
  refine ⟨S, hS, fun V g hg ↦ ?_⟩
  have h₁ := AddMonoidHom.isOfFinAddOrder (e.hom.hom.app (op V)).hom (h hg)
  have h₂ := ConcreteCategory.congr_hom (e.hom.hom.naturality g.op) (e.inv.hom.app U s)
  have h₃ : e.hom.hom.app U (e.inv.hom.app U s) = s :=
    ConcreteCategory.congr_hom (congr_app (congrArg (fun a ↦ a.hom) e.inv_hom_id) U) s
  simp only [ConcreteCategory.comp_apply, h₃] at h₂
  rw [← h₂]
  exact h₁

/-- **Proper base change for `ℙ¹`**, for a torsion abelian sheaf placed in degree `0`. -/
lemma isIso_derivedBaseChangeMapPlus_singleFunctor_obj {B' : Scheme.{u}} (s : B' ⟶ B)
    (G : Sheaf (ProjectiveLine B).smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion) :
    IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) s).toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) := by
  let Φ := sheafCompose (ProjectiveLine B).smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let E := Φ.asEquivalence
  let G' := E.inverse.obj G
  let eG : Φ.obj G' ≅ G := E.counitIso.app G
  have : Scheme.IsTorsionModuleSheaf G' :=
    (Scheme.isTorsionModuleSheaf_iff_isTorsion G').2 (isTorsion_of_iso eG.symm hG)
  let e : Φ.mapDerivedCategoryPlus.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G') ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj G :=
    (Φ.mapDerivedCategoryPlusSingleFunctor 0).app G' ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso eG
  rw [← NatTrans.isIso_app_iff_of_iso _ e, isIso_derivedBaseChangeMapPlus_app_forget₂_iff]
  exact Etale.hasTorsionBaseChange_projectiveLine _ B
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) s) _
    (Etale.DerivedCategory.Plus.moduleTorsionHomology_singleFunctor_obj _ _ G')

section SepClosed

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Over a separably closed field `Ω`, an abelian étale sheaf on `Spec Ω` without nonzero
global sections is zero. -/
private lemma isZero_of_subsingleton_sections
    (F : Sheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : Subsingleton (F.obj.obj (op (⊤_ (Spec (.of Ω)).Etale)))) : IsZero F := by
  have hU : ∀ U, Subsingleton (F.obj.obj (op U)) := fun U ↦ ⟨fun x y ↦
    Scheme.eq_of_forall_restrict_eq_of_isSepClosed F fun V hV f ↦ by
      have : Subsingleton (F.obj.obj (op V)) :=
        (F.obj.mapIso (Scheme.etaleIsoOfIsIso V hV ≪≫
          (terminalIsoIsTerminal (Scheme.isTerminalEtalePoint (k := Ω))).symm).op
          ).addCommGroupIsoToAddEquiv.toEquiv.symm.subsingleton
      exact Subsingleton.elim _ _⟩
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact Subsingleton.elim _ _

/-- Over a separably closed field `Ω`, taking global sections of abelian étale sheaves on
`Spec Ω` is exact. -/
private lemma preservesFiniteColimits_sectionsFunctorAt_terminal :
    PreservesFiniteColimits (Sheaf.sectionsFunctorAt (Spec (.of Ω)).smallEtaleTopology
      (⊤_ (Spec (.of Ω)).Etale) : Sheaf _ AddCommGrpCat.{u + 1} ⥤ _) := by
  let Γ : Sheaf _ AddCommGrpCat.{u + 1} ⥤ _ :=
    Sheaf.sectionsFunctorAt (Spec (.of Ω)).smallEtaleTopology (Scheme.etalePoint Ω)
  have : Γ.PreservesEpimorphisms := inferInstanceAs
    ((sheafSections _ AddCommGrpCat.{u + 1}).obj (op (Scheme.etalePoint Ω))).PreservesEpimorphisms
  have : Γ.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels _
  have : PreservesFiniteColimits Γ := Functor.preservesFiniteColimits_of_preservesHomology _
  exact preservesFiniteColimits_of_natIso (F := Γ) (Functor.isoWhiskerLeft (sheafToPresheaf _ _)
    ((evaluation _ _).mapIso (terminalIsoIsTerminal (Scheme.isTerminalEtalePoint (k := Ω))).op))

/-- For a torsion sheaf `H` on `ℙ¹_Ω`, `Ω` separably closed, `Rᵖg_* H = 0` for `p > 2`, where
`g : ℙ¹_Ω ⟶ Spec Ω` is the projection: its global sections are `Hᵖ(ℙ¹_Ω, H)`, which vanishes
since `ℙ¹_Ω` is a curve. -/
lemma isZero_rightDerived_lowerStar_of_isSepClosed
    (H : Sheaf (ProjectiveLine (Spec (.of Ω))).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H.IsTorsion) (p : ℕ) (hp : 2 < p) :
    IsZero ((((ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω))_*[AddCommGrpCat.{u + 1}]).rightDerived
      p).obj H) := by
  let g := ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)
  let Γ : Sheaf _ AddCommGrpCat.{u + 1} ⥤ _ :=
    Sheaf.sectionsFunctorAt (Spec (.of Ω)).smallEtaleTopology (⊤_ (Spec (.of Ω)).Etale)
  have : PreservesFiniteColimits Γ := preservesFiniteColimits_sectionsFunctorAt_terminal
  have : ((sheafSections (Spec (.of Ω)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (op (⊤_ (Spec (.of Ω)).Etale))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙ (evaluation _ AddCommGrpCat.{u + 1}).obj _).Additive
  have : ((sheafSections (ProjectiveLine (Spec (.of Ω))).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (op (⊤_ (ProjectiveLine (Spec (.of Ω))).Etale))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙ (evaluation _ AddCommGrpCat.{u + 1}).obj _).Additive
  have hcoh := (IsCurve.hasTorsionCohomologicalDimensionLE_of_isSepClosed g).1 H hH p hp
  rw [subsingleton_H_iff_isZero_rightDerived_Γ] at hcoh
  refine isZero_of_subsingleton_sections _ ?_
  rw [← AddCommGrpCat.isZero_iff_subsingleton]
  exact IsZero.of_iso hcoh ((Functor.rightDerivedCompObjIsoOfExact (g)_*[AddCommGrpCat.{u + 1}]
    Γ H p).symm ≪≫ (NatIso.rightDerived
      (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g) p).app H)

end SepClosed

/-- For a torsion sheaf `G` on `ℙ¹_B`, the geometric stalks of `Rᵖg_* G` vanish for `p > 2`. -/
theorem isZero_upperStar_rightDerived_lowerStar_of_two_lt
    (G : Sheaf (ProjectiveLine B).smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B) (p : ℕ) (hp : 2 < p) :
    IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj
      ((((ProjectiveLine B ↘ B)_*[AddCommGrpCat.{u + 1}]).rightDerived p).obj G)) := by
  let sq := ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) s
  let s' := ProjectiveSpace.map (ULift.{u} (Fin 2)) s
  let F := (ProjectiveLine B ↘ B)_*[AddCommGrpCat.{u + 1}]
  let F' := (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω))_*[AddCommGrpCat.{u + 1}]
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  have := isIso_derivedBaseChangeMapPlus_singleFunctor_obj B s G hG
  have hvan := isZero_rightDerived_lowerStar_of_isSepClosed
    ((s')^*[AddCommGrpCat.{u + 1}].obj G) (Etale.isTorsion_upperStar s' hG) p hp
  exact IsZero.of_iso hvan
    ((s)^*[AddCommGrpCat.{u + 1}].mapIso
        (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso G p).symm ≪≫
      (((s)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso p).app
        (F.rightDerivedFunctorPlus.obj K) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ p).mapIso
        (asIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K)) ≪≫
      (DerivedCategory.Plus.homologyFunctor _ p).mapIso
        (F'.rightDerivedFunctorPlus.mapIso
          ((((s')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).app G)) ≪≫
      F'.homologyRightDerivedFunctorPlusObjSingleFunctorIso _ p)

end AlgebraicGeometry.ProjectiveLine
