/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientComparisons
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedFiniteModelProofAPISupplement
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Exact condensed coefficient changes and their derived tensor calculus

Source: archived master ModuleObject/Colimit/Compatibility.lean, A0.2 and Flat;
ModuleObject/Colimit/TwoColimit.lean, ExtendScalars
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).

All modules below are the master internal module objects. The constructible categories
are `PadicSubfieldConstructible` and `PadicAlgClConstructible`, with no completeness
condition. The adjunctions are on the ambient unbounded derived categories.
-/

@[expose] public section

universe u wC wD wE vC vD vE uC uD uE

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

-- Keep canonical resolution comparisons opaque to implicit instance matching.
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.extendScalars

section FiniteBasisConstruction

universe v₁ v₂ u₁ u₂
open CategoryTheory.MonObj CategoryTheory.BraidedCategory
open scoped CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false

/- The following finite free comparisons use only additive monoidal functors, so they apply
both to sheafification and to inverse image from the point. -/
namespace CategoryTheory.Mod

section Map
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  [Abelian D] [MonoidalPreadditive D]
  (F : C ⥤ D) [F.LaxMonoidal] [F.Additive]
  {R S : C} [MonObj R] [MonObj S]
  (a : R ⟶ S) [IsMonHom a]
private theorem additive_mapMod : (F.mapMod R).Additive where
  map_add := hom_ext _ _ F.map_add

private noncomputable def mapRegularIso :
    (F.mapMod R).obj (regular R) ≅ regular (F.obj R) :=
  isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp])
private noncomputable def mapFiniteFreeIso (n : ℕ) :
    (F.mapMod R).obj (finiteFree R n) ≅ finiteFree (F.obj R) n := by
  have : (F.mapMod R).Additive := additive_mapMod F
  exact (F.mapMod R).mapBiproduct (fun _ : Fin n ↦ regular R) ≪≫
    biproduct.mapIso (fun _ ↦ mapRegularIso F)
private noncomputable def mapRestrictedRegularIso :
    (F.mapMod R).obj ((comap a).obj (regular S)) ≅
      (comap (F.map a)).obj (regular (F.obj S)) :=
  (F.mapModComapIso a).app (regular S) ≪≫
    (comap (F.map a)).mapIso (mapRegularIso F)
private noncomputable def mapFreeRestrictedRegularIso (n : ℕ)
    (e : (comap a).obj (regular S) ≅ finiteFree R n) :
    (comap (F.map a)).obj (regular (F.obj S)) ≅ finiteFree (F.obj R) n :=
  (mapRestrictedRegularIso F a).symm ≪≫ (F.mapMod R).mapIso e ≪≫ mapFiniteFreeIso F n
end Map
section RingIso
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C] [MonoidalClosed C]
  {R S : C} [MonObj R] [MonObj S]
private noncomputable def regularRingIso (r : R ≅ S) [IsMonHom r.hom] :
    (comap r.inv).obj (regular R) ≅ regular S :=
  isoMk r (by
    change (r.inv ▷ R ≫ μ[R]) ≫ r.hom = S ◁ r.hom ≫ μ[S]
    rw [Category.assoc, IsMonHom.mul_hom]
    rw [MonoidalCategory.tensorHom_def]
    rw [Category.assoc, ← comp_whiskerRight_assoc, r.inv_hom_id,
      id_whiskerRight, Category.id_comp])
private noncomputable def comapFreeIso (e : R ≅ S) [IsMonHom e.hom] (n : ℕ) :
    (comap e.inv).obj (finiteFree R n) ≅ finiteFree S n := by
  let : PreservesBiproduct (fun _ : Fin n ↦ regular R) (comap e.inv) :=
    preservesBiproduct_of_preservesProduct _
  let er := regularRingIso e
  exact (comap e.inv).mapBiproduct (fun _ : Fin n ↦ regular R) ≪≫
    biproduct.mapIso (fun _ ↦ er)

variable {R' S' : C} [MonObj R'] [MonObj S']
private noncomputable def restrictedRegularIsoOfRingIso
    (a : R ⟶ S) [IsMonHom a] (a' : R' ⟶ S') [IsMonHom a']
    (r : R ≅ R') (s : S ≅ S') [IsMonHom r.hom] [IsMonHom s.hom]
    (h : a' ≫ s.inv = r.inv ≫ a) :
    (comap a').obj (regular S') ≅
      (comap r.inv).obj ((comap a).obj (regular S)) := by
  let es := regularRingIso s
  exact (comap a').mapIso es.symm ≪≫
    ((comapComp a' s.inv).symm ≪≫ comapCongr h ≪≫ comapComp r.inv a).app _
private noncomputable def freeRestrictedRegularIsoOfRingIso
    (a : R ⟶ S) [IsMonHom a] (a' : R' ⟶ S') [IsMonHom a']
    (r : R ≅ R') (s : S ≅ S') [IsMonHom r.hom] [IsMonHom s.hom]
    (h : a' ≫ s.inv = r.inv ≫ a)
    (n : ℕ) (e : (comap a).obj (regular S) ≅ finiteFree R n) :
    (comap a').obj (regular S') ≅ finiteFree R' n :=
  restrictedRegularIsoOfRingIso a a' r s h ≪≫
    (comap r.inv).mapIso e ≪≫ comapFreeIso r n
end RingIso
end CategoryTheory.Mod

/- Work sectionwise before sheafification: a continuous field-linear map gives an internal
module morphism, and the coordinate maps of a finite basis give inverse biproduct maps. -/
namespace Profinite

private noncomputable def continuousAddHomPresheaf
    {S T : Type} [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    [Ring T] [TopologicalSpace T] [IsTopologicalRing T]
    (l : S →+ T) (hl : Continuous l) :
    continuousMapRingPresheaf.{u} S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1} ⟶
      continuousMapRingPresheaf T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1} where
  app U := AddCommGrpCat.ofHom
    { toFun f := ULift.up ⟨fun x ↦ l (f.down x), hl.comp f.down.continuous⟩
      map_zero' := by
        change ULift.up _ = ULift.up _
        congr 1
        ext x
        exact map_zero l
      map_add' f g := by
        change ULift.up _ = ULift.up _
        congr 1
        ext x
        exact map_add l _ _ }
  naturality _ _ _ := rfl

private noncomputable def continuousLinearPresheafHom
    {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (l : S →ₗ[R] R) (hl : Continuous l) :
    (Mod.comap (Functor.whiskerRight (continuousMapRingPresheafMap
      (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
      (Mod.regular (continuousMapRingPresheaf.{u} S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) ⟶
    Mod.regular (continuousMapRingPresheaf R ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
  Mod.homMk (continuousAddHomPresheaf l.toAddMonoidHom hl) (by
    ext U : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r s
    change ULift.up (⟨fun x ↦ l ((algebraMap R S (r.down x)) * s.down x), _⟩ :
      C(U.unop, R)) = ULift.up _
    congr 1
    ext x
    change l ((algebraMap R S (r.down x)) * s.down x) = r.down x * l (s.down x)
    simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
      l.map_smul (r.down x) (s.down x))

private noncomputable def continuousLinearPresheafHomFrom
    {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (l : R →ₗ[R] S) (hl : Continuous l) :
    Mod.regular (continuousMapRingPresheaf.{u} R ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) ⟶
    (Mod.comap (Functor.whiskerRight (continuousMapRingPresheafMap
      (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
      (Mod.regular (continuousMapRingPresheaf S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) :=
  Mod.homMk (continuousAddHomPresheaf l.toAddMonoidHom hl) (by
    ext U : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r s
    change ULift.up _ = ULift.up _
    congr 1
    ext x
    change l (r.down x * s.down x) = algebraMap R S (r.down x) * l (s.down x)
    simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
      l.map_smul (r.down x) (s.down x))

private noncomputable def continuousBasisIso
    {R S : Type} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
    [Field S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (n : ℕ) (b : Module.Basis (Fin n) R S)
    (hc : ∀ i, Continuous (b.coord i)) :
    (Mod.comap (Functor.whiskerRight (continuousMapRingPresheafMap
      (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1}))).obj
      (Mod.regular (continuousMapRingPresheaf.{u} S ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) ≅
    Mod.finiteFree (continuousMapRingPresheaf R ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) n := by
  let p (i : Fin n) := continuousLinearPresheafHom ha (b.coord i) (hc i)
  let q (i : Fin n) := continuousLinearPresheafHomFrom ha
    (LinearMap.toSpanSingleton R S (b i))
    (by
      change Continuous (fun r : R ↦ r • b i)
      simp_rw [Algebra.smul_def]
      exact ha.mul_const (b i))
  refine
    { hom := biproduct.lift p
      inv := biproduct.desc q
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [biproduct.lift_desc]
    apply Mod.hom_ext
    change (Mod.forget _).map (∑ i, p i ≫ q i) = _
    rw [Functor.map_sum]
    apply NatTrans.ext
    funext U
    simp only [NatTrans.app_sum]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    let ev : (AddCommGrpCat.of (ULift.{u + 1} C(U.unop, S)) ⟶
        AddCommGrpCat.of (ULift.{u + 1} C(U.unop, S))) →+ S :=
      { toFun g := (g.hom f).down x
        map_zero' := rfl
        map_add' _ _ := rfl }
    change ev (∑ i, _) = f.down x
    rw [map_sum]
    change (∑ i, (b.coord i (f.down x)) • b i) = f.down x
    exact b.sum_repr (f.down x)
  · apply biproduct.hom_ext
    intro i
    apply biproduct.hom_ext'
    intro j
    simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      Category.id_comp]
    apply Mod.hom_ext
    by_cases hij : j = i
    · subst j
      rw [biproduct.ι_π_self]
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      change ULift.up _ = f
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      change b.coord i ((f.down x) • b i) = f.down x
      simp
    · rw [biproduct.ι_π_ne _ hij]
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      change ULift.up _ = (0 : ULift.{u + 1} C(U.unop, R))
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      change b.coord i ((f.down x) • b j) = 0
      simp [hij]

private noncomputable def continuousBasisSheafIso
    {R S : Type} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
    [Field S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]
    (ha : Continuous (algebraMap R S)) (n : ℕ) (b : Module.Basis (Fin n) R S)
    (hc : ∀ i, Continuous (b.coord i)) :
    (Mod.comap ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (continuousMapRingSheafMap (algebraMap R S) ha))).obj
      (Mod.regular (continuousMapRingObj S)) ≅ Mod.finiteFree (continuousMapRingObj R) n := by
  let a := Functor.whiskerRight (continuousMapRingPresheafMap
    (algebraMap R S) ha) (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let sh := presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  exact Mod.freeRestrictedRegularIsoOfRingIso (sh.map a) _
    (Sheaf.sheafifyRingPresheafIso _ (continuousMapRingSheaf R))
    (Sheaf.sheafifyRingPresheafIso _ (continuousMapRingSheaf S))
    (by rw [Sheaf.sheafCompose_map_eq]; simp [sh, a, continuousMapRingSheafMap_hom]) n
    (Mod.mapFreeRestrictedRegularIso sh a n (continuousBasisIso ha n b hc))

end Profinite

end FiniteBasisConstruction

section ModuleCacheScope

-- Package the canonical module structures once, before substituting coefficient rings.
namespace CategoryTheory
section ModuleStructures
variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{vC} C] [Abelian.HasFunctorialFlatResolution C]

@[instance_reducible]
private noncomputable def scalarAbelian (R : C) [MonObj R] [IsCommMonObj R] :
  Abelian (Mod C R) := inferInstance

@[instance_reducible]
private noncomputable def scalarMonoidal (R : C) [MonObj R] [IsCommMonObj R] :
  MonoidalCategory (Mod C R) := inferInstance

omit [Abelian.HasFunctorialFlatResolution C] in
@[instance_reducible]
private noncomputable def scalarHasDerived (R : C) [MonObj R] [IsCommMonObj R] :
    HasDerivedCategory.{vC} (Mod C R) := inferInstance

omit [Abelian.HasFunctorialFlatResolution C] in
private theorem scalarMonoidalAdditive (R : C) [MonObj R] [IsCommMonObj R] :
  MonoidalPreadditive (Mod C R) := inferInstance

omit [Abelian.HasFunctorialFlatResolution C] in
private theorem scalarGrothendieck (R : C) [MonObj R] [IsCommMonObj R] :
  IsGrothendieckAbelian.{vC} (Mod C R) := inferInstance

omit [Abelian.HasFunctorialFlatResolution C] in
private theorem scalarCountable (R : C) [MonObj R] [IsCommMonObj R] :
  HasCountableCoproducts (Mod C R) := inferInstance

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private theorem scalarIntColimits (R : C) [MonObj R] [IsCommMonObj R] :
  HasColimitsOfShape ℤ (Mod C R) := inferInstance

omit [Abelian.HasFunctorialFlatResolution C] in
private theorem scalarExactIntColimits (R : C) [MonObj R] [IsCommMonObj R] :
  HasExactColimitsOfShape ℤ (Mod C R) := inferInstance

omit [MonoidalPreadditive C] in
private theorem scalarFlatResolution (R : C) [MonObj R] [IsCommMonObj R] :
  Abelian.HasFunctorialFlatResolution (Mod C R) := inferInstance

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private theorem scalarTensor4 (R : C) [MonObj R] [IsCommMonObj R]
    (X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod C R)) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private theorem scalarTensor12 (R : C) [MonObj R] [IsCommMonObj R]
    (X₁ X₂ X₃ : GradedObject ℤ (Mod C R)) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private theorem scalarTensor23 (R : C) [MonObj R] [IsCommMonObj R]
    (X₁ X₂ X₃ : GradedObject ℤ (Mod C R)) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private theorem scalarTensorColimits (R : C) [MonObj R] [IsCommMonObj R]
    (X : Mod C R) :
    PreservesColimitsOfShape ℤ ((curriedTensor (Mod C R)).obj X) := inferInstance

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private theorem scalarFlipTensorColimits (R : C) [MonObj R] [IsCommMonObj R]
    (X : Mod C R) :
    PreservesColimitsOfShape ℤ ((curriedTensor (Mod C R)).flip.obj X) := inferInstance

end ModuleStructures
end CategoryTheory

attribute [local instance 2000] CategoryTheory.scalarAbelian
attribute [local instance 2000] CategoryTheory.scalarMonoidal
attribute [local instance 2000] CategoryTheory.scalarMonoidalAdditive
attribute [local instance 2000] CategoryTheory.scalarGrothendieck
attribute [local instance 2000] CategoryTheory.scalarCountable
attribute [local instance 2000] CategoryTheory.scalarIntColimits
attribute [local instance 2000] CategoryTheory.scalarExactIntColimits
attribute [local instance 2000] CategoryTheory.scalarFlatResolution
attribute [local instance 2000] CategoryTheory.scalarTensor4
attribute [local instance 2000] CategoryTheory.scalarTensor12
attribute [local instance 2000] CategoryTheory.scalarTensor23
attribute [local instance 2000] CategoryTheory.scalarTensorColimits
attribute [local instance 2000] CategoryTheory.scalarFlipTensorColimits

section CoherenceTools

set_option maxRecDepth 2048

namespace CategoryTheory
section
variable {C D : Type*} [Category C] [Category D]
  {F F' : C ⥤ D} {G G' : D ⥤ C}
private lemma uniq_eq_conjugate (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    a.leftAdjointUniq (b.ofNatIsoRight e) =
      (conjugateIsoEquiv b a).symm e := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]
end
end CategoryTheory

namespace CategoryTheory
section Scalar
variable {C : Type*} [Category C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S U : C} [MonObj R] [MonObj S] [MonObj U]
  [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ U) [IsMonHom ψ]
  (χ : R ⟶ U) [IsMonHom χ] (h : φ ≫ ψ = χ)
private noncomputable abbrev scalarComp :=
  (Mod.extendScalarsComp φ ψ).symm ≪≫ Mod.extendScalarsIsoOfEq h

private lemma scalarComp_eq :
    (Mod.extendScalarsComp φ ψ).symm ≪≫ Mod.extendScalarsIsoOfEq h =
      Adjunction.leftAdjointCompIso (Mod.extendRestrictAdjunction φ)
        (Mod.extendRestrictAdjunction ψ) (Mod.extendRestrictAdjunction χ)
        ((Mod.comapComp φ ψ).symm ≪≫ Mod.comapCongr h) := by
  rw [Mod.extendScalarsComp, Mod.extendScalarsIsoOfEq, uniq_eq_conjugate,
    uniq_eq_conjugate]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    conjugateIsoEquiv_symm_apply_hom, conjugateIsoEquiv_symm_apply_inv,
    Adjunction.leftAdjointCompIso, Iso.trans_inv]
  exact congr_app (conjugateEquiv_symm_comp
    (Mod.extendRestrictAdjunction χ) (Mod.extendRestrictAdjunction (φ ≫ ψ))
    ((Mod.extendRestrictAdjunction φ).comp (Mod.extendRestrictAdjunction ψ))
    (Mod.comapCongr h).inv (Mod.comapComp φ ψ).hom) X
end Scalar
end CategoryTheory

namespace CategoryTheory
section ScalarCoherence
variable {C : Type*} [Category C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S U V : C} [MonObj R] [MonObj S] [MonObj U] [MonObj V]
  [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj U]
  (f : R ⟶ S) [IsMonHom f] (g : S ⟶ U) [IsMonHom g] (j : U ⟶ V) [IsMonHom j]
  (fg : R ⟶ U) [IsMonHom fg] (gj : S ⟶ V) [IsMonHom gj]
  (fgj : R ⟶ V) [IsMonHom fgj]
  (hfg : f ≫ g = fg) (hgj : g ≫ j = gj) (hfgj : f ≫ gj = fgj) (hfgj' : fg ≫ j = fgj)
private lemma scalarComp_assoc :
    Functor.isoWhiskerRight (scalarComp f g fg hfg) (Mod.extendScalars j) ≪≫
        scalarComp fg j fgj hfgj' =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (Mod.extendScalars f) (scalarComp g j gj hgj) ≪≫
          scalarComp f gj fgj hfgj := by
  simp only [scalarComp, scalarComp_eq]
  have he : Functor.isoWhiskerLeft (Mod.comap j)
      ((Mod.comapComp f g).symm ≪≫ Mod.comapCongr hfg) ≪≫
        ((Mod.comapComp fg j).symm ≪≫ Mod.comapCongr hfgj') =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ((Mod.comapComp g j).symm ≪≫ Mod.comapCongr hgj)
          (Mod.comap f) ≪≫
        ((Mod.comapComp f gj).symm ≪≫ Mod.comapCongr hfgj) := by
    ext M
    simp only [Functor.comp_obj, Functor.isoWhiskerLeft_trans, Iso.trans_assoc, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Mod.comp_hom', Mod.comapComp_inv_app_hom, Mod.comapCongr_hom_app_hom,
      Functor.isoWhiskerRight_trans, Functor.isoWhiskerRight_hom,
      Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp, Mod.comap_map_hom]
    change (𝟙 M.X ≫ 𝟙 M.X ≫ 𝟙 M.X ≫ 𝟙 M.X) =
      (𝟙 M.X ≫ 𝟙 M.X ≫ 𝟙 M.X ≫ 𝟙 M.X)
    simp
  rw [Adjunction.leftAdjointCompIso_assoc
    (Mod.extendRestrictAdjunction f) (Mod.extendRestrictAdjunction g)
    (Mod.extendRestrictAdjunction j) (Mod.extendRestrictAdjunction fg)
    (Mod.extendRestrictAdjunction gj) (Mod.extendRestrictAdjunction fgj) _ _ _ _ he]
  simp
end ScalarCoherence
end CategoryTheory

namespace CategoryTheory
section ScalarUnit
variable {C : Type*} [Category C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
private noncomputable abbrev scalarUnit (a : R ⟶ R) [IsMonHom a] (ha : a = 𝟙 R) :=
  Mod.extendScalarsIsoOfEq ha ≪≫ Mod.extendScalarsId

private lemma scalarUnit_eq (a : R ⟶ R) [IsMonHom a] (ha : a = 𝟙 R) :
    scalarUnit a ha = Adjunction.leftAdjointIdIso (Mod.extendRestrictAdjunction a)
      (Mod.comapCongr ha ≪≫ Mod.comapId R) := by
  unfold scalarUnit Mod.extendScalarsIsoOfEq Mod.extendScalarsId
  rw [uniq_eq_conjugate, uniq_eq_conjugate]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [Iso.trans_hom, NatTrans.comp_app, conjugateIsoEquiv_symm_apply_hom,
    Adjunction.leftAdjointIdIso, Iso.symm_hom, Iso.trans_inv]
  exact congr_app (conjugateEquiv_symm_comp Adjunction.id
    (Mod.extendRestrictAdjunction (𝟙 R)) (Mod.extendRestrictAdjunction a)
    (Mod.comapId R).inv (Mod.comapCongr ha).inv) X

omit [IsCommMonObj S] in
private lemma scalarComp_id_comp (a : R ⟶ R) [IsMonHom a] (ha : a = 𝟙 R)
    (f : R ⟶ S) [IsMonHom f] (h : a ≫ f = f) :
    scalarComp a f f h =
      Functor.isoWhiskerRight (scalarUnit a ha) (Mod.extendScalars f) ≪≫
        Functor.leftUnitor (Mod.extendScalars f) := by
  simp only [scalarComp, scalarComp_eq, scalarUnit_eq]
  apply Adjunction.leftAdjointCompIso_id_comp
  ext M
  simp only [Functor.comp_obj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Mod.comp_hom',
    Mod.comapComp_inv_app_hom, Mod.comapCongr_hom_app_hom, Functor.isoWhiskerLeft_trans,
    Iso.trans_assoc, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.id_obj,
    Functor.rightUnitor_hom_app, Category.comp_id, Mod.comapId_hom_app_hom]
  change (𝟙 M.X ≫ 𝟙 M.X) = (𝟙 M.X ≫ 𝟙 M.X)
  simp

private lemma scalarComp_comp_id (a : S ⟶ S) [IsMonHom a] (ha : a = 𝟙 S)
    (f : R ⟶ S) [IsMonHom f] (h : f ≫ a = f) :
    scalarComp f a f h =
      Functor.isoWhiskerLeft (Mod.extendScalars f) (scalarUnit a ha) ≪≫
        Functor.rightUnitor (Mod.extendScalars f) := by
  simp only [scalarComp, scalarComp_eq, scalarUnit_eq]
  apply Adjunction.leftAdjointCompIso_comp_id
  ext M
  simp
end ScalarUnit
end CategoryTheory

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section DerivedComposition
variable {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
  [Abelian C] [Abelian D] [Abelian E] [Abelian V]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory V]
  {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ V} {FG : C ⥤ E} {GH : D ⥤ V} {FGH : C ⥤ V}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
  [GH.Additive] [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
  [FGH.Additive] [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]

private lemma derivedComp_assoc (a : F ⋙ G ≅ FG) (b : FG ⋙ H ≅ FGH)
    (c : G ⋙ H ≅ GH) (d : F ⋙ GH ≅ FGH)
    (h : isoWhiskerRight a H ≪≫ b = isoWhiskerLeft F c ≪≫ d) :
    isoWhiskerRight (derivedComp a) H.mapDerivedCategory ≪≫ derivedComp b =
      isoWhiskerLeft F.mapDerivedCategory (derivedComp c) ≪≫ derivedComp d := by
  have hm : (mapDerivedCategoryNatIso (isoWhiskerRight a H)).hom ≫
      (mapDerivedCategoryNatIso b).hom =
      (mapDerivedCategoryNatIso (isoWhiskerLeft F c)).hom ≫
        (mapDerivedCategoryNatIso d).hom := by
    rw [← mapDerivedCategoryNatIso_trans, ← mapDerivedCategoryNatIso_trans, h]
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have ha := congr_app (mapDerivedCategoryNatIso_isoWhiskerRight a H) K
  have hc := congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft F c) K
  have hassoc := congr_app (mapDerivedCategoryCompIso_assoc F G H) K
  have hm' := congr_app hm K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at ha hc hassoc hm'
  simp only [derivedComp, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [← cancel_epi (H.mapDerivedCategory.map ((mapDerivedCategoryCompIso F G).inv.app K))]
  simp only [← map_comp_assoc, Iso.inv_hom_id_app_assoc]
  rw [← cancel_epi ((mapDerivedCategoryCompIso (F ⋙ G) H).inv.app K)]
  rw [← reassoc_of% ha, Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% hassoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% hc, Iso.inv_hom_id_app_assoc]
  exact hm'
end DerivedComposition
end CategoryTheory.Functor

namespace CategoryTheory.Functor
section Transport
variable {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
  {F F' : C ⥤ D} {G G' : D ⥤ E} {H H' : E ⥤ V}
  {FG FG' : C ⥤ E} {GH GH' : D ⥤ V} {FGH FGH' : C ⥤ V}
private lemma associator_trans_eq (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ V)
    {K : C ⥤ V} (e : F ⋙ G ⋙ H ≅ K) : associator F G H ≪≫ e = e := by
  ext X
  simp

private lemma transportComp_assoc (aF : F ≅ F') (aG : G ≅ G') (aH : H ≅ H')
    (aFG : FG ≅ FG') (aGH : GH ≅ GH') (aFGH : FGH ≅ FGH')
    (a : F' ⋙ G' ≅ FG') (b : FG' ⋙ H' ≅ FGH')
    (c : G' ⋙ H' ≅ GH') (d : F' ⋙ GH' ≅ FGH')
    (h : isoWhiskerRight a H' ≪≫ b = isoWhiskerLeft F' c ≪≫ d) :
    isoWhiskerRight (transportComp aF aG aFG a) H ≪≫ transportComp aFG aH aFGH b =
      isoWhiskerLeft F (transportComp aG aH aGH c) ≪≫ transportComp aF aGH aFGH d := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  have hh := congr_app (congr_arg Iso.hom h) X
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    isoWhiskerLeft_hom, whiskerLeft_app] at hh
  simp only [transportComp, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (aH.hom.naturality (aFG.hom.app X))]
  rw [← H.map_comp_assoc (aFG.inv.app X) (aFG.hom.app X),
    Iso.inv_hom_id_app, H.map_id, Category.id_comp]
  rw [reassoc_of% (aH.hom.naturality (a.hom.app X))]
  rw [reassoc_of% (aH.hom.naturality (G'.map (aF.hom.app X)))]
  rw [reassoc_of% (aH.hom.naturality (aG.hom.app (F.obj X)))]
  rw [reassoc_of% hh, reassoc_of% (c.hom.naturality (aF.hom.app X))]
  simp only [Iso.inv_hom_id_app_assoc]

end Transport
end CategoryTheory.Functor

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section DerivedUnit
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {A : C ⥤ C} {B : D ⥤ D} {F : C ⥤ D}
  [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private noncomputable abbrev derivedUnit (e : A ≅ 𝟭 C) : A.mapDerivedCategory ≅ 𝟭 _ :=
  mapDerivedCategoryNatIso e ≪≫ mapDerivedCategoryIdIso C

private lemma derivedComp_id_comp (e : A ≅ 𝟭 C) (a : A ⋙ F ≅ F)
    (h : a = isoWhiskerRight e F ≪≫ leftUnitor F) :
    derivedComp a = isoWhiskerRight (derivedUnit e) F.mapDerivedCategory ≪≫
      leftUnitor F.mapDerivedCategory := by
  rw [h]
  have he : (mapDerivedCategoryNatIso (leftUnitor F)).hom = 𝟙 _ :=
    mapDerivedCategoryNatIso_refl
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hn := congr_app (mapDerivedCategoryNatIso_isoWhiskerRight e F) K
  have hu := congr_app (mapDerivedCategoryCompIso_id_comp F) K
  simp only [NatTrans.comp_app, whiskerRight_app, NatTrans.id_app] at hn hu
  simp only [derivedComp, derivedUnit, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, map_comp, leftUnitor_hom_app,
    mapDerivedCategoryNatIso_trans, he, Category.comp_id, Category.assoc]
  rw [← cancel_epi ((mapDerivedCategoryCompIso A F).inv.app K),
    Iso.inv_hom_id_app_assoc, ← reassoc_of% hn, reassoc_of% hu, Category.comp_id]
  exact (Category.comp_id _).symm

private lemma derivedComp_comp_id (e : B ≅ 𝟭 D) (a : F ⋙ B ≅ F)
    (h : a = isoWhiskerLeft F e ≪≫ rightUnitor F) :
    derivedComp a = isoWhiskerLeft F.mapDerivedCategory (derivedUnit e) ≪≫
      rightUnitor F.mapDerivedCategory := by
  rw [h]
  have he : (mapDerivedCategoryNatIso (rightUnitor F)).hom = 𝟙 _ :=
    mapDerivedCategoryNatIso_refl
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hn := congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft F e) K
  have hu := congr_app (mapDerivedCategoryCompIso_comp_id F) K
  simp only [NatTrans.comp_app, whiskerLeft_app, NatTrans.id_app] at hn hu
  simp only [derivedComp, derivedUnit, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, rightUnitor_hom_app,
    mapDerivedCategoryNatIso_trans, he, Category.comp_id, Category.assoc]
  rw [← cancel_epi ((mapDerivedCategoryCompIso F B).inv.app K),
    Iso.inv_hom_id_app_assoc, ← reassoc_of% hn, reassoc_of% hu, Category.comp_id]
  exact (Category.comp_id _).symm
end DerivedUnit
end CategoryTheory.Functor

namespace CategoryTheory.Functor
section TransportUnit
variable {C D : Type*} [Category C] [Category D]
  {A A' : C ⥤ C} {B B' : D ⥤ D} {F F' : C ⥤ D}

private lemma transportComp_id_comp (aA : A ≅ A') (aF : F ≅ F')
    (e : A' ≅ 𝟭 C) (c : A' ⋙ F' ≅ F')
    (h : c = isoWhiskerRight e F' ≪≫ leftUnitor F') :
    transportComp aA aF aF c =
      isoWhiskerRight (aA ≪≫ e) F ≪≫ leftUnitor F := by
  rw [h]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [transportComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, isoWhiskerRight_hom, whiskerRight_app,
    leftUnitor_hom_app, map_comp, Category.assoc]
  rw [← reassoc_of% (aF.hom.naturality (aA.hom.app X))]
  rw [← reassoc_of% (aF.hom.naturality (e.hom.app X))]
  simp only [Functor.id_obj]
  simp

private lemma transportComp_comp_id (aB : B ≅ B') (aF : F ≅ F')
    (e : B' ≅ 𝟭 D) (c : F' ⋙ B' ≅ F')
    (h : c = isoWhiskerLeft F' e ≪≫ rightUnitor F') :
    transportComp aF aB aF c =
      isoWhiskerLeft F (aB ≪≫ e) ≪≫ rightUnitor F := by
  rw [h]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [transportComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, isoWhiskerRight_hom, whiskerRight_app,
    rightUnitor_hom_app, Category.assoc]
  rw [reassoc_of% (e.hom.naturality (aF.hom.app X))]
  simp
end TransportUnit
end CategoryTheory.Functor

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section LeftTransport
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

variable [MonoidalCategory E] [MonoidalPreadditive E]
  [HasCountableCoproducts E]
  [HasColimitsOfShape ℤ E] [HasExactColimitsOfShape ℤ E]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ E), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : E), PreservesColimitsOfShape ℤ ((curriedTensor E).obj X)]
  [∀ (X : E), PreservesColimitsOfShape ℤ ((curriedTensor E).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution E]
  {V : Type*} [Category V] [Abelian V] [HasDerivedCategory V]
private lemma leftComp_assoc
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : E ⥤ V) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {FG : C ⥤ E} [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    {GH : D ⥤ V} [GH.Additive] [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
    {FGH : C ⥤ V} [FGH.Additive] [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]
    (a : F ⋙ G ≅ FG) (b : FG ⋙ H ≅ FGH) (c : G ⋙ H ≅ GH) (d : F ⋙ GH ≅ FGH)
    (h : isoWhiskerRight a H ≪≫ b = associator F G H ≪≫ isoWhiskerLeft F c ≪≫ d) :
    isoWhiskerRight
        ((F.leftDerivedFunctorCompIso G).symm ≪≫ (F ⋙ G).leftDerivedFunctorNatIso a)
        H.leftDerivedFunctor ≪≫
      (FG.leftDerivedFunctorCompIso H).symm ≪≫ (FG ⋙ H).leftDerivedFunctorNatIso b =
    associator F.leftDerivedFunctor G.leftDerivedFunctor H.leftDerivedFunctor ≪≫
      isoWhiskerLeft F.leftDerivedFunctor
        ((G.leftDerivedFunctorCompIso H).symm ≪≫ (G ⋙ H).leftDerivedFunctorNatIso c) ≪≫
      (F.leftDerivedFunctorCompIso GH).symm ≪≫ (F ⋙ GH).leftDerivedFunctorNatIso d := by
  simp only [leftComp_transport, associator_trans_eq]
  apply transportComp_assoc
  apply derivedComp_assoc
  simpa only [associator_trans_eq] using h


end LeftTransport
end CategoryTheory.Functor

namespace CategoryTheory.Functor
section IdentityShift
variable (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]

omit [HasDerivedCategory C] in
private lemma complexId_shift :
    NatTrans.CommShift (mapHomologicalComplexIdIso C (.up ℤ)).hom ℤ where
  shift_comm n := by
    ext K i
    dsimp
    simp

omit [HasDerivedCategory C] in
private lemma homotopyId_shift :
    NatTrans.CommShift (mapHomotopyCategoryIdIso C (.up ℤ)).hom ℤ := by
  have := complexId_shift C
  have he : whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (mapHomotopyCategoryIdIso C (.up ℤ)).hom =
      ((𝟭 C).mapHomotopyCategoryFactors (.up ℤ)).hom ≫
        whiskerRight (mapHomologicalComplexIdIso C (.up ℤ)).hom
          (HomotopyCategory.quotient C (.up ℤ)) ≫
        (HomotopyCategory.quotient C (.up ℤ)).leftUnitor.hom ≫
        (HomotopyCategory.quotient C (.up ℤ)).rightUnitor.inv := by
    ext K
    simp only [comp_obj, id_obj, whiskerLeft_app, mapHomotopyCategoryIdIso_hom_app,
      NatTrans.comp_app, whiskerRight_app, leftUnitor_hom_app, rightUnitor_inv_app,
      Category.comp_id]
    exact (Category.id_comp _).symm
  have : NatTrans.CommShift (whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (mapHomotopyCategoryIdIso C (.up ℤ)).hom) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient C (.up ℤ))
    (fun X ↦ by
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      exact ⟨K, 𝟙 _, inferInstance⟩)

private lemma derivedId_shift :
    NatTrans.CommShift (mapDerivedCategoryIdIso C).hom ℤ := by
  have := homotopyId_shift C
  have he : whiskerLeft DerivedCategory.Qh (mapDerivedCategoryIdIso C).hom =
      (𝟭 C).mapDerivedCategoryFactorsh.hom ≫
        whiskerRight (mapHomotopyCategoryIdIso C (.up ℤ)).hom DerivedCategory.Qh ≫
        DerivedCategory.Qh.leftUnitor.hom ≫ DerivedCategory.Qh.rightUnitor.inv := by
    have h := congr_arg Iso.hom (mapDerivedCategoryIdIso_factorsh C)
    rw [← cancel_mono DerivedCategory.Qh.rightUnitor.hom]
    simpa only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using h
  have : NatTrans.CommShift (whiskerLeft DerivedCategory.Qh
      (mapDerivedCategoryIdIso C).hom) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso X).inv, inferInstance⟩)
end IdentityShift
end CategoryTheory.Functor

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section LeftShift
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

private lemma leftUnit_shift (A : C ⥤ C) [A.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A] (e : A ≅ 𝟭 C) :
    let := CommShift.ofIso A.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    NatTrans.CommShift (A.leftDerivedFunctorNatIso e ≪≫
      (𝟭 C).leftDerivedFunctorIsoMapDerivedCategory ≪≫ mapDerivedCategoryIdIso C).hom ℤ := by
  let := CommShift.ofIso A.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift A.leftDerivedFunctorIsoMapDerivedCategory.symm.hom ℤ :=
    CommShift.ofIso_compatibility A.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift A.leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
    NatTrans.CommShift.of_iso_inv A.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have := derivedId_shift C
  simp only [leftDerivedFunctorNatIso, Iso.trans_assoc, Iso.symm_self_id_assoc,
    Iso.trans_hom]
  infer_instance
end LeftShift
end CategoryTheory.Functor

namespace CategoryTheory
section ScalarDerived
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{vC} C] [Abelian.HasFunctorialFlatResolution C]
  {R S U V : C} [MonObj R] [MonObj S] [MonObj U] [MonObj V]
  [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj U] [IsCommMonObj V]
  [HasDerivedCategory.{vC} (Mod C R)] [HasDerivedCategory.{vC} (Mod C S)]
  [HasDerivedCategory.{vC} (Mod C U)] [HasDerivedCategory.{vC} (Mod C V)]

private theorem scalarCalculus (φ : R ⟶ S) [IsMonHom φ]
    [PreservesFiniteLimits (Mod.extendScalars φ)] :
    let := Functor.CommShift.ofIso
      (Mod.extendScalars φ).leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    PreservesFiniteLimits (Mod.extendScalars φ) ∧
    PreservesFiniteColimits (Mod.extendScalars φ) ∧
    PreservesFiniteLimits
      (Mod.comap φ :
        Mod C S ⥤
          Mod C R) ∧
    PreservesFiniteColimits
      (Mod.comap φ :
        Mod C S ⥤
          Mod C R) ∧
    Nonempty ((Mod.extendScalars φ) ⊣ (Mod.comap
      φ)) ∧
    Nonempty (DerivedCategory.Q ⋙ (Mod.extendScalars φ).leftDerivedFunctor ≅
      (Mod.extendScalars φ).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
    Nonempty ((Mod.extendScalars φ).leftDerivedFunctor ⊣
      (Mod.comap φ).mapDerivedCategory) ∧
    Nonempty ((Mod.extendScalars φ).leftDerivedFunctor ≅
      (Mod.extendScalars φ).mapDerivedCategory) ∧
    (Mod.extendScalars φ).leftDerivedFunctor.IsTriangulated ∧
    (∀ n : ℤ, Nonempty (shiftFunctor (DerivedCategory (Mod C R)) n ⋙
      (Mod.extendScalars φ).leftDerivedFunctor ≅
        (Mod.extendScalars φ).leftDerivedFunctor ⋙
        shiftFunctor (DerivedCategory (Mod C S)) n)) := by
  let f := Mod.extendScalars φ
  let := Functor.CommShift.ofIso f.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Mod.extendRestrictAdjunction _⟩, ?_,
    ⟨((Mod.extendRestrictAdjunction φ).derivedAdjunction).ofNatIsoRight
      (Mod.comap φ).rightDerivedFunctorIsoMapDerivedCategory⟩,
    ⟨f.leftDerivedFunctorIsoMapDerivedCategory⟩, ?_, ?_⟩
  · exact ⟨Functor.isoWhiskerLeft DerivedCategory.Q
      f.leftDerivedFunctorIsoMapDerivedCategory ≪≫ f.mapDerivedCategoryFactors⟩
  · let e := f.leftDerivedFunctorIsoMapDerivedCategory.symm
    have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
    exact Functor.isTriangulated_of_iso e
  · intro n
    exact ⟨f.leftDerivedFunctor.commShiftIso n⟩

private noncomputable abbrev scalarDerivedComp
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ U) [IsMonHom g]
    (fg : R ⟶ U) [IsMonHom fg] (h : f ≫ g = fg)
    [PreservesFiniteLimits (Mod.extendScalars f)]
    [PreservesFiniteLimits (Mod.extendScalars g)]
    [PreservesFiniteLimits (Mod.extendScalars fg)] :=
  ((Mod.extendScalars f).leftDerivedFunctorCompIso (Mod.extendScalars g)).symm ≪≫
    ((Mod.extendScalars f) ⋙ (Mod.extendScalars g)).leftDerivedFunctorNatIso
      (scalarComp f g fg h)

private noncomputable abbrev scalarDerivedUnit
    (a : R ⟶ R) [IsMonHom a] (ha : a = 𝟙 R)
    [PreservesFiniteLimits (Mod.extendScalars a)] :=
  (Mod.extendScalars a).leftDerivedFunctorNatIso (scalarUnit a ha) ≪≫
    (𝟭 (Mod C R)).leftDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryIdIso (Mod C R)
private lemma scalarDerivedComp_assoc
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ U) [IsMonHom g] (j : U ⟶ V) [IsMonHom j]
    (fg : R ⟶ U) [IsMonHom fg] (gj : S ⟶ V) [IsMonHom gj]
    (fgj : R ⟶ V) [IsMonHom fgj]
    (hfg : f ≫ g = fg) (hgj : g ≫ j = gj) (hfgj : f ≫ gj = fgj) (hfgj' : fg ≫ j = fgj)
    [PreservesFiniteLimits (Mod.extendScalars f)]
    [PreservesFiniteLimits (Mod.extendScalars g)]
    [PreservesFiniteLimits (Mod.extendScalars j)]
    [PreservesFiniteLimits (Mod.extendScalars fg)]
    [PreservesFiniteLimits (Mod.extendScalars gj)]
    [PreservesFiniteLimits (Mod.extendScalars fgj)] :
    Functor.isoWhiskerRight (scalarDerivedComp f g fg hfg)
        (Mod.extendScalars j).leftDerivedFunctor ≪≫ scalarDerivedComp fg j fgj hfgj' =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (Mod.extendScalars f).leftDerivedFunctor
          (scalarDerivedComp g j gj hgj) ≪≫ scalarDerivedComp f gj fgj hfgj := by
  unfold scalarDerivedComp
  apply Functor.leftComp_assoc
  exact scalarComp_assoc f g j fg gj fgj hfg hgj hfgj hfgj'

private lemma scalarDerivedComp_id_comp
    (a : R ⟶ R) [IsMonHom a] (ha : a = 𝟙 R)
    (f : R ⟶ S) [IsMonHom f] (h : a ≫ f = f)
    [PreservesFiniteLimits (Mod.extendScalars a)]
    [PreservesFiniteLimits (Mod.extendScalars f)] :
    scalarDerivedComp a f f h =
      Functor.isoWhiskerRight (scalarDerivedUnit a ha) (Mod.extendScalars f).leftDerivedFunctor ≪≫
        Functor.leftUnitor _ := by
  simp only [scalarDerivedComp, Functor.leftComp_transport]
  simp only [scalarDerivedUnit, Functor.leftDerivedFunctorNatIso,
    Iso.trans_assoc, Iso.symm_self_id_assoc]
  apply Functor.transportComp_id_comp
  apply Functor.derivedComp_id_comp
  exact scalarComp_id_comp a ha f h

private lemma scalarDerivedComp_comp_id
    (a : S ⟶ S) [IsMonHom a] (ha : a = 𝟙 S)
    (f : R ⟶ S) [IsMonHom f] (h : f ≫ a = f)
    [PreservesFiniteLimits (Mod.extendScalars a)]
    [PreservesFiniteLimits (Mod.extendScalars f)] :
    scalarDerivedComp f a f h =
      Functor.isoWhiskerLeft (Mod.extendScalars f).leftDerivedFunctor (scalarDerivedUnit a ha) ≪≫
        Functor.rightUnitor _ := by
  simp only [scalarDerivedComp, Functor.leftComp_transport]
  simp only [scalarDerivedUnit, Functor.leftDerivedFunctorNatIso,
    Iso.trans_assoc, Iso.symm_self_id_assoc]
  apply Functor.transportComp_comp_id
  apply Functor.derivedComp_comp_id
  exact scalarComp_comp_id a ha f h


private lemma scalarDerivedComp_shift
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ U) [IsMonHom g]
    (fg : R ⟶ U) [IsMonHom fg] (h : f ≫ g = fg)
    [PreservesFiniteLimits (Mod.extendScalars f)]
    [PreservesFiniteLimits (Mod.extendScalars g)]
    [PreservesFiniteLimits (Mod.extendScalars fg)] :
    let := Functor.CommShift.ofIso
      (Mod.extendScalars f).leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    let := Functor.CommShift.ofIso
      (Mod.extendScalars g).leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    let := Functor.CommShift.ofIso
      (Mod.extendScalars fg).leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    NatTrans.CommShift (scalarDerivedComp f g fg h).hom ℤ :=
  Functor.leftComp_shift _ _ (scalarComp f g fg h)

private lemma scalarDerivedUnit_shift
    (a : R ⟶ R) [IsMonHom a] (ha : a = 𝟙 R)
    [PreservesFiniteLimits (Mod.extendScalars a)] :
    let := Functor.CommShift.ofIso
      (Mod.extendScalars a).leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    NatTrans.CommShift (scalarDerivedUnit a ha).hom ℤ :=
  Functor.leftUnit_shift _ (scalarUnit a ha)
end ScalarDerived
end CategoryTheory

end CoherenceTools

end ModuleCacheScope

namespace AlgebraicGeometry.ProEtale

open Scheme
open CategoryTheory.MonObj CategoryTheory.Functor
open scoped CategoryTheory.Obj CategoryTheory.Functor

section FiniteFree

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

private theorem point_finiteFree (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)} (h : E ≤ F) :
    Nonempty ((Mod.comap (Profinite.padicSubfieldRingObjMap.{u} ℓ h)).obj
      (Mod.regular (Profinite.continuousMapRingObj F)) ≅
      Mod.finiteFree (Profinite.continuousMapRingObj E)
        (@Module.finrank E F inferInstance inferInstance
          (Module.compHom F (IntermediateField.inclusion h).toRingHom))) := by
  let := Sheaf.symmetricCategory (coherentTopology Profinite.{u}) Ab.{u + 1}
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[ℓ] E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E F
  let b := Module.finBasis E F
  have hb (i : Fin (Module.finrank E F)) : Continuous (b.coord i) :=
    ((b.coord i).restrictScalars ℚ_[ℓ]).continuous_of_finiteDimensional
  have ha : Continuous (algebraMap E F) := continuous_subtype_val.subtype_mk _
  exact ⟨Profinite.continuousBasisSheafIso ha _ b hb⟩

private theorem scheme_finiteFree (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)} (h : E ≤ F) :
    Nonempty ((Mod.comap (padicSubfieldRingObjMap T ℓ h)).obj
      (Mod.regular (padicSubfieldRingObj T ℓ F)) ≅
      Mod.finiteFree (padicSubfieldRingObj T ℓ E)
        (@Module.finrank E F inferInstance inferInstance
          (Module.compHom F (IntermediateField.inclusion h).toRingHom))) := by
  let := Sheaf.symmetricCategory (coherentTopology Profinite.{u}) Ab.{u + 1}
  obtain ⟨e⟩ := point_finiteFree.{u} ℓ h
  have : (upperStarFromPoint T).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  exact ⟨Mod.mapFreeRestrictedRegularIso (upperStarFromPoint T)
    (Profinite.padicSubfieldRingObjMap ℓ h) _ e⟩

end FiniteFree

/-- Source: Compatibility.lean, A0.2 and Flat; ordinary module tensor adjunction;
TwoColimit.lean, ExtendScalars
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).
Proof: choose a finite field basis; its coordinate maps are continuous by the
finite-dimensional linear homeomorphism lemma. Continuous maps on profinite sets
therefore identify the finite coefficient module with the free module of that rank.
The exact strong monoidal inverse image from the point preserves this identification.
The tensor/restriction adjunction is given by `p ↦ 1 ⊗ p` and multiplication.
Restriction is exact because it only changes the action. Finite-stage tensor is exact
because its underlying module is a finite direct sum. For the algebraic closure, its
finite-stage coefficient cocone is a filtered colimit already on the finite-cover
basis of profinite sets; pullback preserves this colimit. Module sheaf filtered
colimits are exact and commute with tensor, giving flatness at the closure.
The exact-functor factorization and exact-derived-functor lemmas identify derivation
with termwise tensor on every complex, with its canonical shifts and cone triangles.
Descend the termwise unit and counit through localization; their triangle identities
are detected before localization, yielding the unbounded derived adjunction. -/
theorem condensedFiniteCoefficientCalculus
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)} (h : E ≤ F) :
    Nonempty ((Mod.comap (padicSubfieldRingObjMap T ℓ h)).obj (Mod.regular (padicSubfieldRingObj T ℓ
      F)) ≅
      Mod.finiteFree (padicSubfieldRingObj T ℓ E) (@Module.finrank E F inferInstance inferInstance
          (Module.compHom F (IntermediateField.inclusion h).toRingHom))) ∧
    PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)) ∧
    PreservesFiniteColimits (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)) ∧
    PreservesFiniteLimits
      (Mod.comap (padicSubfieldRingObjMap T ℓ h) :
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ F) ⥤
          Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)) ∧
    PreservesFiniteColimits
      (Mod.comap (padicSubfieldRingObjMap T ℓ h) :
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ F) ⥤
          Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)) ⊣ (Mod.comap
      (padicSubfieldRingObjMap T ℓ h))) ∧
    Nonempty (DerivedCategory.Q ⋙ (Mod.extendScalars (padicSubfieldRingObjMap T ℓ
      h)).leftDerivedFunctor ≅
      (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).mapHomologicalComplex (ComplexShape.up ℤ)
        ⋙ DerivedCategory.Q) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor ⊣ (Mod.comap
      (padicSubfieldRingObjMap T ℓ h)).mapDerivedCategory) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor ≅
      (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).mapDerivedCategory) ∧
    (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor.IsTriangulated ∧
    (∀ n : ℤ, Nonempty (shiftFunctor (DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (padicSubfieldRingObj T ℓ E))) n ⋙
      (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor ≅ (Mod.extendScalars
        (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor ⋙ shiftFunctor (DerivedCategory (Mod
        (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ F))) n)) := by
  let := scalarAbelian (C := Sheaf (ProEt.topology T) Ab.{u + 1})
  let := scalarMonoidal (C := Sheaf (ProEt.topology T) Ab.{u + 1})
  let := scalarHasDerived (C := Sheaf (ProEt.topology T) Ab.{u + 1})
  exact ⟨scheme_finiteFree T ℓ h, scalarCalculus (padicSubfieldRingObjMap T ℓ h)⟩

/-- Source: Compatibility.lean, A0.2 and Flat; ordinary module tensor adjunction;
TwoColimit.lean, ExtendScalars
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).
Proof: choose a finite field basis; its coordinate maps are continuous by the
finite-dimensional linear homeomorphism lemma. Continuous maps on profinite sets
therefore identify the finite coefficient module with the free module of that rank.
The exact strong monoidal inverse image from the point preserves this identification.
The tensor/restriction adjunction is given by `p ↦ 1 ⊗ p` and multiplication.
Restriction is exact because it only changes the action. Finite-stage tensor is exact
because its underlying module is a finite direct sum. For the algebraic closure, its
finite-stage coefficient cocone is a filtered colimit already on the finite-cover
basis of profinite sets; pullback preserves this colimit. Module sheaf filtered
colimits are exact and commute with tensor, giving flatness at the closure.
The exact-functor factorization and exact-derived-functor lemmas identify derivation
with termwise tensor on every complex, with its canonical shifts and cone triangles.
Descend the termwise unit and counit through localization; their triangle identities
are detected before localization, yielding the unbounded derived adjunction. -/
theorem condensedAlgClCoefficientCalculus
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)) ∧
    PreservesFiniteColimits (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)) ∧
    PreservesFiniteLimits
      (Mod.comap (padicSubfieldRingObjToPadicAlgCl T ℓ E) :
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ) ⥤
          Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)) ∧
    PreservesFiniteColimits
      (Mod.comap (padicSubfieldRingObjToPadicAlgCl T ℓ E) :
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ) ⥤
          Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)) ⊣ (Mod.comap
      (padicSubfieldRingObjToPadicAlgCl T ℓ E))) ∧
    Nonempty (DerivedCategory.Q ⋙ (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ
      E)).leftDerivedFunctor ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor ⊣
      (Mod.comap (padicSubfieldRingObjToPadicAlgCl T ℓ E)).mapDerivedCategory) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).mapDerivedCategory) ∧
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor.IsTriangulated ∧
    (∀ n : ℤ, Nonempty (shiftFunctor (DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (padicSubfieldRingObj T ℓ E))) n ⋙
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor ≅
        (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor ⋙
        shiftFunctor (DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj
        T ℓ))) n)) := by
  let := scalarAbelian (C := Sheaf (ProEt.topology T) Ab.{u + 1})
  let := scalarMonoidal (C := Sheaf (ProEt.topology T) Ab.{u + 1})
  let := scalarHasDerived (C := Sheaf (ProEt.topology T) Ab.{u + 1})
  exact scalarCalculus (padicSubfieldRingObjToPadicAlgCl T ℓ E)

/-- Coherence of the canonical multiplication and unit comparisons.
Source: TwoColimit.lean, ExtendScalars; sheaf tensor coherence and localization
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).
Proof: multiplication and its inverse are balanced and natural before sheafification.
The two associativity paths send `d ⊗ (c ⊗ (b ⊗ p))` to `dcb ⊗ p`.
Together with associativity of functor composition this gives the five-ring pentagon:
every path sends `h ⊗ (d ⊗ (c ⊗ (b ⊗ p)))` to `hdcb ⊗ p`.
The unit sends `a ⊗ p` to `ap`; either insertion of it in a multiplication comparison
has the same value. The same calculations hold with the last ring the closure.
These are equalities of maps from presheaf tensors and pass through the universal
property of sheafification, without asserting that global sections are pure tensors.
Apply these comparisons termwise. Shifts introduce the same differential sign on both
sides, and all coefficient factors have degree zero. Localization descends these
transformations and detects their equalities, proving the unit, associativity,
pentagon and shift compatibility laws. -/
theorem condensedCoefficientCoherence
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime] :
    (∀ (E F G H : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (h : E ≤ F) (k : F ≤ G) (l : G ≤ H),
      Functor.isoWhiskerRight (condensedCoefficientCompIso T ℓ h k) (derivedExtendScalarsSubfield T
        ℓ l) ≪≫
          (condensedCoefficientCompIso T ℓ (h.trans k) l) =
        Functor.associator (derivedExtendScalarsSubfield T ℓ h) (derivedExtendScalarsSubfield T ℓ k)
          (derivedExtendScalarsSubfield T ℓ l) ≪≫
          Functor.isoWhiskerLeft (derivedExtendScalarsSubfield T ℓ h) (condensedCoefficientCompIso T
            ℓ k l)
            ≪≫
          (condensedCoefficientCompIso T ℓ h (k.trans l))) ∧
    (∀ (E F G : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F) (k : F ≤ G),
      Functor.isoWhiskerRight (condensedCoefficientCompIso T ℓ h k)
        (derivedExtendScalarsToPadicAlgCl T ℓ G)
        ≪≫ (derivedExtendScalarsCompIso T ℓ (h.trans k)) =
        Functor.associator (derivedExtendScalarsSubfield T ℓ h) (derivedExtendScalarsSubfield T ℓ k)
          (derivedExtendScalarsToPadicAlgCl T ℓ G) ≪≫
          Functor.isoWhiskerLeft (derivedExtendScalarsSubfield T ℓ h) (derivedExtendScalarsCompIso T
            ℓ k) ≪≫
            (derivedExtendScalarsCompIso T ℓ h)) ∧
    (∀ (E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F),
      (condensedCoefficientCompIso T ℓ (le_refl E) h) =
        Functor.isoWhiskerRight (condensedCoefficientUnitIso T ℓ E) (derivedExtendScalarsSubfield T
          ℓ h) ≪≫
          Functor.leftUnitor (derivedExtendScalarsSubfield T ℓ h)) ∧
    (∀ (E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F),
      (condensedCoefficientCompIso T ℓ h (le_refl F)) =
        Functor.isoWhiskerLeft (derivedExtendScalarsSubfield T ℓ h) (condensedCoefficientUnitIso T ℓ
          F) ≪≫
          Functor.rightUnitor (derivedExtendScalarsSubfield T ℓ h)) ∧
    (∀ E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ),
      (derivedExtendScalarsCompIso T ℓ (le_refl E)) =
        Functor.isoWhiskerRight (condensedCoefficientUnitIso T ℓ E)
          (derivedExtendScalarsToPadicAlgCl T ℓ E)
          ≪≫ Functor.leftUnitor (derivedExtendScalarsToPadicAlgCl T ℓ E)) ∧
    (∀ (E F G : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F) (k : F ≤ G),
      NatTrans.CommShift (condensedCoefficientCompIso T ℓ h k).hom ℤ) ∧
    (∀ (E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F),
      NatTrans.CommShift (derivedExtendScalarsCompIso T ℓ h).hom ℤ) ∧
    (∀ E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ), NatTrans.CommShift
      (condensedCoefficientUnitIso T ℓ E).hom ℤ) := by
  let := scalarAbelian (C := Sheaf (ProEt.topology T) Ab.{u + 1})
  let := scalarMonoidal (C := Sheaf (ProEt.topology T) Ab.{u + 1})
  let := scalarHasDerived (C := Sheaf (ProEt.topology T) Ab.{u + 1})
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro E F G H h k l
    exact scalarDerivedComp_assoc
      (padicSubfieldRingObjMap T ℓ h) (padicSubfieldRingObjMap T ℓ k)
      (padicSubfieldRingObjMap T ℓ l) (padicSubfieldRingObjMap T ℓ (h.trans k))
      (padicSubfieldRingObjMap T ℓ (k.trans l))
      (padicSubfieldRingObjMap T ℓ ((h.trans k).trans l))
      (condensedCoefficientMap_comp T ℓ h k) (condensedCoefficientMap_comp T ℓ k l)
      (condensedCoefficientMap_comp T ℓ h (k.trans l))
      (condensedCoefficientMap_comp T ℓ (h.trans k) l)
  · intro E F G h k
    exact scalarDerivedComp_assoc
      (padicSubfieldRingObjMap T ℓ h) (padicSubfieldRingObjMap T ℓ k)
      (padicSubfieldRingObjToPadicAlgCl T ℓ G)
      (padicSubfieldRingObjMap T ℓ (h.trans k))
      (padicSubfieldRingObjToPadicAlgCl T ℓ F) (padicSubfieldRingObjToPadicAlgCl T ℓ E)
      (condensedCoefficientMap_comp T ℓ h k)
      (padicSubfieldRingObjMap_comp_toPadicAlgCl T ℓ k)
      (padicSubfieldRingObjMap_comp_toPadicAlgCl T ℓ h)
      (padicSubfieldRingObjMap_comp_toPadicAlgCl T ℓ (h.trans k))
  · intro E F h
    exact scalarDerivedComp_id_comp (padicSubfieldRingObjMap T ℓ (le_refl E))
      (condensedCoefficientMap_id T ℓ E) (padicSubfieldRingObjMap T ℓ h)
      (condensedCoefficientMap_comp T ℓ (le_refl E) h)
  · intro E F h
    exact scalarDerivedComp_comp_id (padicSubfieldRingObjMap T ℓ (le_refl F))
      (condensedCoefficientMap_id T ℓ F) (padicSubfieldRingObjMap T ℓ h)
      (condensedCoefficientMap_comp T ℓ h (le_refl F))
  · intro E
    exact scalarDerivedComp_id_comp (padicSubfieldRingObjMap T ℓ (le_refl E))
      (condensedCoefficientMap_id T ℓ E) (padicSubfieldRingObjToPadicAlgCl T ℓ E)
      (padicSubfieldRingObjMap_comp_toPadicAlgCl T ℓ (le_refl E))
  · intro E F G h k
    exact scalarDerivedComp_shift (padicSubfieldRingObjMap T ℓ h)
      (padicSubfieldRingObjMap T ℓ k) (padicSubfieldRingObjMap T ℓ (h.trans k))
      (condensedCoefficientMap_comp T ℓ h k)
  · intro E F h
    exact scalarDerivedComp_shift (padicSubfieldRingObjMap T ℓ h)
      (padicSubfieldRingObjToPadicAlgCl T ℓ F) (padicSubfieldRingObjToPadicAlgCl T ℓ E)
      (padicSubfieldRingObjMap_comp_toPadicAlgCl T ℓ h)
  · intro E
    exact scalarDerivedUnit_shift (padicSubfieldRingObjMap T ℓ (le_refl E))
      (condensedCoefficientMap_id T ℓ E)

end AlgebraicGeometry.ProEtale
