/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyFiniteTorDimension
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes
import WeilConjectures.AlgebraicGeometry.OpenRestrictionKFlatModel
import WeilConjectures.AlgebraicGeometry.OpenRestrictionTotalTensor

/-! # Locality of a fixed Tor amplitude interval

Source: Stacks Project, Cohomology of Sheaves, Lemma 09U9
(cohomology-lemma-tor-amplitude-stalk).
(blueprint: lem-pc-tor-amplitude-open-local).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private noncomputable local instance (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

private theorem exists_kFlat_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) :
    ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := X.sheaf) P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E) := by
  let M := DerivedCategory.Q.objPreimage E
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) M
  have : QuasiIso s := hs
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map s) ≪≫
    DerivedCategory.Q.objObjPreimageIso E⟩⟩

private theorem tensor_model_iso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P) :
    Nonempty (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N (curriedTensor _))) := by
  obtain ⟨e⟩ := kFlat_derivedTensor_comparison_natIso X
    ((Functor.const (Discrete PUnit.{1})).obj P)
    ((Functor.const (Discrete PUnit.{1})).obj N) (fun _ ↦ hP)
  exact ⟨(e.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩⟩

private theorem tensor_vanishes_iff (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (G : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ) :
    schemeDerivedTensorCohomologyVanishes X E G i ↔
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (E ⊗ (DerivedCategory.singleFunctor _ 0).obj G)) := by
  let N := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G
  constructor
  · rintro ⟨P, hP, ⟨eP⟩, hz⟩
    obtain ⟨cmp⟩ := tensor_model_iso X P N hP
    let e := (tensorIso eP (Iso.refl (DerivedCategory.Q.obj N))).symm ≪≫ cmp
    exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _)
  · intro hz
    obtain ⟨P, hP, ⟨eP⟩⟩ := exists_kFlat_model X E
    refine ⟨P, hP, ⟨eP⟩, ?_⟩
    obtain ⟨cmp⟩ := tensor_model_iso X P N hP
    let e := (tensorIso eP (Iso.refl (DerivedCategory.Q.obj N))).symm ≪≫ cmp
    exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _).symm

private theorem open_pullback_model_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := Y.sheaf) P) :
    Nonempty ((derivedPullback f).obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj
      (((Scheme.Modules.restrictFunctor f).mapHomologicalComplex (.up ℤ)).obj P)) := by
  classical
  have d := derivedPullback_spec f
  obtain ⟨T, hT, hTmap, hTadd, ε, _, _, hflat⟩ :=
    d.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2
  let T₀ := Scheme.Modules.tensorPullback f
  have hEq : T = T₀ := CategoryTheory.Functor.ext hT (fun _ _ a ↦ hTmap a)
  subst T
  have : T₀.Additive := hTadd
  have : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hflat P hP
  let θ : T₀ ≅ Scheme.Modules.restrictFunctor f :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
      (Scheme.Modules.restrictAdjunction f)
  exact ⟨(derivedPullback f).mapIso
    ((DerivedCategory.quotientCompQhIso _).symm.app P) ≪≫
    asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
    DerivedCategory.Qh.mapIso ((T₀.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex θ (.up ℤ)).app P)⟩

private theorem open_pullback_restriction_iso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) :
    let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)
    Nonempty (R.mapDerivedCategory.obj E ≅ (derivedPullback U.ι).obj E) := by
  classical
  dsimp only
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_kFlat_model X E
  let S : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.restrictFunctor U.ι
  let θ : R ≅ S := Scheme.Modules.overFunctorEquiv U
  have : R.Additive := inferInstance
  have : S.Additive := Functor.additive_of_iso θ
  obtain ⟨cmp⟩ := open_pullback_model_iso U.ι P hP
  exact ⟨R.mapDerivedCategory.mapIso eP.symm ≪≫ R.mapDerivedCategoryFactors.app P ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex θ (.up ℤ)).app P) ≪≫
    cmp.symm ≪≫ (derivedPullback U.ι).mapIso eP⟩

/-- Tor amplitude in a fixed interval can be checked on open neighbourhoods.
Source: Stacks Project, Cohomology of Sheaves, Lemma 09U9
(cohomology-lemma-tor-amplitude-stalk), its proof using exact stalks and tensor.
(blueprint: lem-pc-tor-amplitude-open-local).

Proof: Fix a global module sheaf G and a degree i outside [a,b]. Choose a K-flat
representative P of E. Its total tensor with G[0] computes the global derived tensor.
For each x choose U from the hypothesis. Exact open restriction preserves K-flatness
and total tensor, so the restriction of this tensor computes E|_U tensor^L G|_U.
The local hypothesis, applied to G|_U and i, says the i-th cohomology of this derived
tensor is zero. Independence of K-flat models identifies this with the restriction of
the i-th cohomology of P tensor G[0]. Its stalk at x is therefore zero. As x was
arbitrary and stalks detect zero sheaves, the global cohomology sheaf is zero.
The chosen P and its localization isomorphism witness the required existential
vanishing predicate. For the empty scheme the stalk argument is vacuous and still
valid, since its only module sheaf is zero. No quasi-coherence or compactness is needed.
-/
theorem torAmplitude_of_open_neighbourhoods (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) (a b : ℤ) (hab : a ≤ b)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∀ (G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (i : ℤ),
        i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes U.toScheme
          ((derivedPullback U.ι).obj E) G i) :
    ∀ (G : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ),
      i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes X E G i := by
  classical
  have _hab := hab
  intro G i hi
  apply (tensor_vanishes_iff X E G i).2
  choose U hx hU using h
  have hcover : ⨆ x, U x = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply Scheme.Modules.isZero_of_iSup_eq_top _ U hcover
  intro x
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (U x) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (U x)))
      (D := SheafOfModules.{u} (moduleRings (U x).toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv (U x))
  have hz := (tensor_vanishes_iff (U x).toScheme
    ((derivedPullback (U x).ι).obj E) (R.obj G) i).1 (hU x (R.obj G) i hi)
  obtain ⟨pullbackIso⟩ := open_pullback_restriction_iso X (U x) E
  obtain ⟨tensorIso'⟩ := derivedTensor_openRestriction_iso_universes X (U x)
    E ((DerivedCategory.singleFunctor _ 0).obj G)
  let cmp := tensorIso' ≪≫ tensorIso pullbackIso
    ((R.mapDerivedCategorySingleFunctor 0).app G)
  have hz' := hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso cmp)
  have hzR := hz'.of_iso ((R.mapDerivedCategoryHomologyFunctorIso i).app
    (E ⊗ (DerivedCategory.singleFunctor _ 0).obj G))
  exact hzR.of_iso ((Scheme.Modules.overFunctorEquiv (U x)).app
    ((DerivedCategory.homologyFunctor _ i).obj
      (E ⊗ (DerivedCategory.singleFunctor _ 0).obj G))).symm

end AlgebraicGeometry
