/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Algebra.Homology.DerivedFreeModuleHomology
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Perfect generation over an affine base

Source: literature/stacks-project/perfect.tex, Tags 06Z0 and 09IS
(blueprint: lem-pc-perfect-generation-affine-base).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The free rank-one module detects vanishing by computing every cohomology group. -/
private theorem freeModule_detects_zero (A : Type u) [Ring A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (M : DerivedCategory (ModuleCat.{u} A))
    (h : ∀ n : ℤ, Subsingleton
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A A))⟦n⟧ ⟶ M)) : IsZero M := by
  classical
  let C := ModuleCat.{u} A
  let S := (DerivedCategory.singleFunctor C 0).obj (ModuleCat.of A A)
  obtain ⟨e, _⟩ := derivedFreeModule_hom_homology A
  apply DerivedCategory.isZero_of_forall_isZero_homology M
  intro n
  let b := shiftEquiv' (DerivedCategory C) (-n) n (by omega)
  have : Subsingleton (b.functor.obj S ⟶ M) := h (-n)
  have : Subsingleton (S ⟶ b.inverse.obj M) :=
    (b.toAdjunction.homEquiv S M).symm.subsingleton
  have : Subsingleton (S ⟶ M⟦n⟧) := ‹Subsingleton (S ⟶ b.inverse.obj M)›
  have hz : IsZero ((DerivedCategory.homologyFunctor C 0).obj (M⟦n⟧)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact (e (M⟦n⟧)).toEquiv.symm.subsingleton
  exact IsZero.of_iso hz
    (((DerivedCategory.homologyFunctor C 0).shiftIso n 0 n (by omega)).app M).symm

/-- If `X` is affine (`X ≅ Spec(A)`, `A = Γ(X, 𝒪_X)`), the structure sheaf is perfect
and generates the quasi-coherent derived category.
Source: Stacks Project, perfect.tex, Tags 06Z0 and 09IS
(blueprint: lem-pc-perfect-generation-affine-base).

Proof. Use the affine equivalence between the derived category of modules over `A`
and the quasi-coherent derived category of `X`; it sends `A[n]` to `𝒪_X[n]` and
preserves zero objects and Hom groups. The free rank-one module is strictly perfect,
and maps from its shifts detect all cohomology groups, hence detect zero objects.
Transport this criterion across the equivalence. -/
theorem perfectGeneration_affine_base (X : Scheme.{u}) [IsAffine X]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    schemeDerivedQCohProperty X
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace))) ∧
      Scheme.IsPerfect X
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace))) ∧
      ∀ E : schemeDerivedQCohCategory X,
        IsZero E.obj ↔
          ∀ n : ℤ,
            Subsingleton
              (((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
                (SheafOfModules.unit (moduleRings X.toRingedSpace)))⟦n⟧ ⟶ E.obj) := by
  classical
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let O := SheafOfModules.unit (moduleRings X.toRingedSpace)
  let S := (DerivedCategory.singleFunctor C 0).obj O
  refine ⟨?_, ?_, ?_⟩
  · intro n
    by_cases hn : n = 0
    · subst n
      exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app O).symm
        (by
          change O.IsQuasicoherent
          exact SheafOfModules.isQuasicoherent_unit (R := moduleRings X.toRingedSpace))
    · let K := (CochainComplex.singleFunctor C 0).obj O
      have hz : IsZero (K.homology n) := (K.sc n).isZero_homology_of_isZero_X₂
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 O n hn)
      have hz' : IsZero ((DerivedCategory.homologyFunctor C n).obj S) :=
        IsZero.of_iso hz ((DerivedCategory.homologyFunctorFactors C n).app K)
      have hzero : IsZero
          (SheafOfModules.free (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        apply (SheafOfModules.freeHomEquiv _).injective
        funext i
        exact PEmpty.elim i
      have : (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).ContainsZero :=
        ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free
          (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}⟩⟩
      exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_isZero hz'
  · intro x
    let U : X.Opens := ⊤
    let R := (moduleRings X.toRingedSpace).over U
    let K := (CochainComplex.singleFunctor (SheafOfModules.{u} R) 0).obj
      (SheafOfModules.unit R)
    refine ⟨U, by simp [U], K, ⟨?_, ?_⟩, ?_⟩
    · refine ⟨0, 0, fun n hn ↦ ?_⟩
      exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n (by omega)
    · intro n
      by_cases hn : n = 0
      · subst n
        let e : K.X 0 ≅ SheafOfModules.free (R := R) (ULift.{u} (Fin 1)) :=
          HomologicalComplex.singleObjXSelf (.up ℤ) 0 _ ≪≫
            (SheafOfModules.freeUniqueIso _).symm
        exact ⟨1, e.hom, e.inv, e.hom_inv_id⟩
      · have hz : IsZero (K.X n) :=
          HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn
        exact ⟨0, 0, 0, by simpa using hz.eq_of_src (0 : K.X n ⟶ K.X n) (𝟙 _)⟩
    · let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
      exact ⟨(F.mapDerivedCategorySingleFunctor 0).app O ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (Iso.refl _)⟩
  · intro E
    constructor
    · intro hE n
      exact ⟨fun f g ↦ hE.eq_of_tgt f g⟩
    · intro hE
      let A := Γ(X, ⊤)
      let Y := Spec (.of A)
      let CY := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
      let := HasDerivedCategory.standard CY
      let := HasDerivedCategory.standard (ModuleCat.{u} A)
      let s : X ≅ Y := X.isoSpec
      let a : C ≌ CY := CategoryTheory.Equivalence.mk
        (Scheme.Modules.restrictFunctor s.inv) (Scheme.Modules.restrictFunctor s.hom)
        ((Scheme.Modules.restrictFunctorId (X := X)).symm ≪≫
          Scheme.Modules.restrictFunctorCongr s.hom_inv_id.symm ≪≫
          Scheme.Modules.restrictFunctorComp s.hom s.inv)
        ((Scheme.Modules.restrictFunctorComp s.inv s.hom).symm ≪≫
          Scheme.Modules.restrictFunctorCongr s.inv_hom_id ≪≫
          Scheme.Modules.restrictFunctorId (X := Y))
      have : a.functor.Additive := Functor.additive_of_preserves_binary_products _
      have : a.inverse.Additive := Functor.additive_of_preserves_binary_products _
      let d := a.mapDerivedCategory
      have : d.functor.CommShift ℤ := by
        change a.functor.mapDerivedCategory.CommShift ℤ
        infer_instance
      let SY := (DerivedCategory.singleFunctor CY 0).obj
        (SheafOfModules.unit (moduleRings Y.toRingedSpace))
      let iS : d.functor.obj S ≅ SY :=
        (a.functor.mapDerivedCategorySingleFunctor 0).app O ≪≫
          (DerivedCategory.singleFunctor CY 0).mapIso (Scheme.Modules.restrictUnitIso s.inv)
      let E' : schemeDerivedQCohCategory Y := ⟨d.functor.obj E.obj, by
        intro n
        have : ((DerivedCategory.homologyFunctor C n).obj E.obj).IsQuasicoherent :=
          E.property n
        exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
          ((a.functor.mapDerivedCategoryHomologyFunctorIso n).app E.obj)
          (by
            change ((Scheme.Modules.restrictFunctor s.inv).obj
              ((DerivedCategory.homologyFunctor C n).obj E.obj)).IsQuasicoherent
            infer_instance)⟩
      have hSY (n : ℤ) : Subsingleton (SY⟦n⟧ ⟶ E'.obj) := by
        have : Subsingleton (S⟦n⟧ ⟶ E.obj) := hE n
        have : Subsingleton (d.functor.obj (S⟦n⟧) ⟶ E'.obj) :=
          (d.fullyFaithfulFunctor.homEquiv).symm.subsingleton
        let i : d.functor.obj (S⟦n⟧) ≅ SY⟦n⟧ :=
          (d.functor.commShiftIso n).app S ≪≫ (shiftFunctor _ n).mapIso iS
        exact (Iso.homCongr i (Iso.refl E'.obj)).symm.subsingleton
      obtain ⟨e, _, _, _, hs⟩ := exists_affineQCohDerivedEquivalence A
      let M := e.inverse.obj E'
      have hM : IsZero M := by
        apply freeModule_detects_zero A M
        intro n
        obtain ⟨i⟩ := hs n
        let j := (schemeDerivedQCohProperty Y).ι.mapIso (e.counitIso.app E')
        have hsrc : Subsingleton (SY⟦n⟧ ⟶ E'.obj) := hSY n
        have himg : Subsingleton (((e.functor ⋙ (schemeDerivedQCohProperty Y).ι).obj
            (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A A))⟦n⟧)) ⟶ (e.functor.obj M).obj) :=
          ⟨fun f g ↦ (Iso.homCongr i j).injective (hsrc.elim _ _)⟩
        have : Subsingleton (e.functor.obj
            (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A A))⟦n⟧) ⟶ e.functor.obj M) :=
          ⟨fun f g ↦ (schemeDerivedQCohProperty Y).ι.map_injective (himg.elim _ _)⟩
        exact e.fullyFaithfulFunctor.homEquiv.subsingleton
      have hz : IsZero E'.obj := IsZero.of_iso
        ((schemeDerivedQCohProperty Y).ι.map_isZero (e.functor.map_isZero hM))
        ((schemeDerivedQCohProperty Y).ι.mapIso (e.counitIso.app E')).symm
      exact IsZero.of_iso (d.inverse.map_isZero hz) (d.unitIso.app E.obj)

end AlgebraicGeometry
