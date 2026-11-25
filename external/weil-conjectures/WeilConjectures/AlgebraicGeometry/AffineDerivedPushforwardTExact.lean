/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.AffineDerivedCohomology
import WeilConjectures.AlgebraicGeometry.AffineDerivedPushforwardConservative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Affine derived direct image preserves and reflects standard cohomological bounds

Source: Stacks Project, Derived Categories of Schemes, Tags 0AVW and 08I8
(blueprint: lem-sc-affine-derived-pushforward-t-exact).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

private theorem qc_single {X : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (hM : M.IsQuasicoherent) :
    schemeDerivedQCohProperty X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  have hzero : Limits.IsZero
      (SheafOfModules.free (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}) := by
    apply (Limits.IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free PEmpty.{u + 1}⟩⟩
  intro i
  by_cases hi : i = 0
  · subst i
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · apply (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_isZero
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE _ 0 i hi
    · exact DerivedCategory.isZero_of_isLE _ 0 i hi

private theorem affine_reflects_module_zero {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [IsAffineHom f]
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (hM : M.IsQuasicoherent)
    (hz : Limits.IsZero ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj M)) :
    Limits.IsZero M := by
  let S := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
  have hS : schemeDerivedQCohProperty X S := qc_single M hM
  have hR : Limits.IsZero ((schemeDerivedDirectImage f).obj S) := by
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro i
    obtain ⟨⟨e⟩, _⟩ := schemeHigherDirectImage_of_affine f S hS i
    apply Limits.IsZero.of_iso _ e
    by_cases hi : i = 0
    · subst i
      exact hz.of_iso ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M))
    · apply (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).map_isZero
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE S 0 i hi
      · exact DerivedCategory.isZero_of_isLE S 0 i hi
  have : IsIso ((schemeDerivedDirectImage f).map (0 : S ⟶ S)) := hR.isIso hR _
  have : IsIso (0 : S ⟶ S) := schemeDerivedDirectImage_isIso_of_affine f hS hS _
  have hSz : Limits.IsZero S := Limits.IsZero.of_mono_zero S S
  exact ((DerivedCategory.homologyFunctor _ 0).map_isZero hSz).of_iso
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm

/-- Affine derived direct image takes quasi-coherent cohomology to quasi-coherent cohomology,
preserves and reflects both bounds of the standard t-structure, and reflects isomorphisms
between objects with quasi-coherent cohomology.
Source: Stacks Project, Tags 0AVW and 08I8
(blueprint: lem-sc-affine-derived-pushforward-t-exact).

Proof:
1. The affine cohomology comparison `lem-sc-affine-derived-cohomology` identifies
   H^i(Rf_*E) with f_*H^i(E), which is quasi-coherent, for every integer i.
2. This comparison preserves cohomology vanishing above or below every integer n.
   Conversely, if f_*H^i(E) vanishes, apply the same comparison to H^i(E)[0]:
   its derived direct image has zero cohomology in every degree. Its zero map to
   zero therefore has invertible derived direct image, and
   `lem-sc-affine-derived-pushforward-conservative` makes that map invertible.
   Thus H^i(E) vanishes. The descriptions of the standard t-structure in
   `def-sbc-standard-tstructure-derived-category` give both bound equivalences.
3. For a morphism between two objects with quasi-coherent cohomology, apply
   `lem-sc-affine-derived-pushforward-conservative` to reflect invertibility. -/
theorem schemeDerivedDirectImage_tExact_and_conservative_of_affine
    {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [IsAffineHom f] :
    (∀ E : schemeDerivedCategory X, schemeDerivedQCohProperty X E →
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E) ∧
      ∀ n : ℤ,
        (DerivedCategory.IsLE E n ↔
          DerivedCategory.IsLE ((schemeDerivedDirectImage f).obj E) n) ∧
        (DerivedCategory.IsGE E n ↔
          DerivedCategory.IsGE ((schemeDerivedDirectImage f).obj E) n)) ∧
    (∀ (E F : schemeDerivedCategory X),
      schemeDerivedQCohProperty X E → schemeDerivedQCohProperty X F →
      ∀ a : E ⟶ F, IsIso ((schemeDerivedDirectImage f).map a) → IsIso a) := by
  constructor
  · intro E hE
    have hvanish : ∀ i : ℤ,
        Limits.IsZero ((DerivedCategory.homologyFunctor _ i).obj E) ↔
        Limits.IsZero ((DerivedCategory.homologyFunctor _ i).obj
          ((schemeDerivedDirectImage f).obj E)) := by
      intro i
      obtain ⟨⟨e⟩, _⟩ := schemeHigherDirectImage_of_affine f E hE i
      constructor
      · intro hz
        exact ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).map_isZero hz).of_iso e
      · intro hz
        exact affine_reflects_module_zero f _ (hE i) (hz.of_iso e.symm)
    refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨⟨e⟩, hq⟩ := schemeHigherDirectImage_of_affine f E hE i
      exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
        e.symm hq
    · intro n
      constructor
      · simp only [DerivedCategory.isLE_iff, ← hvanish]
      · simp only [DerivedCategory.isGE_iff, ← hvanish]
  · intro E F hE hF a ha
    let := ha
    exact schemeDerivedDirectImage_isIso_of_affine f hE hF a

end AlgebraicGeometry
