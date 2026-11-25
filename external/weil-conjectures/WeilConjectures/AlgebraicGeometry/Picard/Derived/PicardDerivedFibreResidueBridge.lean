/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFiberCohomologyFunctor
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedCoefficientMap
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedFibreResidueModelData
import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedFibreResidueBridgeCore
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.AlgebraicGeometry.Affine.AffineResidueModelNaturality

/-! A common affine residue model bridge for the derived fibre comparison.

This is the model-selection part of the proof of
`picard_derived_fibre_naturality`; its output is deliberately stated before
the geometric cohomology comparisons.

## References

* Stacks Project, Tags 01IB, 064K, 06YJ and 0B91
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
set_option linter.style.haveILetI false in
/-- Choose common affine residue models and representatives for the finite family. -/
theorem picard_derived_fibre_residue_bridge
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)]
    [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    let Ei := fun i ↦ (schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))
    ∃ (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
        (p : Ideal Γ(W, U)) (hprime : p.IsPrime)
        (hpEq : p = RingHom.ker (W.evaluation U w hwU).hom)
        (K : CochainComplex
          (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
        (C : Fin n → CochainComplex
          (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
        (hK : IsStrictlyPerfect W U K) (hC : ∀ i, IsStrictlyPerfect W U (C i))
        (m : (SheafOfModules.overFunctor.{v}
          (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
            DerivedCategory.Q.obj K)
        (m' : ∀ i, (SheafOfModules.overFunctor.{v}
          (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj (Ei i) ≅
            DerivedCategory.Q.obj (C i))
        (φ : ∀ i, K ⟶ C i)
        (e : derivedFiberCohomology W E 1 w ≃+
          Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
        (ei : ∀ i, derivedFiberCohomology W (Ei i) 1 w ≃+
          Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1),
        letI := hprime
        ∀ i, DerivedCategory.Q.map (φ i) = m.inv ≫ (SheafOfModules.overFunctor.{v}
            (moduleRings W.toRingedSpace) U).mapDerivedCategory.map
              (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) ≫ (m' i).hom ∧
          (∀ z, ei i ((derivedFiberCohomologyFunctor W w 1).map
            (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) z) =
            structureSheafCohomologyPullback
              (((Over.pullback (S.fromSpecResidueField s)).map
                (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                  (ui i) (hui i))).left) 1 (e z)) ∧
          ∀ z, ((affineResidueModelEquiv W w U hwU hU p hpEq _ (C i) (hC i) (m' i)).trans
              (ei i)) (affineResidueCycleHomologyMap (φ i) z) =
            structureSheafCohomologyPullback
              (((Over.pullback (S.fromSpecResidueField s)).map
                (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                  (ui i) (hui i))).left) 1
              ((affineResidueModelEquiv W w U hwU hU p hpEq _ K hK m).trans e z) := by
  classical
  exact (picard_derived_fibre_residue_model_data f Xi fi ui hui L W k w s hw τ).elim
    fun U h ↦ h.elim fun hwU h ↦ h.2.elim fun p h' ↦ h'.elim fun hp h' ↦
      h'.elim fun hpEq h' ↦ h'.elim fun K h' ↦ h'.elim fun C h' ↦ by
        letI : p.IsPrime := hp
        exact ⟨U, hwU, h.1, p, hp, hpEq, K, C, h'.1, h'.2.1,
          h'.2.2.1.some, fun i ↦ (h'.2.2.2 i).some,
          picard_derived_fibre_residue_bridge_core f Xi fi ui hui L W k w s hw τ
            U hwU h.1 p hpEq K C h'.1 h'.2.1 h'.2.2.1.some
            (fun i ↦ (h'.2.2.2 i).some)⟩

end AlgebraicGeometry.Scheme
