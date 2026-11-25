/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedCoefficientMap
public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFiberCohomologyFunctor
public import WeilConjectures.AlgebraicGeometry.Affine.AffineResidueModelNaturality
import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueHomologyChosenMap

/-! Affine residue data for the fixed-model bridge.

## Implementation details

Apply the affine residue model naturality theorem to the coefficient
arrow and choose a chain representative by the affine perfect map theorem.
Compose the residue-to-derived-fibre comparisons with the geometric residue
comparisons.  Naturality of the geometric residue comparison gives the two
required equations simultaneously for every index.

## References

* Stacks Project, Tags 01IB, 064K, 06YJ and 0B91
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- The fixed-model naturality traverses derived and residue comparisons.
/-- Fixed affine-model residue naturality data for a finite family. -/
theorem picard_derived_fibre_residue_affine_data
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
    (L : X.Modules) [Modules.IsInvertible L]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (_hw : k w = s)
    (_τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (m : ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅ DerivedCategory.Q.obj K))
    (m' : ∀ i, ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i))) :
    ∃ φ : ∀ i, K ⟶ C i, ∀ i,
      DerivedCategory.Q.map (φ i) = m.inv ≫ (SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.map
          (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) ≫ (m' i).hom ∧
      ∀ z, affineResidueModelEquiv W w U hwU hU p hp _ (C i) (hC i) (m' i)
          (affineResidueCycleHomologyMap (φ i) z) =
        (derivedFiberCohomologyFunctor W w 1).map
          (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k)
          (affineResidueModelEquiv W w U hwU hU p hp _ K hK m z) := by
  choose φ hφ using fun i ↦ picard_residue_homology_choose_model_map W w U hU hwU p hp
    (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) hK (hC i) m (m' i)
  exact ⟨φ, hφ⟩

end AlgebraicGeometry.Scheme
