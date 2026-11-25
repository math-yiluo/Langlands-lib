/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative
public import WeilConjectures.AlgebraicGeometry.Affine.AffineResidueModelNaturality
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFiberCohomologyFunctor

/-! # Choice of an affine residue representative

This is the per-index choice step in the geometric residue comparison.

## References

* Stacks Project, Tags 08CR and 01IB
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A chain representative of the restricted arrow `b` exists, and the canonical affine
residue comparisons intertwine its residue cycle homology map with the derived fibre
cohomology map of `b`. -/
theorem picard_residue_homology_choose_model_map
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (w : W) (U : W.Opens) (hU : IsAffineOpen U)
    (hwU : w ∈ U) (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    {E E' : schemeDerivedCategory W} (b : E ⟶ E')
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (hK : IsStrictlyPerfect W U K) (hC : IsStrictlyPerfect W U C)
    (m : (SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)
    (m' : (SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E' ≅
        DerivedCategory.Q.obj C) :
    ∃ φ : K ⟶ C, DerivedCategory.Q.map φ = m.inv ≫
        (SheafOfModules.overFunctor.{v}
          (moduleRings W.toRingedSpace) U).mapDerivedCategory.map b ≫ m'.hom ∧
      ∀ z, affineResidueModelEquiv W w U hwU hU p hp E' C hC m'
          (affineResidueCycleHomologyMap φ z) =
        (derivedFiberCohomologyFunctor W w 1).map b
          (affineResidueModelEquiv W w U hwU hU p hp E K hK m z) := by
  obtain ⟨φ, hφ⟩ := perfect_affine_map_representative W U hU K C hK hC
    (m.inv ≫
      (SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.map b ≫ m'.hom)
  exact ⟨φ, hφ, affineResidueModelEquiv_naturality W w U hwU hU p hp b hK hC m m' φ hφ⟩

end AlgebraicGeometry.Scheme
