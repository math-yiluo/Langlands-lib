/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectFiniteFreeResidueModelData
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectFiniteFreeResidueModelExistence

/-! # Finite free local models with prescribed residue cohomology ranks

The derived fibre is `derivedPullback (X.fromSpecResidueField x)`; its degree-`i`
cohomology vector space over `κ(x)` is `derivedFiberCohomology X E i x` and its dimension
`d_i` is `derivedFiberBetti X E i x`.

## References

* Stacks Project, More on Algebra, Lemma lift-perfect-from-residue-field, Tag 0BCD
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

noncomputable section

/-- Every perfect complex has an affine local bounded finite free model whose degreewise
ranks equal its derived fibre cohomology dimensions at the prescribed point. -/
theorem exists_finiteFreeResidueModel
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : IsPerfect X E) (x : X) :
    (∀ i : ℤ, Module.Finite (X.residueField x) (derivedFiberCohomology X E i x)) ∧
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → derivedFiberBetti X E i x = 0) ∧
      ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
        ∃ K : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
          (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)) ∧
          (∀ i : ℤ, Nonempty (K.X i ≅ SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over U)
            (ULift.{u} (Fin (derivedFiberBetti X E i x))))) ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅
            DerivedCategory.Q.obj K) := by
  obtain ⟨hfin, hbound⟩ := finiteFiberData X E x (hE x)
  obtain ⟨U, hxU, hUaff, K, hKb, hKrank, hKE⟩ :=
    finiteFreeModel_of_fiberData X E x (hE x) hfin hbound
  exact ⟨hfin, hbound, U, hxU, hUaff, K, hKb, hKrank, hKE⟩

end
end AlgebraicGeometry.Scheme
