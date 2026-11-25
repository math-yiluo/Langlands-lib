/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectFiniteResidueCohomologyFinite
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectFiniteResidueCohomologyBounded

/-! # Finite fibre data of a strictly perfect neighbourhood

## References

* Stacks Project, More on Algebra, Tag 0BCD
* Stacks Project, Cohomology of Sheaves, Tag 08C4 (strictly perfect complexes)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- A strictly perfect neighbourhood of a point gives finite-dimensional derived fibre
cohomology, supported in a bounded interval. -/
theorem finiteFiberData
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (x : X)
    (hlocal : ∃ V : X.Opens, x ∈ V ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        IsStrictlyPerfect X V P ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj P)) :
    (∀ i : ℤ, Module.Finite (X.residueField x) (derivedFiberCohomology X E i x)) ∧
      ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → derivedFiberBetti X E i x = 0 := by
  exact ⟨finiteFiberCohomology X E x hlocal,
    finiteFiberCohomologyBounded X E x hlocal⟩

end
end AlgebraicGeometry.Scheme
