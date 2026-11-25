/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralUnitReduction
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Normalized.NormalizedKummerTarget

/-! # Integral quotient reduction with its two normalized comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Simultaneous integral reduction identifies the integer source and Kummer target,
with the integer generator and the positive boundary fixing the two comparisons.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2);
the expanded proof in `SmoothPurityTowerClasses`, steps 3--7.
(blueprint: lem-sfb-normalized-kummer-reduction).

Proof: view abelian towers as integer modules on the inverse-system topos. Forget
quotient coefficients on that topos, and take the left adjoint given by tensoring
with the actual quotient ring system. Apply the K-flat derived change-of-rings
construction to obtain Reduction, retaining its ordinary and derived adjunctions
and the representative transpose formula. The integer unit is flat, so the
universal counit identifies its reduction with the quotient unit; multiplication
fixes this comparison's adjunct to integerGenerator. Compute reduction of the
constant units tower using the bounded flat resolution whose nth term is
[Z --l^(n+1)--> Z] in degrees -1 and 0 and whose transition is (l,1).
Kummer exactness identifies the sole cohomology of the resulting two-term units
complex with the actual roots tower, with power-l transitions. Its quotient
coefficient action is the unique action on the annihilated group. Canonical
truncation inside the quotient-module derived category supplies M, its
underlying-root isomorphism i, and the shifted comparison b. Fix the sign by the
positive kernel inclusion. If the Kummer complex is [U -> V] with augmentation
v and cone projection p, its boundary is -p v^{-1}. The homotopy with sole
nonzero component 1_V identifies the positive kernel model's tensor-unit map
with this boundary. Shift once and use shiftFunctorAdd to obtain exactly the
displayed targetNormalization equation. This calculation is on entire systems;
it does not deduce equality of derived arrows from their finite evaluations.
On the empty scheme the same constructions and universal properties apply.
The exponent n+1 is positive even when n=0, and no division by 2 occurs. -/
theorem exists_normalizedKummerReduction (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (k : Kummer l T) :
    (fun R : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} ↦
    ∃ (r : Reduction T R) (M : Systems T R)
      (i : r.forget.F.obj M ≅ roots l T)
      (a : r.derived.obj ((DerivedCategory.singleFunctor (Ab T) 0).obj (integers T)) ≅
        unit T R)
      (b : r.derived.obj (((DerivedCategory.singleFunctor (Ab T) 0).obj
        (units T))⟦(1 : ℤ)⟧) ≅
        ((DerivedCategory.singleFunctor (Systems T R) 0).obj M)⟦(2 : ℤ)⟧),
      r.model.sourceNormalization a (integerGenerator T R r.forget) ∧
      r.model.targetNormalization (ShortComplex.mk k.inclusion k.power k.zero)
        k.exact b i) (Rrings l T) := by
  obtain ⟨r, a, ha⟩ := exists_integralUnitReduction T (Rrings l T)
  obtain ⟨M, i, b, hb⟩ := exists_normalizedKummerTarget l T hT k r
  exact ⟨r, M, i, a, b, ha, hb⟩

end AlgebraicGeometry.ProEtale.SpTowerClasses
