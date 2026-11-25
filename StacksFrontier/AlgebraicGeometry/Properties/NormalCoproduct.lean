module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.Normal

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Normal locally Noetherian schemes as disjoint unions

A locally Noetherian scheme is normal exactly when it is a disjoint union of normal integral
schemes, and a Noetherian scheme is normal exactly when it is a *finite* such disjoint union.

## Main results

* `AlgebraicGeometry.isNormal_iff_exists_iso_coproduct_integral_normal` characterizes normal
  locally Noetherian schemes as coproducts of normal integral schemes.
* `AlgebraicGeometry.isNormal_iff_exists_iso_finite_coproduct_integral_normal` characterizes
  normal Noetherian schemes as finite coproducts of normal integral schemes.

## Implementation notes

A disjoint union is represented by an isomorphism with the categorical coproduct of a family of
schemes; the index type may be empty, as required for the empty scheme, and is required to be
finite only in the Noetherian case.

## References

* [Stacks Project, Tag 033M](https://stacks.math.columbia.edu/tag/033M)
* [Stacks Project, Tag 033N](https://stacks.math.columbia.edu/tag/033N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A locally Noetherian scheme is normal if and only if it is isomorphic to a coproduct of normal
integral schemes. -/
@[stacks 033N]
public theorem isNormal_iff_exists_iso_coproduct_integral_normal
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsNormal X ↔
      ∃ (ι : Type u) (Y : ι → Scheme.{u})
          (_ : ∀ i, IsNormal (Y i)) (_ : ∀ i, IsIntegral (Y i)),
        Nonempty (X ≅ ∐ Y) :=
  isNormal_iff_exists_iso_coproduct (X := X) (finite_irreducibleComponents_of_isCompact X)

end AlgebraicGeometry

end
