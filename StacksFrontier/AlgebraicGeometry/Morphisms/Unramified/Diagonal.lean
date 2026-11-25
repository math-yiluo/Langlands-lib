module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The diagonal of an unramified morphism

The diagonal of an unramified morphism of schemes is an open immersion. Conversely, a morphism
with open diagonal is unramified as soon as it is locally of finite type, and G-unramified as
soon as it is locally of finite presentation.

## Main results

* `AlgebraicGeometry.Unramified.isOpenImmersion_diagonal`: the diagonal of an unramified
  morphism is an open immersion.
* `AlgebraicGeometry.Unramified.of_isOpenImmersion_diagonal`: the converse under local finite
  type.
* `AlgebraicGeometry.GUnramified.of_isOpenImmersion_diagonal`: the converse under local finite
  presentation.
* `AlgebraicGeometry.Etale.of_comp_of_unramified`: a morphism from a scheme étale over `S` to a
  scheme unramified over `S` is étale.

## References

* [Stacks Project, Tag 02GE](https://stacks.math.columbia.edu/tag/02GE)
* [Stacks Project, Tag 0HB1](https://stacks.math.columbia.edu/tag/0HB1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Unramified

/-- The diagonal of an unramified morphism is an open immersion. -/
@[stacks 02GE "part (1)"]
public instance isOpenImmersion_diagonal {X S : Scheme.{u}} (f : X ⟶ S) [Unramified f] :
    IsOpenImmersion (pullback.diagonal f) := by
  let h := (unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mp inferInstance
  have := h.1; have := h.2; infer_instance

end Unramified

namespace GUnramified

end GUnramified

end AlgebraicGeometry

end
