import Langlands.Representation.Conductor.OrderedUnramifiedWhittakerAssembly
import Langlands.AllFieldBZ.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof

/-!
# The normalized inverse Whittaker realization of ordered unramified principal series

For every nonarchimedean local field `F`, every tuple `z` of nonzero complex parameters with
weakly increasing norms and every unitary additive character `ψ` of integer conductor, the
unramified principal series `I(z)` has a nonzero `ψ⁻¹`-Whittaker functional whose coefficient
map is injective, normalized so that the spherical section goes to the explicit spherical
Whittaker function.

The proof is `OrderedUnramifiedWhittakerAssembly.realization_of_h411`, applied to
Bernstein–Zelevinsky's Theorem 4.11 over all nonarchimedean local fields
(`AllFieldBZ.Derivative.orderedCuspidalProductNoDegenerateSubmodules`).
-/

namespace Langlands.Conductor

universe uF

/-- **Normalized inverse Whittaker realization** (Jacquet 2012, Lemma 2 and the
spherical-image comparison) for norm-ordered unramified principal series over every
nonarchimedean local field. -/
theorem orderedUnramifiedWhittakerRealization :
    OrderedUnramifiedWhittakerRealizationStatement.{uF} :=
  OrderedUnramifiedWhittakerAssembly.realization_of_h411 fun P T =>
    AllFieldBZ.Derivative.orderedCuspidalProductNoDegenerateSubmodules.{uF, uF} P T

end Langlands.Conductor
