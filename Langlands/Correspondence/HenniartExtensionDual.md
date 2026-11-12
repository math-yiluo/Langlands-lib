# Contragredients and the extended stable map

Author: Worker 4803. Module `Langlands.Correspondence.HenniartExtensionDual`.

Henniart (2000), §4.3 ("π(σ)^∨ = π(σ^∨) ... découle aussi de 3.8"), extended by
unramified twists as in §4.4.

## Weil-side lemmas

`Weil.dualBasisEquiv_twistBasisEquiv` (namespace
`Langlands.VirtualRepresentation.Weil`): the dual of the twist of an irreducible
class by `χ` is the twist of its dual by `χ⁻¹`. Classes of equal rank with equal
underlying classes are equal (`IrreducibleBasis.ext_underlyingClass`, published).
On representatives the two representations agree by the published
`Langlands.dual_twist`, so the identity is an equivalence.

`Weil.factorsThrough_dualBasisEquiv`: the dual of a class factoring through
`f : G →* H` via `A` factors through `f` via the dual of `A`. The two
representations agree because `f (g⁻¹) = (f g)⁻¹`.

## Stable images of duals

`generator_unitaryDual_mem` (namespace `Langlands.Henniart.Extension`): the dual
of a unitary class factoring through a finite quotient `q` factors through `q`.

`IsStableImage.dual`: if the generator of `π` is a stable image of `b`, then
the generator of the contragredient of `π` is a stable image of the dual of `b`,
at the same quotient. Take any candidate `Φ` at that quotient. The dual clause of
3.8 (`LatticeMap.DualCompatibility`) sends the dual of the generator of `b` to
the contragredient of `Φ` of the generator of `b`, which is the generator of `π`.
The published generator lemmas `unitaryDualLatticeEquiv_generator` and
`unitaryContragredientLatticeEquiv_generator` finish the proof.

## Compatibility

`extensionBasis_dual`: the extension commutes with duals on bases. For a stable
decomposition `b = z b₀` with image `π₀`, the dual `b^∨ = z⁻¹ b₀^∨` has the
stable decomposition `(z⁻¹, b₀^∨, π₀^∨)`. The published
`contragredientBasisEquiv_unramifiedTwist` gives `(z π₀)^∨ = z⁻¹ π₀^∨`.

`extensionMap_dual`: the published `SupercuspidalDualCompatibility`, through the
published `supercuspidalDualCompatibility_iff` and `sigma_extensionMap`.
