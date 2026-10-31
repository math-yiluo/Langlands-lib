# Surjectivity on uniform generalized central-character spaces

Author: Worker 189. The operator-algebra construction is adapted from Worker
23's published `FiniteActionSpectrumProof`. The lifting design follows the
published statement by Workers 526 and 277, with guidance from Workers 8 and
359.

This internal algebra proof establishes the unchanged public proposition
`Langlands.GeneralizedCentralCharacterSurjectivityStatement.{uGroup,uSource,uTarget}`
as the complete closed type of
`Langlands.generalizedCentralCharacterSurjectivity`. The group, source and
target universes are independent. It uses the actual representations,
intertwiner, generalized subrepresentations and restricted map from
`Langlands.Representation.Exponents.Central`.

The source central operator span is a finite-dimensional commutative algebra
`B`. To construct it, restrict `ρ` to the full centre and let `S` be the span
of these operators in `Module.End ℂ V`. The identity comes from the central
element one. Two span inductions establish closure under composition and
commutativity: products of generators are the operator of their product,
and central elements commute. The resulting `S.toSubalgebra` is given this
commutative ring structure; the statement's sole finite-span hypothesis gives
`Module.Finite ℂ B`.

The proof uses only the topology-free lemmas of
`Langlands.Representation.Exponents.FiniteActionSpectrumProof`.
`finite_algHom` gives finitely many algebra characters.
`exists_decomposition` supplies a common natural exponent `N` and elements
`h φ` with unit sum `s`, satisfying `y * h φ = 0` for
`y ∈ (ker φ)^N`. Put `p φ = h φ * s⁻¹`. Then `∑ φ, p φ = 1` and
`y * p φ = (y * h φ) * s⁻¹ = 0`. The proof explicitly uses the inverse
of the supplied unit before asserting sum one.

For every vector `v`, the vector `p φ v` lies in the uniform generalized
central-character space for `z ↦ φ (ρ z)`. The exponent supplied by the
algebra works simultaneously for every central element. Every source vector
is the sum of these pieces.

The helper `GeneralizedCentralSurjectivity.preimage_stable` proves by span
induction that the inverse image under the given intertwiner of every target
subrepresentation is stable under `B`. For generators this is precisely
intertwining; linearity handles sums and scalar multiples. This includes
stability of the actual kernel by taking the zero target subrepresentation.
It also gives the required target generalized-space stability directly,
without supplying an independent action on the target. In quotient-action
terms, kernel stability makes the formula `b (f v) = f (b v)` independent
of the representative, and ambient surjectivity supplies representatives.
For a central generator its target operator is exactly the given `σ z`
by intertwining. Lean uses this formula through `preimage_stable` on the
chosen preimage rather than constructing a separate bundled target action.

Choose an ambient preimage `v` of a target generalized vector `w`. Each
`f (p φ v)` remains in the generalized space for the desired character by
the helper, and lies in that for the character induced by `φ` by preservation
of generalized spaces under intertwiners. If the characters differ, choose a
central element where they differ and use
`FiniteActionSpectrum.eq_zero_of_pow_sub_smul` to make this image zero.
The sum of the matching source pieces therefore maps to `w` and lies in the
desired source generalized space.

This proof imposes no topology, occurrence, carrier dimension or target-span
condition. It retains nilpotent directions and permits the preimage exponent
to exceed the target exponent. The same sums cover zero carriers and absent
characters. Orthogonal idempotence is not used. This module proves no
Jacquet, geometric, grouped-real-block or classification assertion.

The provenance is internal algebra. The inherited uniform generalized-space
convention is explained in the public `Central` Markdown with its Casselman
reference; this arbitrary-group surjectivity theorem is not presented as a
literal assertion from that literature. The proof reuses the published
finite-dimensional algebra results and adapts their span construction.
The theorem uses only `propext`, `Classical.choice` and `Quot.sound`.
