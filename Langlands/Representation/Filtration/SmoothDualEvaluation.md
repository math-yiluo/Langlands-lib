# Covariant evaluation against the ambient smooth dual

This internal construction packages evaluation as an actual element of
`Langlands.InvariantBilinear.forms`. For a representation `ρ` over a field and
a unit-valued character `χ`, `smoothDualEvaluation ρ χ` is the bilinear map
`B(v, ℓ) = ℓ(v)`, with the ordinary action on `v` and the `χ` twist of the
smooth contragredient action on `ℓ`. Its simultaneous covariance is `χ(g)`.
The construction does not require smoothness of `ρ`, an open character kernel,
or any topology on its carrier. If a bundled smooth twisted representation is
needed, its smoothness remains a separate obligation.

`comapGroup` pulls back both actions and the covariance function along a monoid
homomorphism. It preserves the carriers and the bilinear map exactly, and
therefore preserves separation on the left. In particular, restriction to a
subgroup keeps the smooth dual of the ambient representation as its second
carrier. It does not replace that carrier with the smooth dual formed after
restriction.

`comapLeft_separatingLeft` proves that pullback in the first variable along an
injective intertwiner preserves separation on the left. If a vector pairs to
zero with every second argument, separation kills its image, and injectivity
kills the vector. `comapLeft_ne_zero_of_separatingLeft` then proves nonvanishing
when the source carrier is nontrivial. These claims concern arbitrary
representations and do not require irreducibility or finite length.

For a smooth complex representation of a topological group with cofinal
compact open subgroups, `smoothDualEvaluation_separatingLeft` follows from the
published injectivity of `Langlands.smoothBidual`: vanishing against every
smooth functional makes the canonical bidual image zero. Admissibility is
not assumed. All group and carrier universes remain independent.

The provenance is internal and derived. The covariance proof uses the
published `smoothDualPairing_invariant` law and linearity in the functional.
The separation proof uses
`smoothBidual_injective_of_compact_cofinal` from
`Smooth.Contragredient.AdmissibleDualityProof`. The remaining proofs are
elementary pullback arguments over the existing actual form, representation,
and intertwiner definitions. No derivative, segment, classification,
induction, or irreducibility theorem is used or asserted.

The four direct project imports have a 20-module transitive project closure.
Every imported Lean/Markdown pair matches Library commit
`8c73c345a56c4d23f7e0056f0f55e31cebda2513` byte for byte. That closure
contains no derivative or classification module. This construction therefore
uses none of the excluded segment, classification, exhaustion or two-factor
irreducibility conclusions. This bounded construction audit does not certify
the dependency closure of a future consumer.
