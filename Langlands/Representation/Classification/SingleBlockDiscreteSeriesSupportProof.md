# Single-block unitary cuspidal support on the original GL carrier

Author: Worker 320.

`Langlands.glSingleBlockDiscreteSeriesSupport` proves the unchanged
`Langlands.GLSingleBlockDiscreteSeriesSupportStatement.{uF,uV}` from
[`SingleBlockDiscreteSeriesSupportStatement`](SingleBlockDiscreteSeriesSupportStatement.md).
It is a derived specialization of the published product-Levi theorem
`glDiscreteSeriesPositiveRootSupport`. It retains arbitrary primes, fields,
supplied topologies, positive ranks, every single-block shape, and independent
field and original-carrier universes.

The supporting theorem
`PadicField.TopologicalData.isLeviSquareIntegrable_singleBlock_iff` proves
that the original analytic `T.IsSquareIntegrable ρ` is equivalent to
`IsLeviSquareIntegrable T C (Rep.of (ρ.comp (C.leviEmbedding F.Carrier)))`
for any shape `C` of length one. The actual continuous equivalence
`C.singleBlockLeviEquivContinuous hC F.Carrier` has forward map equal to
that embedding. Its induced `centralQuotientCongr` is an equivalence of the
actual groups modulo their full centers.

For the GL-to-Levi transport, take any Borel structure and Haar measure `μ`
on the single-block Levi quotient. Push `μ` forward through the central
quotient equivalence, apply the original all-Haar hypothesis, and use
`isSquareIntegrableModCenter_comp_continuousMulEquiv`. This transports
admissibility, the genuine unitary central character, and every `L²`
coefficient bound. For the Levi-to-GL transport, give the Levi quotient its
Borel measurable structure, push any supplied GL Haar measure through the
inverse central quotient equivalence, and apply the same transport theorem
in reverse. Pullback followed by inverse pullback is the original action,
as checked by the actual group equivalence's inverse identity. No chosen
replacement carrier, central-strip comparison, or fixed Haar normalization
is introduced.

For the main theorem, pull irreducibility back through the same single-block
multiplicative equivalence using `isIrreducible_comp_mulEquiv_iff`. The helper
supplies precisely the full-center analytic hypothesis of
`glDiscreteSeriesPositiveRootSupport`. That proved theorem supplies the
refinement `R`, unitary irreducible cuspidal datum `ω`, strict root parameter
`t`, and a surjective intertwiner `q` onto the single-block pullback of `ρ`.
All this data is reused without alteration.

The final map `q'` has exactly the linear map of `q`. Its source GL action
is the refined induced action pulled back along the inverse constructed
single-block equivalence `e`. The intertwining equation for `q` at
`e.symm g` becomes the equation for `q'` at `g`, since
`e (e.symm g) = g`. Surjectivity is the same hypothesis `hq` on that
unchanged linear map. In particular, the codomain is the original `ρ` on
`V : Type uV`, while the inducing and induced carriers remain in
`Type (max uF uV)`.

The source retains the negative determinant parameter, coarse parameter
zero, upper refined parabolic, positive half modulus, and right translation
from the product-Levi theorem. This proof uses its verified support and
strict-cone results and existing group and coefficient transports. It uses
no multisegment exhaustion, strong-head coverage, tempered block uniqueness,
square-integrable Langlands classification, regular exhaustion, or parent
classification conclusion. It proves no single-segment progression or
strong-head assertion. Its provenance is the explicit internal transport
above, with no additional original-literature claim.
