# Ordinary-unit recognition for principal ideles

The theorem `Langlands.ClassField.Global.principalIdeleUnitCriterion` proves
`PrincipalIdeleUnitCriterion.{u}` for every number field in arbitrary universe
`u`. For an actual field unit `a : Eˣ`, its principal idele has valuation one
at every finite place if and only if it is the image of a unit of `𝓞 E`.
No extension or Galois hypothesis is used.

The private helper `principalCompletionValuation` identifies the valuation of
the canonical image in a finite completion with the corresponding field
valuation. The forward direction uses `ideleCoordinate_unitEmbedding` to
transfer the hypothesis to field valuations. Mathlib's
`mem_integers_of_valuation_le_one` is applied to `a` and its inverse, since
both have valuation one at every finite place. This produces ring integers
`x` and `y` with those images. Injectivity of the ring-integer inclusion shows
`x * y = 1`; commutativity gives the reverse product, so they define a unit
whose image is `a`.

Conversely, `Valuation.Integers.one_of_isUnit'` applied to an ordinary unit,
together with `HeightOneSpectrum.valuation_le_one` on ring integers, shows
its field valuation is one. The same completion comparison then proves the
required condition on the principal idele. The proof uses the actual
ring-integer unit map and the published principal-idele coordinates.

This implements the unit recognition stated in Milne, *Class Field Theory*
v4.03, Chapter V, Aside 4.5, the first claim of footnote 12, printed p.171
(PDF180); registered source `milne-2020-class-field-theory`, SHA256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.
The direct Lean proof uses Mathlib valuation and integrality lemmas.
No topology, finite-index, exact-sequence or cohomology assertion is proved here.

Worker 343 supplied the complete Lean proof and its proof description in the
shared draft. Worker 54 checked the exact target and imported lemmas, verified
the source locator, and prepared this contribution for independent review.
