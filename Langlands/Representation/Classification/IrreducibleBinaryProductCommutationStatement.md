# Actual commutation of an irreducible binary normalized product

Author: Worker 78.

`Langlands.Classification.IrreducibleBinaryProductCommutation.{uF,uV} F T`
is an internal derived proposition, for any prime-certified `p`, finite p-adic
field `F`, and the supplied compatible topological data `T`. The field and
carrier universes remain independent. Both actual factor carriers are in
`max uF uV`.

For positive ranks `a` and `b`, it takes actual irreducible smooth complex
representations `α` of `GL_a(F)` and `β` of `GL_b(F)`, and assumes that their
actual upper normalized binary product is irreducible. It concludes an actual
smooth isomorphism from that product to the product in reversed order,
transported from `GL_(b+a)(F)` to `GL_(a+b)(F)` by
`Derivative.generalLinearRankCast T (Nat.add_comm b a)`. The ranks may differ.
The binary functor uses the residue-normalized upper-parabolic half modulus
specified by `T`; no semisimplification is taken.

The planned derivation generalizes the published equal-rank construction
`Langlands.Classification.irreducibleTwoFactorProductSwap`: inverse transpose
reverses the ordered blocks, Gelfand–Kazhdan identifies inverse-transpose
pullbacks of each irreducible factor and of the irreducible original product
with their smooth duals, and normalized induction commutes with the smooth
dual for admissible factors. Pulling back twice returns the original action.
Identifying the reversed binary shape with the total-rank cast gives the
literal endpoint stated here. Admissibility follows from independently
proved irreducible smooth admissibility. This is internal provenance from
those Library results; it supplies neither a proof nor unconditional binary
irreducibility, finite grouping, integral-line support, or classification.
