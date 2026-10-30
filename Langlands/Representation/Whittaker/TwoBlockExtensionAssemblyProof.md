# Conditional proof of the full JPSS extension formula

The theorem `twoBlockWhittakerExtension_of_rowFourierSurjectivity` proves the
published internal proposition `TwoBlockExtensionAssemblyStatement`. Its
conclusion is the unchanged `TwoBlockWhittakerExtensionStatement`, conditional
on the family of row Fourier surjectivity propositions for canonical p-adic
topologies and all row dimensions. It does not prove that family or the unconditional parent
statement.

The determinant helper expands the two-block modulus at the actual Levi
element `(I_A,g)`, where `A=a+1` and `B=b+1`. Its full modulus is the inverse
of `|det g|^A`. The positive square root of that value, multiplied by the
rectangular Jacobian `|det g|^A`, equals `|det g|^(A/2)`. Positivity follows
from the invertible matrix's nonzero determinant. The real calculation
rewrites square roots and natural powers as real powers and adds their
exponents; `Real.coe_sqrt` passes from nonnegative reals to reals.

An entrywise helper compares the iterated `appendIdentity` embedding with
the literal `blockSum (g,1)`, after the respective equality-of-rank reindices.
It splits both indices into the two blocks and uses the published entry
laws. The resulting `twoBlockLeadingEmbedding_eq` identifies precisely the
parent target's embedding and the one in the scalar coefficient formula.

The first factor's Whittaker-type hypothesis gives an equivalence from its
functional space to the complex numbers. The inverse image of one is a
nonzero functional. A nonzero linear functional to the scalar field is
surjective, so it has a vector with value one. The given second Whittaker
coefficient supplies its functional and vector through actual coefficient
range membership.

The representations are the exact literal conjugations on
`ULift.{uV₂} V₁` and `ULift.{uV₁} V₂` required by the parent. Smoothness
transports through `isSmooth_literalULift_iff`; the corresponding literal
representation equivalences transport both standard functionals by
`Whittaker.functionalsCongr`, with the vectors lifted by `ULift.up`.
Evaluation therefore retains value one in the first factor and the specified
second coefficient at every `g`.

Choose a normalized additive Haar measure on any positive compact subset of
the canonical field. The conditional matrix Fourier slice supplies a
rectangular Schwartz–Bruhat function whose twisted integral is
`|det g|^A Φ(lastRow g)`. Apply the scalar pure-tensor coefficient theorem to
these lifted factors, functionals and vectors and that rectangular function.
It constructs an actual coefficient in the target's intrinsic Whittaker
set. Substitution of the slice, the two functional evaluations, the leading
embedding identity and the determinant helper yields the complete displayed
formula. All three universe parameters are independent.

This is an internal derivation from the imported Library results, rather than
an additional claim extracted from the literature. The proof retains the
explicit row-surjectivity family as its sole additional premise; this module
does not import a proof of that family, and its theorem remains the
conditional implication `TwoBlockExtensionAssemblyStatement`.

That family is proved by the separate published theorem
[`Langlands.HarmonicAnalysis.padicRowFourierSurjectivity`](../../HarmonicAnalysis/PadicRowFourierSurjectivityProof.md),
in `Langlands.HarmonicAnalysis.PadicRowFourierSurjectivityProof`, for every
`F : PadicField.{u} p`, every `T : F.TopologicalData` and every row
dimension `d`, hence for `F.canonicalTopologicalData`. The separate published
theorem
[`Langlands.Whittaker.twoBlockWhittakerExtension`](TwoBlockExtensionProof.md),
in `Langlands.Representation.Whittaker.TwoBlockExtensionProof`, applies the
theorem of this module to that canonical specialization and proves the
unconditional parent `TwoBlockWhittakerExtensionStatement.{uF, uV₁, uV₂}`.
