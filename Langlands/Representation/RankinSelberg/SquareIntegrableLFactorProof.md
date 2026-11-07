# L-factors of pairs of essentially square-integrable representations

`squareIntegrableLFactor` proves the unchanged proposition
`SquareIntegrableLFactorStatement`, with independent field, two supercuspidal
carrier and two component-carrier universes. The target is JPSS 1983,
Theorem (8.2), display (5), printed pages 444–445.

The proof first establishes `squareIntegrableLFactor_normalized`, assuming
square-integrability of the supercuspidal bases and the actual irreducible
components. Square-integrable genericity supplies the component Whittaker
types. Real twists preserve the Whittaker types of the supercuspidal blocks.
Pole-freeness supplies L-polynomial certificates for the components and their
actual inverse-transpose pullbacks, with the negated additive character and
the same underlying Haar measure for the latter.

For equal base ranks, `supercuspidalParameterProduct` supplies a finite set of
complex units and certified original and dual products of linear factors.
Square-integrable unitarity makes their parameters have norm one.
`centeredBlockLPolynomial` rescales these certificates to every centered block
pair. `componentGammaProduct` compares the actual component gamma factor with
the rectangular block product, producing a reflected-ratio identity up to a
nonzero Laurent monomial. `segmentGammaTelescoping` cancels the rectangular
interior factors. The resulting boundary products have no zero in the open
unit disk, since the parameters have norm one and the rank inequality orders
the segment lengths. `gammaDecompositionUniqueness_of_ratio` identifies the
component polynomial with the boundary polynomial, which is precisely the
first-row block product. When the base ranks differ, the supercuspidal
unequal-rank formula makes every block polynomial one, and the same ratio
uniqueness argument gives the result.

To remove the extra square-integrability assumptions, each supercuspidal base
is realized on its original smooth carrier and normalized by a real
determinant twist using its essential square-integrability. Twisting actual
subrepresentations and their surjective intertwiners, followed by the
normalized-induction twist equivalence, transports each component hypothesis
to the centered induction of the normalized base.

The private `squareIntegrable_centered_component` lemma proves these normalized
components are square-integrable. A square-integrable base supplies a unitary
character of the actual center. Its restriction to scalar matrices is denoted
by omega. The scalar character of the centered induction is the product of
the block scalar characters. The centered real exponents sum to zero, so the
determinant powers cancel and the product is omega raised to the number of
blocks. This character has norm one. Scalar action passes through the actual
invariant subspace and surjective intertwiner to the component, without an
equality constraint on the carrier universes. Essential square-integrability
supplies admissibility, and irreducibility makes the carrier nontrivial.
`glSquareIntegrableCentralCharacter` constructs a unitary character of the full
center; the published essential-square-integrability criterion then removes
the remaining real normalizing exponent.

The normalized formula now applies. The two-variable real-twist theorem
transports both the component certificate and every first-row block
certificate back to the original representations. Polynomial substitution is
a ring homomorphism, so it preserves the finite product equality. No
hypothesis is added to the target, and its defining Lean/Markdown pair and
imported pairs are unchanged.

This proof is an assembly of the imported representation-theoretic,
analytic and finite-polynomial results. The private transport and scalar
character lemmas are derived algebraic steps for this assembly; the proof
route uses the published supporting interfaces rather than reproducing all
intermediate prose of JPSS.
