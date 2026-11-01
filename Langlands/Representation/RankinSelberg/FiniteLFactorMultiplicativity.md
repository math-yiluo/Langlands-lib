# Symmetric polynomial choice and finite-block L-polynomial divisibility

Worker 46 adapted the ordered induction in Worker 20's
`FiniteGammaMultiplicativity` to symmetric L-polynomial certificates and their
cleared polynomial divisibility relation. This is an internal derivation from
the imported Library results, following the finite-block reduction motivating
JPSS Section 3.2. It does not supply the two-block analytic theorem.

`whittakerTypeLPolynomial F ψ ν π σ hπ hσ` chooses a polynomial from the closed
`symmetricLPolynomialExists` theorem for two actual full Whittaker-type
representations. It requires no supplied factor-existence certificate.
`whittakerTypeLPolynomial_spec` supplies its full symmetric certificate,
including compatible-measure existence and universality.
`whittakerTypeLPolynomial_eq` identifies it with every other certified
polynomial for the same pair by uniqueness. The ranks and three universes are
independent, the supplied self-dual Haar measure is retained, and neither
irreducibility nor a restricted rank order is assumed.

The exported theorem is
`Langlands.RankinSelberg.lFactorMultiplicativity_of_twoBlock`. Its single premise
is `TwoBlockLFactorMultiplicativityStatement.{uF,uV,max uF uW}` and its conclusion
is the unchanged `LFactorMultiplicativityStatement.{uF,uV,uW}`. The field, test
carrier and original block carriers have independent universes. Actual induced
tail carriers live in `max uF uW`, explaining the premise's universe. No
two-block premise at the original block-carrier universe is required.

The proof inducts on the number of ordered positive blocks. An empty family
contradicts the positive total rank. For one block,
`whittakerTypeLPolynomial` supplies a polynomial for the original pair using
closed symmetric existence, and its specification supplies the certificate.
`singleBlock_L_iff` transports that same certificate to the actual normalized
singleton induction. The block polynomial is the same polynomial, and the
cleared identity holds with quotient `1` and exponent `0`.

For at least two blocks, the remaining tail has positive rank. The induction
hypothesis supplies an induced-tail polynomial `Pt`, block polynomials `Pit`,
and an identity
`X ^ etail * product Pit = Qt * Pt`. The closed
`normalizedProductWhittakerType` theorem supplies full Whittaker type for the
actual normalized tail induction. The rank substitution construction
`normalizedProductRankCastEquiv` identifies its head/tail-shape rank with the
successor rank used by that theorem.

The outer two-block family is the original head lifted to the common induced
carrier universe, followed by the actual tail induction. Full Whittaker type
transports through the head lift and the tail rank equivalence. A private
shape adapter eliminates equality of size functions before applying the
two-block premise; this preserves the dependent representations and the actual
ordered normalized induction.

That premise supplies a polynomial `P` for the outer induction, polynomials
`H 0` and `H 1` for its two factors, and an identity
`X ^ eouter * (H 0 * H 1) = Qo * P`. Symmetric L-certificate transport returns
the head certificate to its original carrier. Tail certificate transport and
uniqueness identify `H 1 = Pt`. The published
`headTailProductInductionEquiv` transports `P` to the original normalized upper
induction, with its order and positive-half-modulus normalization preserved.

The final original block family is `Fin.cons (H 0) Pit`. Multiplying the tail
identity by the head polynomial, then combining it with the outer identity,
gives
`X ^ (etail + eouter) * product (Fin.cons (H 0) Pit) = (Qo * Qt) * P`.
Thus the divisibility direction is exactly the one in the published target.
All polynomials retain their actual existential certificates.

The existing symmetric certificate relations retain the supplied self-dual
Haar measure, existence of compatible quotient measures and one polynomial
valid for every compatible measure. All canonical fields, nontrivial unitary
additive characters, positive ranks, both rank orders and arbitrary reducible
full Whittaker-type inputs remain quantified as in the imported statements.
There is no irreducibility assumption.

This conditional result leaves the two-block analytic theorem as a premise.
It does not establish the closed multiplicativity proposition required by the
parent task. Its mathematical provenance is the imported actual induction
equivalences, closed Whittaker-type and polynomial-existence theorems,
certificate transport and uniqueness, and elementary polynomial algebra.
