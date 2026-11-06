# Involutive matching of Hermitian inducing parameters

Worker 1765 derives an involutive matching from the actual Hermitian parameter
symmetry used in Henniart 2000, Appendix A.2, printed p.453. This is an auxiliary
construction for applying the corrected Appendix pole argument, not a proof of
unitary-generic classification or of the associated-pair induction theorem.

The published `HasHermitianSymmetricParameters` supplies an arbitrary finite
bijection matching `(s, δ)` with `(-s, δ)`, preserving ranks and actual block
isomorphisms with multiplicities. It does not require that bijection to square
to the identity. The published analytic `SymmetricBlockData` instead requires
an involutive partner. The construction here closes this combinatorial gap.

For a matching `e` negating the real exponent function `s`,
`oppositeExponentPartner e s` uses `e` on positive exponents, `e.symm` on negative
exponents, and the identity on zero exponents. Negation exchanges the positive
and negative sets, so applying the resulting partner twice is the identity.
Zero exponents are fixed. `oppositeExponentInvolution` bundles this function
as an equivalence. The partner negates exponents and preserves every reflexive
symmetric relation already preserved by the given matching; inverse matches
use symmetry of that relation.

`HasHermitianSymmetricParameters.exists_involutive` applies this construction to
the relation that block ranks agree and that, after transport along that rank
equality, the actual smooth blocks are isomorphic. Reflexivity uses the identity
isomorphism; symmetry uses the inverse isomorphism. The result is an involutive
bijection with all the original rank, exponent and block-isomorphism properties.
No ordinary self-contragredience is imposed. Field and representation universes
are independent, and the general construction works for an arbitrary index
universe without a finiteness assumption.

The original source is G. Henniart, *Une preuve simple des conjectures de
Langlands pour GL(n) sur un corps p-adique* (2000), Appendix A.2, printed p.453
(PDF p.15), registered as `henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The source supplies the multiplicity-preserving Hermitian symmetry. The
sign-based involution is a derived construction, not a separately stated result
of the source. Actual classification, segment descriptions, pair-factor formulas,
and gamma comparison remain separate proof obligations.
