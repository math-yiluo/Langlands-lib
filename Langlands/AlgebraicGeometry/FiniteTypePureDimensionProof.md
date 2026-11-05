# Pure dimension under arbitrary field extension: proof

This development proves the exact proposition
`SchemeFiberGeometry.FiniteTypeFieldExtensionPureRingDimensionInvariance`.
It is an internal algebraic prerequisite for the componentwise fibre
condition of Conrad Theorem 3.4(2); scheme base-change comparisons,
constructibility and unrestricted filtered descent remain separate.

`HasPureRingDimension.of_ringEquiv` transports the condition across an
actual ring isomorphism, in independent universes. The proof uses the
prime-spectrum homeomorphism to transport irreducible components and
their topological dimensions and then applies the affine comparison.

The fraction-field helper embeds a domain A into its actual fraction
field, views that field as flat over an injectively embedded domain R
through FractionRing R, and tensors this injection with a flat R-algebra S.
When S is a domain, the resulting algebra is torsion-free over S.
A minimal prime cannot contain a nonzero scalar image because every
element of a minimal prime is a zero divisor. Thus it contracts to zero.
For an integral torsion-free algebra over a domain, the induced injection
of minimal-prime quotients is integral and preserves Krull dimension.
The quotient by the contracted zero ideal is identified with the base.

`hasPureRingDimension_tensorProduct_of_domain` applies actual Noether
normalization P = k[Fin n] into a finite-type domain A. The scalar
extension S = P tensor_k K is a domain through tensor commutation and
the polynomial algebra equivalence, and it is flat over P. The
fraction-field helper makes S tensor_P A torsion-free over S, and
finiteness of A/P makes this algebra integral over S. Each component
has the dimension of S, which agrees with the dimension of P and A.
Tensor commutation and `cancelBaseChange k P P A K` identify this ring
with A tensor_k K.

`ringKrullDim_quotient_eq_of_intermediate_pure` passes from pure dimension
of B/I to the dimension of B/q when q is a minimal prime of B and I is
contained in q. The minimal-prime correspondence supplies the prime of
B/I above q, and the actual third isomorphism theorem identifies its
quotient with B/q. Noether normalization also supplies a natural number
for the dimension of each finite-type domain.

For a minimal prime q of A tensor_k K, its contracted prime p in A is
prime, so A/p is a finite-type domain. The domain theorem and the actual
`quotientTensorEquiv` give pure dimension to
(A tensor_k K)/(p extended). The intermediate-quotient lemma then proves
that the dimension of (A tensor_k K)/q equals the dimension of A/p.
This component comparison does not assume that A is a domain or that
its scalar extension is a domain or reduced.

For preservation, flat going down shows that p is a minimal prime of A,
so the pure-dimension hypothesis determines this common dimension.
For reflection, flat tensoring of k into K proves injectivity of
A into A tensor_k K. The minimal-prime lifting theorem therefore supplies
an upstairs minimal prime over each minimal prime of A. The same
component comparison determines its dimension from the upstairs
pure-dimension hypothesis. The final theorem packages these two
implications as the exact named universal proposition, in independent
universes u, v and w. All field extensions, including inseparable and
transcendental ones, are included; only A is assumed finite type.
