# Rank-one matrix functional equation

`Langlands.GodementJacquet.tateMatrixFunctionalEquation` proves exactly
`TateMatrixFunctionalEquationStatement.{uF,uV}`. For every prime and canonical
p-adic field, every bundled nontrivial continuous unitary additive character,
every supplied self-dual scalar additive Haar measure, and every admissible
irreducible complex representation of GL₁ on the actual independently universed
carrier, it constructs the full
`Padic.NormalizedMatrixFunctionalEquationData (n := 0)`.
The statement and its imported definitions are used unchanged.

The proof assembles the proved character reduction, actual matrix analytic
assertions, and scalar functional equation. These are imported from
`TateCharacterReduction`, `TateMatrixAnalyticData`, and
`TateScalarFunctionalEquation`. The scalar equation is itself derived from the
independent Rankin–Selberg `equalRankFunctionalEquation`, specialized to the
character paired with the trivial character at rank index zero. That input's
proof does not depend on the Godement–Jacquet Tate matrix base.

The final closed theorem first obtains nontriviality of the carrier from
irreducibility. `exists_tateCharacterModel` proves the existence of a continuous
quasicharacter χ and an actual representation equivalence from the original
representation σ to `rankOneCharacter χ`. Its proof derives scalar action from
admissible Schur theory and the rank-one scalar/determinant identity, then uses
irreducibility to construct the one-dimensional equivalence. In the present
module, injectivity, linearity, and the intertwining identity of that equivalence
give `TateCharacterAction σ χ` on the original carrier. The remainder of the
argument constructs the datum directly for σ. The character, equivalence, and
scalar action are derived inside the proof.

`Padic.exists_tateMatrixFunctionalEquationData` performs that assembly for any
smooth nonzero representation with a proved scalar action. It first obtains P
and PDual from `exists_tateMatrixAnalyticAssertions` and
`exists_tateIotaMatrixAnalyticAssertions`. These include a common right
half-plane before every test and bi-smooth coefficient on each side, actual
rational continuations for every such pair, and both exact normalized
reciprocal-polynomial Laurent-span generator equalities. In particular,
`P.coeff 0 = PDual.coeff 0 = 1`. The matrix and scalar rational-value family
equalities transfer these generator properties to the weight-one scalar Mellin
families for χ and χ⁻¹. The supplied-generator scalar functional equation then
chooses a fixed unit c and integer a before all tests.

The matrix/scalar comparisons use the canonical normalized multiplicative Haar
measures, identified exactly by `TateScalarTransport`, and the canonical
normalized absolute value and residue cardinality q. The rank-one JPSS shift is
zero. The transformed coefficient is the original function composed with
inverse transpose; `tateInverseTranspose_eq_inv` identifies this with inversion
in GL₁. Thus the transformed character is χ⁻¹, while the coefficient's value at
the identity is unchanged. `Units.val_inv_eq_inv_val` explicitly identifies the
complex value of the inverse character with the inverse complex value.

The Fourier comparisons in this module retain the supplied additive measure ν.
`tateRectangularFourierIntegral_eq` uses
`oneByOneScalarEquiv_measurePreserving ν` to identify the full one-by-one
product measure with ν. The plus transpose pairing becomes the product of the
two scalar entries. Evaluating the full matrix test in those coordinates gives
the scalar Schwartz–Bruhat test `tateScalarTest`. There is no measure factor.
`tateMatrixFourierPair_of_scalar` also transports integrability at every
Fourier parameter, then pulls the scalar Schwartz–Bruhat witness back along
`tateMatrixScalarHomeomorph` to obtain a full matrix test.

For a matrix test Φ, the assembly theorem applies the scalar equation to
φ = `tateScalarTest Φ` and chooses its Fourier witness φhat before introducing
any coefficient or continuation. Its pullback is the matrix witness Φhat.
For an arbitrary bi-smooth coefficient f, scalar action gives
`f(g) = f(1) * χ(det g)`. Set k = f(1). The original and transformed matrix
continuations consequently become scalar continuations with tests kφ and
kφhat. To use the scalar equation with precisely those tests, the proof applies
the same fixed scalar equation to kφ. The lemma
`tateScalarFourierWitness_smul`, using linearity of the scalar Fourier transform,
identifies the witness returned for kφ with kφhat. This argument includes k = 0
and requires no division by the coefficient value.

Finally, `tateHasShiftedRationalValue_iff` transports each arbitrary supplied
matrix continuation to the corresponding scalar continuation. Applying the
equation for kφ proves `NormalizedFunctionalEquation q P PDual 1 c 0 a R RDual`
for every such pair R, RDual. With z = q^(-s) and zDual = q^(-(1-s)), it says

```text
PDual(zDual) * RDual(zDual) = c * z^a * (P(z) * R(z))
```

whenever `R.denom.eval z ≠ 0` and `RDual.denom.eval zDual ≠ 0`.
Both guards, the dual parameter 1-s, the spectral variable, the central scalar
1, and the sign exponent 0 remain those of the imported predicate. Together
with the two analytic assertions and the coefficient-independent Fourier
witness, this supplies every conjunct of the requested full matrix datum.

The mathematical target is the rank-one specialization of Godement and
Jacquet, *Zeta Functions of Simple Algebras* (1972), Theorem 3.3 and its
normalization discussion, printed pages 30–34 (one-based PDF pages 40–44).
Printed page 31 identifies M = F with the Tate case; pages 32–33 discuss the
normalized generator and the nonzero constant times an integral power of
q^(-s). The registered source is
`godement-jacquet-1972-zeta-simple-algebras`, SHA256
`86a8900900504adeb5757a04b5bb8a8754e6ef00b0fff49754096d371f59d568`,
retained at
`/home/taskhub/central-library/Godement-Jacquet--Zeta functions of simple algebras (book)--1972.pdf`.
The implemented proof follows the internal scalar specialization and transport
route described above. It assumes no additional analytic assertion, central
character, Whittaker certificate, or character-model equivalence.
