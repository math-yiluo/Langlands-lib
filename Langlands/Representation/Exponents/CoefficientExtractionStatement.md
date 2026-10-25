# Exact coefficient extraction for normalized Jacquet exponents

Author: Worker 322.

`Langlands.GLJacquetExponentCoefficientExtractionStatement.{uF,uV}` is a closed
Prop-valued definition. This module states the extraction consequence of
canonical Jacquet duality; it does not prove it or the tempered exponent
criterion.

## Exact scope

The proposition quantifies over every prime `p`, finite p-adic field
`F : PadicField.{uF} p`, supplied realization `T : F.TopologicalData`, positive
rank `n`, and complex module `V : Type uV`. The field and representation
universes are independent. Both admissibility and the smooth dual use the
topology supplied by `T`.

For every admissible representation `ρ` of `GL_n(F)`, every ordered standard
block shape `B`, and every character `χ` satisfying the existing
`T.IsJacquetExponent B ρ χ`, there exist `v : V`, `ℓ : SmoothDual ρ`, and
`ε : ℝ` with `0 < ε ≤ 1` such that, for every block-scalar tuple `a` satisfying

```
T.normalizedAbs ((a i : F.Carrier) / (a j : F.Carrier)) < ε  whenever i < j,
```

the actual coefficient satisfies

```
ℓ.1 (ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) v)
  = (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) * (χ a : ℂ).
```

The witnesses are chosen before the universal quantifier over `a`. Thus one
coefficient works on the whole indicated chamber. This is an exact equality,
with coefficient of `χ` equal to one, not a bound or an eventual identity on
one ray. Common multiplication of every coordinate by any `c : F.Carrierˣ`
preserves all ratios and remains unrestricted. For a one-block shape there
are no indices `i < j`, so the equality is asserted for every scalar tuple.
The positive half modulus is then one.

The hypothesis is the published generalized exponent predicate for the
normalized **upper** Jacquet module. It includes smoothness of `χ` and a
nonzero vector killed by one uniform power of every shifted split-centre
operator. It does not supply an eigenvector. The proposition has no
finite-length, irreducibility, scalar-central-character, chosen-pairing,
nonzero-carrier, or finite-dimensional-ambient-space premise. A zero carrier
is permitted; its Jacquet module has no generalized exponent witness.

## Original source and derivation

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333:

- §I.2, pp.242–243: finite-dimensional translation spaces on the split centre
  contain the pure characters appearing in their exponential-polynomial
  expansion.
- §I.3, p.243: generalized exponents, admissibility of the Jacquet
  representation, and the normalization
  `π_P(m) j_P(v) = δ_P(m)^(-1/2) j_P(π(m)v)`.
- Theorem I.4.1 and Corollary I.4.2, p.245: the nondegenerate invariant pairing
  between the upper Jacquet module and the opposite Jacquet module of the
  smooth contragredient, its chamber asymptotic identity, and the duality
  identification.
- Proposition III.2.2, pp.265–266, especially the first paragraph of its proof
  on p.266: the character equals `δ_P(a)^(-1/2)` times a single smooth
  coefficient throughout a sufficiently deep chamber.

Registered source: `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The retained file is
`/home/taskhub/central-library/Waldspurger--La formule de Plancherel pour les groupes p-adiques d'apres Harish-Chandra--2003.pdf`;
one-based PDF page equals printed page minus 234. The cited pages were read,
and the formulas on pp.245 and 266 were checked in their page images. No
project errata entry for this source was found.

The Lean target is a derived `GL_n` specialization of the extraction step.
Although the proof of III.2.2 starts with a tempered representation, the
extraction sentence invokes I.2 and I.4.1; these require admissibility, not
temperedness. Temperedness is used in the subsequent growth estimate. The
present statement isolates the preceding extraction and makes its supporting
steps explicit as future proof obligations:

1. **Jacquet admissibility.** The normalized Jacquet representation of an
   admissible `ρ` is smooth and admissible. A generalized-character witness
   is fixed by a compact open subgroup of the Levi. Its split-centre orbit
   remains in that fixed-vector space because block scalars are central.
   Admissibility makes this space finite-dimensional; it does not make the
   whole Jacquet module or `V` finite-dimensional.
2. **Generalized character to eigenvector.** In the resulting nonzero
   finite-dimensional invariant generalized-character space, the commuting
   split-centre operators have a common eigenvector. Their generalized
   character equations force its eigencharacter to be `χ`. This is the
   linear-algebra extraction behind the pure-character step in I.2. It
   needs a proof; the definition of `IsJacquetExponent` alone does not
   assert it.
3. **Pairing nondegeneracy.** The canonical pairing of I.4.1 detects this
   nonzero eigenvector with an element of the opposite Jacquet module of
   the smooth contragredient. Rescale that element so that the pairing
   equals one. The pairing and its nondegeneracy are conclusions of
   canonical duality, not premises added to this statement.
4. **Surjective quotient lifts.** Lift the eigenvector through the actual
   upper Jacquet quotient map to a vector `v : V`, and lift the chosen
   opposite quotient element to `ℓ : SmoothDual ρ`. Quotient surjectivity
   supplies representatives; neither a preselected lift nor a section is
   assumed.
5. **Normalization and the chamber.** Apply I.4.1 to these fixed lifts.
   Pairing the normalized eigenvector action gives `χ(a)`. Multiplying
   its identity by the positive half modulus yields exactly the displayed
   coefficient formula. In Lean, `splitCentreJacquet_mk` and
   `normalizedJacquet_mk` record the inverse-half normalization, while
   `leviHalfModulus` is the positive half of the explicit upper block
   modulus. Identifying this explicit modulus with Haar conjugation
   scaling is the separately published `Langlands.glBlockModulusHaar`.
   No inverse character, complex conjugation, or opposite exponent is
   inserted.

For the upper standard block parabolic, the simple relative roots restrict
to adjacent ratios `a_i / a_(i+1)`. Given the source threshold `ε₀ > 0`,
replace it by `ε = min ε₀ 1`. The all-pairs inequalities in the Lean
statement imply the adjacent inequalities required in I.4.1. Conversely,
with `ε ≤ 1`, products of adjacent ratios show that adjacent inequalities
imply all-pairs inequalities; hence this formulation retains the full deep
block chamber. There is no restriction on common scalar directions. With
one block the root set is empty, so I.4.1 applies to every scalar, as does
the Lean statement.

## Library dependencies and proof boundary

`Langlands.Representation.Exponents.Jacquet` supplies `IsJacquetExponent`,
`splitCentreJacquet`, the actual upper Jacquet quotient, block-scalar
embedding, normalized absolute value, and half modulus.
`Langlands.Representation.Smooth.Contragredient.Definitions` supplies the
actual smooth dual. The statement imports these existing constructions;
no substitute spectral datum or postulated pairing is introduced.

The five steps above explain the mathematical provenance and the work
required for a separate proof. This module implements none of them.
Canonical pairing and opposite smooth-duality construction are separate
dependencies; this statement does not duplicate their interfaces or assume
their conclusions. It does not prove temperedness, any integrability
estimate, or any classification result.
