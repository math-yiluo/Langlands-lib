# Elliptic character orthogonality for GLₙ

`Langlands.BaseChange.EllipticCharacterOrthogonalityStatement.{u, uV}` is a
common-measure form of Clozel's Theorem 3, the orthogonality relations for the
characters of square-integrable representations on the elliptic set (first
proved by Kazhdan). It covers `G = GL_n(F)` for a characteristic-zero
nonarchimedean local field `F : Type u` and positive rank `0 < n`.

## The statement

Write `Z` for the center of `G`. The group `G` carries the topology of
`Langlands.LocalFieldTopology`, which makes it Hausdorff, locally compact and
totally disconnected. The central quotient `G ⧸ Z` carries the Borel σ-algebra
`JacquetLanglands.centralQuotientMeasurableSpace`.

The statement asserts that, for each such `F` and `n`, one measure `ν` on
`G ⧸ Z` has the following property for every pair of representations. Let `ρ`
and `π` be complex representations of `G` on carriers `V` and `W`. The two
carriers may be different types in the same universe `uV`. Assume that:

- both are irreducible (`Representation.IsIrreducible`) and square-integrable
  modulo the center (`JacquetLanglands.IsSquareIntegrable`). The second condition
  means admissible, with a unitary central character and with square-integrable
  absolute matrix coefficients on `G ⧸ Z` for every Haar measure;
- their unitary central characters `cρ` and `cπ` (`UnitaryCentralCharacter`)
  satisfy `cρ.character = cπ.character`;
- `Θρ` and `Θπ` are functions on the regular elliptic elements of `G` that give
  the character values of `ρ` and `π` there (`JacquetLanglands.HasCharacterValue`).
  An element is regular elliptic (`JacquetLanglands.IsRegularElliptic`) when its
  characteristic polynomial is separable and irreducible over `F`. A character
  value at `g` is a number `c` such that, for every Haar measure `μ` on `G`, the
  distribution character relative to `μ` equals `c` times integration against `μ`
  on test functions supported near `g`.

Then some function `p` on `G ⧸ Z` satisfies `p (g Z) = Θρ g * conj (Θπ g)` for
regular elliptic `g` and `p (g Z) = 0` for all other `g`. This `p` is
`ν`-integrable, and `∫ p dν` is `1` if `ρ` and `π` are equivalent
(`Nonempty (ρ.Equiv π)`) and `0` otherwise. So the pairing is linear in the
character of the first representation and conjugate linear in the second. The
same `ν` serves for the self-pairings and for the mixed pairings of all pairs.

The condition on `p` determines `p`. The existential only records that the zero
extension of the product descends to the quotient, and it does. A scalar matrix
does not change whether a characteristic polynomial is separable and irreducible.
Translation by a central element `z` multiplies each character value by the
central character `ω(z)`. Since `|ω(z)| = 1` and `ω` is common to both
representations, the product is unchanged. By `HasCharacterValue.unique`, the
character values in the hypotheses are uniquely determined. Harish-Chandra's
theorem, recalled in Clozel §3, makes the character of an irreducible admissible
representation a locally integrable function that is smooth on the regular set,
so the values exist.

The field universe `u` and the carrier universe `uV` are independent.

## Relation to Clozel's Theorem 3

Clozel works with a connected reductive group over a p-adic field of
characteristic zero, and `GL_n` is a case. His square-integrable representations
are irreducible unitary representations whose matrix coefficients are
square-integrable modulo `Z`. The smooth vectors of such a representation form an
irreducible admissible representation of the kind quantified over here, with the
same character. Conversely, an irreducible admissible representation with a
unitary central character and square-integrable coefficients modulo `Z` is
unitarized by the `L²` inner product of its coefficients. Equivalence of
representations corresponds in both directions.

Theorem 3 states that, for two square-integrable representations `π₁` and `π₂`
with the same central character,

  `∑_T |W(G,T)|⁻¹ ∫_{Z\T} |D(γ)| conj(Θ_{π₁}(γ)) Θ_{π₂}(γ) dγ`

equals `1` if `π₁ ≅ π₂` and `0` otherwise. Here `T` runs over the elliptic Cartan
subgroups modulo conjugation, `W(G,T)` is the Weyl group, `D` is the Weyl
discriminant and the Haar measure `dγ` gives mass one to `Z\T`. The Weyl group in
the Weyl integration formula used in the proof is the rational Weyl group
`N_G(T)/T`. The printed integrand conjugates the first character. Both possible
values are real, so taking complex conjugates gives the same identity with the
conjugate on the second character, which is the convention of the Lean statement.

The common measure comes from the weighted torus measures. For `GL_n(F)`, the
elliptic maximal tori are the multiplicative groups of degree-`n` field
extensions of `F`, and there are finitely many conjugacy classes of them. For a
representative `T`, the quotient `T/Z` is compact. An element of `T` is regular
exactly when it is regular elliptic in `G`, and the weight `|D|` vanishes on the
other elements of `T`. Let `ν_T` be the measure `|W(G,T)|⁻¹ |D(γ)| dγ` on `T/Z`,
with `dγ` the Haar probability measure. Let `ν` be the sum of the pushforwards of
the `ν_T` along the injections `T/Z → G/Z`. For every pair as above, `∫ p dν` is
the conjugate of the left side of Theorem 3, so this single `ν` serves all pairs.

Integrability comes from Clozel's Proposition 4, Harish-Chandra's estimate for
tempered characters. Square-integrable representations are tempered. On the
regular elements of each Cartan subgroup, `|D|^{1/2} |Θ|` is bounded by
`c (1 + ‖γ‖)^r`. On an elliptic torus this function is invariant under `Z`, and
`T/Z` is compact, so it is bounded. Hence the integrand is bounded and each `ν_T`
is finite.

The existential quantifier leaves the choice of `ν` to the proof. The Lean
statement therefore follows from Clozel's formula with its explicit measure but
does not record that measure.

## Source

Laurent Clozel, *Invariant harmonic analysis on the Schwartz space of a
reductive p-adic group*, in W. H. Barker and P. J. Sally (eds.), *Harmonic
Analysis on Reductive Groups*, Progress in Mathematics 101, Birkhäuser (1991),
DOI `10.1007/978-1-4612-0455-8_6`.

- Setting (connected reductive group over a p-adic field of characteristic
  zero): §2, printed p. 102 (PDF p. 113).
- Characters as locally integrable functions and Proposition 4: §3, printed
  p. 107 (PDF p. 118).
- Square-integrable representations: §3, printed p. 108 (PDF p. 119).
- Theorem 3, its Remark on the measures and its proof: §3, printed pp. 110–111
  (PDF pp. 121–122).

Literature ID
`provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`,
SHA-256 `c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba`.
