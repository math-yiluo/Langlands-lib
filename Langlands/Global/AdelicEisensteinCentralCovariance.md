# Central covariance of Eisenstein series and their continuations

`Langlands.Global.EisensteinContinuationCentralCovarianceStatement` covers
the parabolic data used for Eisenstein series in the Library. That is a
parabolic `p : P ⟶ G` of a connected reductive group over a number field, a
Levi `l : M ⟶ P`, a root presentation `r` whose split component is
`a : A ⟶ M`, split tori, and a compact subgroup `K` that is Iwasawa for `P`.
Let `φ` satisfy Lapid's `A^n_P` condition `IsSplitComponentEquivariant`, that
is `φ(l(b) g) = l(b)^{ρ_P} φ(g)` for `b` in the split component
`A_M = RestrictionSplitCentre.canonicalSubgroup F M`. Let `E` be a pointwise
continuation of its Eisenstein series in the sense of the wave-packet
statements:

- for each `g`, `λ ↦ E(λ)(g)` is meromorphic in coordinates with holomorphy
  domain `D`;
- `E(λ) = E(·, φ, λ)` for all sufficiently regular `λ`.

Let `Z` be a split torus and `i : Z ⟶ G` a central homomorphism (`IsCentral`,
on all test schemes) that factors through the Levi as `i = j ≫ l ≫ p`. Then,
for every point `x` of the positive subgroup `intrinsicSubgroup F Z`, every
`λ ∈ D` and every `g ∈ G(𝔸)`,

  `E(λ)(i(x) g) = x^{λ|_Z} E(λ)(g)`.

Here `i(x)` is `positivePointMap F G Z i x`, the map used by the published
product decomposition `AdelicFullRationalQuotientProduct.lean`. Also,
`λ|_Z = parameterRestrict (j ≫ l) λ` and `x^μ = parameterPower F Z μ x`. The theorem
`eisensteinContinuationCentralCovariance` proves the statement.

The module also proves the following supporting results:

- `IsIwasawaCompact.heightPower_map_mul` gives
  `m_P(p(q) g)^λ = q^λ m_P(g)^λ` for `q ∈ P(𝔸)`.
- `IsIwasawaCompact.eisensteinSeries_central_mul` covers any `q ∈ P(𝔸)` with
  `p(q)` central in `G(𝔸)` and `φ(p(q) x) = s φ(x)` for a scalar `s`. It
  gives `E(p(q) g, φ, λ) = s q^λ E(g, φ, λ)` for the defining sum at *every*
  `λ`. When the terms are not summable, both sides are zero.
- `eisensteinContinuation_central_mul` gives the same covariance at every
  parameter of the holomorphy domain of a pointwise continuation.
- `IsIwasawaCompact.eisensteinSeries_splitComponent_mul` and
  `eisensteinContinuation_splitComponent_mul` cover `b ∈ A_M` with `p(l(b))`
  central in `G(𝔸)`. They give the factor `l(b)^{λ + ρ_P}`.
- `parameterPower_halfModulus_map_of_isCentral` shows that `m^{ρ_P} = 1` at
  points of a commutative group scheme mapping into `P` whose composite with
  `p` is central.
- `eisensteinContinuation_splitCentre_mul` is the main theorem.
- `packetIntegral_central_mul` assumes `E_j(λ)(z g) = κ(λ) E_j(λ)(g)` for
  `λ ∈ D`, and that each coefficient `c_j(x)` is nonzero only when `e(x) ∈ D`.
  Then `∫ ∑_j c_j(x) E_j(e(x))(z g) dm(x)` equals
  `∫ κ(e(x)) ∑_j c_j(x) E_j(e(x))(g) dm(x)`. The two integrands are equal at
  every point, so no integrability is assumed.

## Provenance and scope

This identity is used, without separate statement, for the Fourier transform
along `A_G` in the proof of Proposition 2 in §8, printed p. 328 (PDF p. 337),
of E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), pp. 309–331. The source is
registered as `lapid-2011-asymptotic-inner-product-truncated-eisenstein`. The
definitions of `E(g, φ, λ)` and of `A^n_P` follow §2, pp. 311–312 (PDF
pp. 320–321), as formalized in `AdelicEisensteinSeries.lean` and
`AdelicSquareIntegrableInducedForms.lean`.

The factorization `j` of the central torus through the Levi is a hypothesis
and is not constructed here. No claim is made about regularity of `E` in the
adelic variable, about square integrability, or about the Fourier transform
itself.

## Implemented proof

- **Defining sum.** Let `d ∈ G(F)` be the chosen representative of a coset in
  `P(F)\G(F)`. Centrality gives `d p(q) g = p(q) d g`. The hypothesis on `φ`
  and `IsIwasawaCompact.height_map_mul` show that the term at `d` gets
  multiplied by `s q^λ`. Pulling the constant out of the unconditional sum
  (`tsum_mul_left`) needs no summability.
- **Continuations.** Both sides are meromorphic in coordinates in `λ`. The
  left side is `E` at the fixed point `p(q) g`. The right side is a constant
  times `λ ↦ q^λ` times `E(λ)(g)`, and `λ ↦ q^λ` is entire by
  `differentiable_parameterPower_affine`, hence meromorphic on the whole space
  (`isMeromorphicInCoordinatesOn_univ`). The two sides agree for sufficiently
  regular `λ`, by the series identity. So
  `ParabolicRootPresentation.eqOn_of_regularParameter` (scalar meromorphic
  uniqueness from the nonempty open regular region) gives equality on all of
  `D`. For `b ∈ A_M`, the identity `l(b)^{ρ_P} l(b)^λ = l(b)^{λ+ρ_P}` comes
  from additivity of the pairing and the exponential.
- **Half modulus.** For `j : Z ⟶ P` with `j ≫ p` central, `j` is central in
  `P` (`CoverPreimage.isCentral_of_comp_mono`, using that `p` is a
  monomorphism). Then the restriction of the adjoint determinant character of
  `P` to `Z` is zero (`Lie.adjointDeterminantCharacter_restrict_eq_zero_of_isCentral`).
  So `parameterRestrict j ρ_P = 0`, and `parameterPower_parameterRestrict`
  gives `m^{ρ_P} = 1` at `j(x)`.
- **Split centre.** `j` is central in `M`, since `l ≫ p` is a closed subgroup
  and hence a monomorphism. By `IsSplitComponent.exists_factor`, `j` factors
  through the split component `a`. Positive points of `Z` map to positive
  points of `A` (`PositiveRealTorus.map_intrinsicSubgroup_le`). Hence `j(x)`
  lies in `imageSubgroup F A M a`, which is `A_M` by
  `RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup`. `i(x)` is
  central in `G(𝔸)` (`positivePointMap_commute`) and equals `p(l(j(x)))`. The
  `A_M` case then gives the factor `j(x)^{λ+ρ_P}`. The `ρ_P` part is `1`, and
  the `λ` part is `x^{λ|_Z}` by `parameterPower_parameterRestrict`.
- **Packets.** The integrands are compared at each `x`, one summand `j` at a
  time. If `c_j(x) = 0`, that summand is zero on both sides. Otherwise
  `e(x) ∈ D` and the covariance applies.
