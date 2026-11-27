# The limit of the integrated main terms in Lapid's §8

Module `Langlands.Global.LocalWavePacketMainTermLimitStatement` states one
proposition, `Langlands.Global.WavePacketMainTermLimitStatement`, and does not
prove it.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
  pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
  page = printed page + 9).
  - §3, pp.313–314: Proposition 1 with formula (2) and its main term;
    Proposition 2 with formula (4).
  - §7, p.325, before Lemma 7: the main term `M(λ, λ', T)` is smooth on
    `i(𝔞_P^G)^* × i(𝔞_{P'}^G)^*`, by the argument of Arthur 1982 (top of
    p.1299), which uses only the holomorphy of the intertwining operators.
  - §7, Lemma 8 and its proof, pp.326–327: the limit of integrals of `(G, M)`-
    families against `c_Q(T; Λ)/θ_Q(Λ)`.
  - §8, p.328: the truncated inner product of two wave packets has the same
    limit as the integral (18) over `μ ∈ i𝔞_G^*`, `λ ∈ i(𝔞_P^G)^*`,
    `λ' ∈ i(𝔞_{P'}^G)^*` of the main terms; "we have to show that this limit
    exists and is equal to the right-hand side of (4)". Lapid shows this: both
    sides vanish if `P` and `P'` are not associate; otherwise one reduces to
    `P' = P`, recasts the integrand as a sum over `s ∈ Ω(P, P)` of
    `(G, M)`-family expressions (following Arthur 1982, §§1–2), applies Lemma 8
    uniformly in `λ` and `μ`, and concludes by adjointness and a change of
    variable.
- J. Arthur, *An introduction to the trace formula* (2005), in
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: §17, pp.94–97,
  `(G, M)`-families and `(G, M)`-orthogonal sets.

Lapid's reference [Art82b] is J. Arthur, *On a family of distributions
obtained from Eisenstein series II: Explicit formulas*, Amer. J. Math. 104
(1982), 1289–1336.

## The proposition

`WavePacketMainTermLimitStatement` quantifies over a number field `F`, a
connected reductive `G` (`hG`), a maximal split torus `i : T → G` (`hi`), a
generic cocharacter `ν` (fixing the minimal parabolic `P_0` and the standard
parabolic subgroups `Standard.parabolicHom i ν S.roots`,
`S : StandardIndex hG hi ν`), a maximal compact subgroup `K` with
`IsIwasawaCompact` for every standard parabolic subgroup, and reflection data
`D`. There is no truncation in the statement.

### Data

1. *Normalizations of the main term*, exactly as in
   `LocalTruncatedEisensteinFamilyInnerProductStatement`: Levi projections
   `π S`, Haar measures `μM S` compatible with the Iwasawa decomposition of
   `P_S`, coordinates `eS S : ℝ^{nS S} ≃ X^*(P_S) ⊗ ℝ` and cutoffs `βS S` with
   `∫ βS S = 1` (they normalize `(·,·)_{P_S}`), and a basis `cd` of
   `𝔞_G = relativeCentralDirections i`.
2. *The two wave packets and the right side of (4)*, exactly as in
   `TruncatedWavePacketSectionSomeCompactLimitStatement` for the standard
   parabolic subgroups `P = P_J`, `P' = P_{J'}`: holomorphic families
   `λ ↦ ∑_l b_{j,l}(λ) v_{j,l}` (`v_{j,l} ∈ A^2_P`, `b_{j,l}` entire), their
   Eisenstein series `E j`, holomorphic on `DE`, smooth coefficients `c j`
   vanishing outside the compact `Sx` with `{i e(x) : x ∈ Sx} ⊆ DE`, and
   likewise `v'`, `b'`, `c'`, `E'`, `Sx'`, `DE'` for `P'`; a Levi projection
   `π'` of `P'`, the inner product `(·,·)_{P'}` given by `μM'`, `e'`, `β'`;
   representatives `w t` of `Ω(P, P')` and expansions
   `∑_l b_{j,l}(λ) M(w_t, λ) v_{j,l} = ∑_a coeff t j a (λ) ψ t j a` in
   `A^2_{P'}` with coefficients holomorphic on `DM ⊇ {i e(x) : x ∈ Sx}`.
   "Sufficiently regular" is `IsStandardRegularParameter D`.
3. *Expansions for the main term*: for every standard `S`, representatives
   `wS S t` of `Ω(P, S)` (`IsWeylConjugation`, injective and onto
   `weylParameterSet`) and expansions
   `∑_l b_{j,l}(λ) M(wS S t, λ) v_{j,l} = ∑_a coeffS S t j a (λ) ψS S t j a`
   in `A^2_S`, with coefficients holomorphic on one set
   `DMS ⊇ {i e(x) : x ∈ Sx}`; likewise `ΩS'`, `wS'`, `cwS'`, `ψS'`,
   `coeffS'`, `DMS'` for the families on `P'`.
4. *Coordinates adapted to the central parameter*: linear equivalences
   `A : ℝ^{n₁} × ℝ^m ≃ ℝ^n` and `A' : ℝ^{n₁'} × ℝ^m ≃ ℝ^{n'}` and measures
   `ν₁`, `ν₁'` such that `A` carries `ν₁ × dz` to Lebesgue measure (and
   likewise `A'`), and such that
   `pair T (restrictToTorus (e (A (u, z)))) (cd r) = z r` for all `u`, `z`,
   `r` (and likewise for `e'`, `A'`). Thus `z ∈ ℝ^m` is the central component
   of the parameter, in the coordinates dual to `cd`, and `u` parametrizes
   `(𝔞_P^G)^*`; the pairs `(e(A(u, z)), e'(A'(u', z)))` are exactly the pairs
   of parameters with the same central component.
5. A direction `v₀ ∈ V T` on which every simple root is positive.

### Conclusion

`mainTerm j j' T λ λ'` is the main term of formula (2) for the families `j`
of `P` and `j'` of `P'`, as in
`LocalTruncatedEisensteinFamilyInnerProductStatement`:

`∑_S ∑_{t, t'} vol(𝔞_S^G / L_S) e^{⟨Λ, T⟩} (M(w_t, λ)φ_j(λ), M(w'_{t'}, λ')φ'_{j'}(λ'))_S / ∏_{α ∈ Δ_S} ⟨Λ, α^∨⟩`,

with `Λ = w_t λ + w'_{t'} \bar λ'`, the volume `corootCovolume hG hi ν D S (eS S) cd`,
and the inner product written through the expansions of item 3. Let

`I(T) = (2π)^{m − n − n'} ∫ z ∫ u ∫ u' ∑_{j, j'} c_j(A(u, z)) \overline{c'_{j'}(A'(u', z))} mainTerm j j' T (i e(A(u, z))) (i e'(A'(u', z))) dν₁'(u') dν₁(u) dz`.

The proposition asserts that `I(j • v₀)` tends, as `j → ∞` through the
natural numbers, to

`∫ ∑_t ∑_{j, a, j', l'} c_j(x) coeff t j a (i e(x)) \overline{c'_{j'}(e'^{-1}(w_t e(x)))} \overline{b'_{j',l'}(w_t i e(x))} (ψ t j a, v'_{j',l'})_{P'} dspectralMeasure(x)`,

which is `∫ ∑_{w ∈ Ω(P, P')} (M(w, λ)φ(λ), φ'(wλ))_{P'} dλ`, the right side of
(4), in the form of `TruncatedWavePacketSectionSomeCompactLimitStatement`.

### Relation to Lapid's (18)

For `μ ∈ i𝔞_G^*` and `λ_1 ∈ i(𝔞_P^G)^*` the main term at `λ_1 + μ` is
Lapid's term for the shifted family: the normalized intertwining operators do
not change under central shifts, `w_t` fixes `μ`, and the conjugate of the
second parameter contributes `−μ`, so `Λ` involves only the components in
`(𝔞^G)^*`. Hence `I(T)` is (18) for the wave packets
`Θ = ∫ ∑_j c_j(x) E_j(i e(x)) dspectralMeasure(x)` and `Θ'`, written in the
coordinates `(u, z)`. The factor `(2π)^{m − n − n'}` collects the factors
`(2π)^{-n}`, `(2π)^{-n'}` of `spectralMeasure` and the factor `(2π)^m` of the
Plancherel formula on `ℝ^m` for the pairing `e^{i⟨z, y⟩}`, where
`y ∈ ℝ^m` parametrizes `A_G` through `cd`. This is the normalization with which
the Fourier transform on `𝔞_G` turns the truncated inner product of the wave
packets into the integral over `z`, `u`, `u'` of truncated inner products of
Eisenstein series on `G(F) \ G(𝔸)¹`.

The main term is singular where a denominator vanishes. For fixed `z` these
points lie in finitely many affine hyperplanes in `(u, u')`, a null set, so
the integrand is defined almost everywhere; by Lapid's §7 (p.325) the sum is
smooth on the support of the coefficients.

### The compact subgroup

The proposition is stated for every maximal compact `K` with Iwasawa
decompositions for the standard parabolic subgroups. It contains no
truncation operator; it is a statement about intertwining operators and the
inner products `(·,·)_{P_S}` on the given inducing data. Lapid's argument uses
only the holomorphy of the intertwining operators on the imaginary axis,
their functional equations and adjointness, and Lemma 8, which hold for the
normalized intertwining operators attached to any such `K`.
