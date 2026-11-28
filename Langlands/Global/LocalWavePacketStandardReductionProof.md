# Proof of the reduction of Lapid's §8 limit to standard parabolic subgroups

Module `Langlands.Global.LocalWavePacketStandardReductionProof` proves
`Langlands.Global.TruncatedWavePacketStandardizationStatement` (module
`Langlands.Global.LocalWavePacketStandardReduction`) as
`Langlands.Global.truncatedWavePacketStandardization`.

The statement is the implication `TruncatedStandardWavePacketLimitStatement →
TruncatedWavePacketSectionSomeCompactLimitStatement`. Lapid, *On Arthur's asymptotic inner product
formula of truncated Eisenstein series* (2011), §8, proves the limit of truncated inner products of
wave packets for standard parabolic subgroups `P, P' ⊇ P₀` of one minimal pair. The implication
transports this to arbitrary presented parabolic subgroups.

## Helper modules

- `Langlands.Global.LocalWavePacketPairLimit`: the predicate `TruncatedWavePacketPairLimit` for
  one pair of parabolic subgroups, one compact subgroup and one truncation, and `mono_reg`.
- `Langlands.Global.LocalWavePacketParabolicIsoTransport`: transport along isomorphisms of the
  source (`of_iso_source`) and of the target (`of_iso_target`).
- `Langlands.Global.LocalWavePacketTargetConjugation`: transport along rational conjugation of the
  target (`of_conj_target`).
- `Langlands.Global.LocalWavePacketStandardRegularity`: comparison of the regularity conditions
  (`StandardParabolicFamily.exists_isRegularParameter_of_coroot_lt`).

## `standardPairLimit_of_statement`

The hypothesis `TruncatedStandardWavePacketLimitStatement`, for one maximal split torus `i` and
generic cocharacter `ν`, gives `K` and, for all reflection data `D`, comparisons `hρ` and
directions `v₀`, `TruncatedWavePacketPairLimit` for the standard parabolic subgroups
`P_J`, `P_{J'}` with `J, J' ⊆ Δ` arbitrary sets of simple roots. The truncation is
`j ↦ Λ^{j v₀}`. The regularity predicates are `IsStandardRegularParameter D J` and
`IsStandardRegularParameter D J'`. The statement indexes standard parabolic subgroups by finite
subsets `S` of the simple roots. For a set `J ⊆ Δ` the filter of the simple roots by `J` is such
an `S` with `S.roots = J`, and the hypothesis applies after substituting `J = S.roots`.

## Proof of `truncatedWavePacketStandardization`

Let `P`, `P'` be the presented parabolic subgroups with presentations `r`, `r'`, and let
`(i, ν) = (r.data.i, r.data.ν)`. Take `K` from `standardPairLimit_of_statement` for `(i, ν)`, and
let `fam = StandardParabolicFamily.ofMaximalSplitTorus` be the standard family of `(i, ν)`.

1. Source. `P` and `P_I`, `I = r.data.J`, have the same image in `G`. This gives `P_I ≅ P` and
   `M_I ≅ M` over `G` (`IsClosedSubgroup.sourceIsoOfRangeEq`), and the unipotent radicals have the
   same image (`range_comp_unipotentRadical_eq_of_iso`). `P(𝔸)K = G(𝔸)` follows from
   `P_I(𝔸)K = G(𝔸)` (`IsIwasawaCompact.of_range_eq`).
2. Target. `StandardParabolicFamily.exists_standardConjugate` gives a rational point `s` and a
   standard `P_{I'}` with `P_{I'} ≅ P'` over the conjugated embedding `p' ≫ Int(s)`, compatibly with
   the Levi subgroups; `π₀ = eQ ≫ π' ≫ κ⁻¹` is the Levi projection of `P_{I'}`. Then
   `P_{I'} ≫ Int(s⁻¹)` and `P'` have the same image, which gives `P'(𝔸)K = G(𝔸)`
   (`IsIwasawaCompact.of_conjugate_map`).
3. Regularity. For given reflection data `D₀`, sufficiently `IsStandardRegularParameter`-regular
   parameters of `P_I` restrict to `r`-regular parameters of `P`. This combines
   `exists_isRegularParameter_of_coroot_lt` for the family presentation with
   `rootPresentationRegularityComparison` (two presentations of one parabolic subgroup). For the
   target, `eisensteinRegularityAmbientTransport` passes between `r'` and its conjugate
   `r'.compAmbientIso (Int s)`.
4. The chain. For `D₀`, `hρ₀`, `v₀` from the conclusion: the standard limit for `(P_I, P_{I'})` →
   `mono_reg` (step 3) → `of_iso_source` (step 1) → `of_conj_target` with `s⁻¹` (base `P_{I'}`) →
   `of_iso_target` (step 2) gives `TruncatedWavePacketPairLimit` for `(p, p')` with regularity
   `r.IsRegularParameter`, `r'.IsRegularParameter`. Applied to the data of the conclusion, this is
   the required limit.

The compact subgroup `K`, its maximality, the coverage `P₀(𝔸)K = G(𝔸)` and the projection property
of the truncation come directly from the hypothesis.

The main theorem raises `maxHeartbeats` to `1000000` for elaboration: the standard parabolic
subgroups of the family are definitionally those of `Standard`, and the proof passes data between
the two descriptions.

## Provenance

Lapid 2011, §2 (p. 311), fixes one minimal pair: a maximal split torus `T₀`, a minimal parabolic
subgroup `P₀` with Levi subgroup `M₀ = C_G(T₀)`, and a maximal compact subgroup `K` of `G(𝔸)` in
good position with respect to `M₀`; from there on `P` and `P'` denote standard parabolic subgroups.
In that standard setting, Lapid 2011, §8 (p. 328, through (18)), proves that the truncated inner
product of two wave packets converges to the right side of (4) (Proposition 2, p. 314): Lemma 9
(p. 327) reduces Proposition 2 to this limit, which follows from Proposition 1 (p. 313) and the
analysis of the integral (18). The hypothesis
`TruncatedStandardWavePacketLimitStatement` states this standard limit in the Library's
formulation, with holomorphic families of forms and the truncation parameter running along a fixed
ray `j • v₀`.

The passage from standard parabolic subgroups to arbitrary presented parabolic subgroups is the
derived reduction proved here. Its rational input is `StandardParabolicFamily.exists_standardConjugate`,
which combines two results of Borel–Tits, *Groupes réductifs* (1965): every rational parabolic
subgroup is conjugate over the base field to a standard one (§5.14, pp. 99–100), and two rational
Levi subgroups of one parabolic subgroup are conjugate by a rational point of its unipotent radical
(Corollary 3.14, p. 80).

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), §2.2, (2.1)
(p. 191), defines the Eisenstein series as the sum over `P(F) \ G(F)`. The scalar identity for a
rationally conjugated parabolic subgroup used by `of_conj_target` is the Library theorem
`IsIwasawaCompact.eisensteinSeries_conjugate_parabolic`. It follows by reindexing the rational
cosets of that series and comparing the heights for the same `K`. The remaining identifications of
forms, coefficients, measures and inner products are derived from the definitions and the
Library's transport lemmas.
