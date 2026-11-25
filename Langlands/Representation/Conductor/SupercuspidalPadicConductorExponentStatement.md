# The JPSS conductor theorem for supercuspidal representations over p-adic fields

This module, in
namespace `Langlands.Conductor`, defines one proposition,
`SupercuspidalPadicConductorExponentStatement`, with universe parameters `uF uV`.
It proves nothing.

The proposition is the published `Conductor.ConductorExponentStatement`
(module `Langlands.Representation.Conductor.EssentialStatement`) with two changes:

- the field is the carrier `K.Carrier` of a p-adic field `K : PadicField.{uF} p`
  with its canonical topology, valuation and local-field structure, instead of an
  arbitrary nonarchimedean local field;
- the representation `π` is in addition supercuspidal
  (`GeneralLinear.IsSupercuspidal π`, module
  `Langlands.Representation.Classification.Supercuspidal`).

Everything else (normalizations, epsilon relation, levels, conclusion) is the same.

## Sources

**Jacquet, Piatetski-Shapiro and Shalika, *Conducteur des représentations du
groupe linéaire*, Math. Ann. 256 (1981), 199-214** (literature ID
`jpss-1981-conductor`; PDF page = printed page - 198).

- **§(5.1), Théorème, printed page 211 (PDF page 13).** `π` is an irreducible
  generic representation of `G_r`, `ψ` has exponent `0`, and `m` is the integer
  with `ε_π(X, ψ) = C X^m` (display (1)). (i) `m ≥ 0`. (ii) For an integer
  `a > 0`, `K_r(a)` is the subgroup of `K_r` of matrices `[[h, v], [u, x]]` with
  `h ∈ K_{r-1}`, `x ∈ 𝔒^×`, `x ≡ 1 mod 𝔓^a`, `u ≡ 0 mod 𝔓^a`, and
  `K_r(0) = K_r`; the essential vector is invariant under `K_r(m)` and the space
  of vectors fixed by `K_r(m)` has dimension one. (iii) If `a ≥ 0` and `π` has a
  nonzero vector fixed by `K_r(a)`, then `a ≥ m`.

**Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions*,
Amer. J. Math. 105 (1983), 367-464** (literature ID `jpss-1983-rankin-selberg`;
the scan has one cover page, so PDF page = printed page - 365). These two
results are not used in the statement. They are the proof route sketched in
"Proof plan" below.

- **Theorem (2.7)(ii), printed pages 390-391 (PDF pages 25-26).** `π` and
  `π'` are representations of Whittaker type of `G_r` and `G_t`, with
  `W ∈ 𝒲(π; ψ)` and `W' ∈ 𝒲(π'; ψ̄)`. The integrals are rational functions of
  `q^{-s}`. If `r = t`, the integrals `Ψ(s, W, W', Φ)` span a fractional ideal
  `ℂ[q^{-s}, q^s] L(s, π × π')` of `ℂ[q^s, q^{-s}]`, and
  `L(s, π × π') = P(q^{-s})^{-1}` with `P ∈ ℂ[X]` and `P(0) = 1`. If
  `t ≤ r - 1`, a similar factor `L(s, π × π')`, independent of `j`, generates
  the ideal spanned by the integrals `Ψ(s, W, W'; j)`.
- **§(8.1), Proposition (i), printed page 443 (PDF page 78).** If `π` is an
  irreducible supercuspidal representation of `G_r`, `σ` a representation of
  Whittaker type of `G_t`, and `r > t`, then `L(s, π × σ) = 1`.

## The statement

`SupercuspidalPadicConductorExponentStatement` quantifies over a prime `p` and a
p-adic field `K : PadicField.{uF} p`. Through `letI` it gives `K.Carrier` the
topology, the valuative relation and the `IsNonarchimedeanLocalField` structure
of `K.canonicalTopologicalData` (module `Langlands.LocalField.Canonical`). This
is the convention of the Library's other p-adic statements, for example
`SupercuspidalKirillovStatement` and `RankinSelberg.SupercuspidalUnequalRankLFactorStatement`.
With these structures it takes, exactly as `ConductorExponentStatement` does:

- instances `T2Space K.Carrier` and `TotallyDisconnectedSpace K.Carrier`, and
  Borel measurable structures on `K.Carrier`, `GL_1(K.Carrier)`, its upper
  unipotent subgroup and `N_1 \ GL_1(K.Carrier)`;
- `q`, the cardinality of the residue field of the valuation ring;
- an absolute value `abv` with `abv ϖ = q⁻¹` for a uniformizer `ϖ` and
  `abv x = 1` whenever the valuation of `x` is `1`;
- `ψ` with `HasIntegerConductor ψ` (JPSS's exponent `0`) and an additive Haar
  measure `ν` with `IsSelfDual ψ ν`;
- `n`, a complex vector space `V` in universe `uV`, and a representation `π` of
  `GL_(n+1)(K.Carrier)` on `V` with `IsGeneric ψ n π` (irreducible, admissible,
  with a nonzero `ψ`-Whittaker functional) and `IsSupercuspidal π`.

The conclusion is that there are `c : ℂˣ` and `m : ℕ` with

- `IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m)`: the epsilon
  factor of `π` against the trivial character of `GL_1` is `c q^{-ms}`;
- `IsNewvectorConductor π m`: `levelFixedVectors π m` is nonzero and
  `levelFixedVectors π b = 0` for every `b < m`;
- `Module.finrank ℂ (levelFixedVectors π m) = 1`.

As in `ConductorExponentStatement`, taking `m : ℕ` is part (i), the dimension
claim is part (ii), and the minimality clause of `IsNewvectorConductor` is
part (iii). `levelFixedVectors π a` is the space fixed by the published
`levelSubgroup`, which is JPSS's `K_r(a)`; `EssentialStatement.md` explains the
comparison.

The `T2Space` and `TotallyDisconnectedSpace` hypotheses do not restrict the
statement: they hold for the canonical topology (for the first, see
`PadicField.TopologicalData.fieldT2` in `Langlands.LocalField.Topology`). They
are kept as binders so that the statement has the binders of
`ConductorExponentStatement`.

## Provenance and relation to the source

The statement is derived. It is JPSS 1981, §(5.1), Théorème (i)-(iii),
specialized to supercuspidal `π` over a p-adic field. It is a special case of
`ConductorExponentStatement`: instantiate that statement at
`F := K.Carrier` with the canonical structures and forget the hypothesis
`IsSupercuspidal π`. The interpretation remarks of `EssentialStatement.md`
("Interpretation and gaps") apply unchanged. In particular, the epsilon factor
is the JPSS 1983 pair factor `ε(s, π × 1, ψ)` of `IsPairEpsilonFactor`, not the
Godement-Jacquet factor that JPSS 1981 use, and the relation is the one for the
self-dual measure `ν`.

The restriction removes the hard case of the source's argument. For `r ≥ 2`, a
supercuspidal `π` has L-factor `1` (for the pair factor `L(s, π × 1)` this is
JPSS 1983, §(8.1), Proposition (i), with `t = 1`). `EssentialStatement.md`
records Jacquet's 2012 correction, Remark 1 (printed page 523): the 1981
existence proof of the essential vector is correct when `L(s, π) = 1`.

## Why the Henniart route needs only this case

The Henniart route uses `ConductorExponentStatement` at one place only:
`Henniart.Extension.exists_newvectorConductor_of_pairEpsilon`
(module `Langlands.Correspondence.HenniartConductorFinitenessProof`). There it
calls `Conductor.genericConductor_isNewvectorConductor_of_conductorExponentStatement`
(module `Langlands.Representation.Conductor.GenericEpsilonConductor`) for
`A.obj.representation`, where `A : GeneralLinear.SupercuspidalRep` is a
supercuspidal representation of `GL_(k+1)(K.Carrier)` and `K` is a p-adic field
with its canonical structures. The supercuspidal hypothesis is
`A.property.2`. So this statement supplies everything the route takes from
`ConductorExponentStatement`. The companion reduction statement
`Henniart.Extension.SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement`
(module `Langlands.Correspondence.HenniartSupercuspidalConductorReductionStatement`)
states this replacement for the three-input form of the route.

## Closure under the inverse-transpose twist

The published reduction `Conductor.conductorExponentStatement_of`
(module `Langlands.Representation.Conductor.EssentialConductorReduction`) applies
its essential-vector hypothesis both to `(ψ, π)` and to
`(ψ.scale (-1), inverseTransposePullback π)`. Here
`Whittaker.inverseTransposePullback π` is by definition
`π.comp (inverseTranspose (n + 1) F).toMonoidHom`. The hypotheses of this
statement are preserved by that twist:

- `Conductor.isGeneric_inverseTransposePullback`
  (module `Langlands.Representation.Conductor.EssentialDualSetup`):
  `IsGeneric ψ n π → IsGeneric (ψ.scale (-1)) n (inverseTransposePullback π)`;
- `Conductor.hasIntegerConductor_scale_neg_one` (same module):
  `HasIntegerConductor ψ → HasIntegerConductor (ψ.scale (-1))`;
- `GeneralLinear.isSupercuspidal_comp_inverseTranspose`
  (module `Langlands.Representation.Classification.SupercuspidalInverseTranspose`):
  `IsSupercuspidal ρ → IsSupercuspidal (ρ.comp (inverseTranspose n F).toMonoidHom)`.

So a version of that reduction for one representation at a time, applied within
the class of supercuspidal generic representations, never leaves the class.

## Proof plan

This module proves nothing. The theorem
`Langlands.Conductor.supercuspidalPadicConductorExponent`, in
[`SupercuspidalPadicConductorExponentProof`](SupercuspidalPadicConductorExponentProof.md),
proves the statement; that page describes the proof as carried out. The route
sketched for it is:

- **Rank one** (`n = 0`). `Conductor.conductorExponent_rankOne_of_localTate`
  (module `Langlands.Representation.Conductor.RankOneTateReduction`) gives the
  conclusion from `GodementJacquet.LocalTateConductorStatement`, which is proved
  as `GodementJacquet.localTateConductor` (Tate's thesis).
- **Rank at least two.** By JPSS 1983, §(8.1), Proposition (i),
  `L(s, π × σ) = 1` for `σ` of Whittaker type of smaller rank. The Library
  proves this for p-adic fields with canonical structures as
  `RankinSelberg.supercuspidalUnequalRankLFactor`. By JPSS 1983, Theorem
  (2.7)(ii), the integrals then span `ℂ[q^{-s}, q^s]`, so a finite combination
  of them equals `1`; the proof of `supercuspidalUnequalRankLFactor` already puts
  `1` in the span (`RankinSelberg.IsNormalizedGenerator.eq_one_of_laurentValues`).
  With `P = 1` this is expected to give the hypotheses of
  `Conductor.exists_isEssentialVector_of_jpss`
  (module `Langlands.Representation.Conductor.EssentialExistenceReduction`) for
  `π` and for its inverse-transpose twist. A version of
  `conductorExponentStatement_of` for one representation at a time then gives
  the conclusion. `Langlands.supercuspidalKirillov` (the supercuspidal Kirillov
  model) is also available.

The canonical structures are chosen because the published supercuspidal
results above are stated for them. A statement with arbitrary local-field
structures on `K.Carrier` would also require showing that every such structure
is the canonical one.
