# Truncated Eisenstein families: uniform asymptotics and square integrability

Module `Langlands.Global.AdelicTruncatedEisensteinFamilyUniformAsymptoticsStatement`
states one proposition,
`Langlands.Global.LocalTruncatedEisensteinFamilyUniformAsymptoticsStatement`.
The file states the proposition and does not prove it.

## Sources

The sources are those of
[`LocalTruncatedEisensteinFamilyUniformInnerProductStatement`](AdelicTruncatedEisensteinUniformAsymptoticsStatement.md),
with the passages on the projection property, which concern only the omitted
part 1:

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
  pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (PDF page =
  printed page + 9): §2, p.312, Working hypothesis; §3, p.313, Proposition 1
  and formula (2); §4, Lemma 3, p.317; §6, Corollary 2, p.323; §7, (14),
  p.324, and the end of §7, p.325; §8, p.328.
- J. Arthur, *A trace formula for reductive groups II: applications of a
  truncation operator*, Compositio Math. 40 (1980), 87–121, registered as
  `arthur-1980-trace-formula-reductive-groups-II`: §1, Lemma 1.4, pp.95–96;
  for the omitted projection property, the Remark after Lemma 1.3, p.92.
- J. Arthur, *An introduction to the trace formula* (2005), in
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: §4, p.24 (a
  suitable maximal compact `K`); §13, Proposition 13.2, p.71; for the
  omitted projection property, Proposition 13.1 and the paragraph after its
  proof, pp.68–69.
- J. Arthur, *The trace formula in invariant form*, Ann. of Math. 114 (1981),
  1–74, registered as `arthur-1981-trace-formula-invariant-form`: §1, p.9,
  maximal compact subgroups admissible relative to `M_0`.

The Markdown of `LocalTruncatedEisensteinFamilyUniformInnerProductStatement`
gives the exact passages and explains how they give each part. Neither
retained part is printed in this form; both are derived there:

- Part 2 (below) is Lapid's formula (2) for each fixed central parameter,
  applied to the families shifted by the common central component `μ`. Its
  uniformity in `μ` in a compact set is derived from Lapid's proof:
  Lemma 3 (p.317) applied, as at the end of §7 (p.325), to the remainder for
  parameters in a compact set, with the exponents controlled by Corollary 2
  (p.323) and (14) (p.324). Lapid's §8 (p.328) uses this uniformity.
- Part 3 (below), the bound on `∫ |Λ^T E(i e(x))|²` uniform for `x` in a
  compact set, is derived from Arthur's fixed-level estimate (Arthur 1980,
  Lemma 1.4, pp.95–96, restated as Arthur 2005, Proposition 13.2 (b), p.71).
  It is applied to the family over the compact set at one common finite
  level, using the uniform weighted derivative bounds supplied by Lapid's
  Working hypothesis (p.312).
  The joint measurability is derived separately.

## The proposition

`LocalTruncatedEisensteinFamilyUniformInnerProductStatement` (module
`Langlands.Global.AdelicTruncatedEisensteinUniformAsymptoticsStatement`)
asserts, for every number field `F`, connected reductive `G`, maximal split
torus `i` and generic cocharacter `ν`, the existence of one subgroup `K` of
`G(𝔸)` with

- `IsMaximalCompactSubgroup F G K`;
- `IsIwasawaCompact (Standard.parabolicHom i ν ∅) K`, that is
  `P_0(𝔸)K = G(𝔸)` with `K` compact;
- `IsIwasawaCompact (Standard.parabolicHom i ν S.roots) K` for every standard
  index `S`;
- `AdelicSiegelFactors.IsPositiveTorusCompatible F G T i ν T₀ j K` for every
  Siegel setup `(T₀, j)` (`AdelicSiegelFactors.IsSiegelAlgebraicSetup`): the
  elements of `K` in `P_0(𝔸)` commute with the positive torus of the setup;

such that for all reflection data `D`, the bijectivity `hρ` and the proofs
`hK₀`, `hK` of the Iwasawa conditions a conjunction of three parts holds:

1. Arthur's projection property: beyond a threshold, the norm-one truncation
   on `G(F) \ G(𝔸)¹` and the full truncation on `G(F) \ G(𝔸)` with respect to
   `K` satisfy `IsOrthogonalL2Extension` for the quotient Haar measures;
2. Lapid's asymptotic formula (Proposition 1, formula (2)) for holomorphic
   families of inducing vectors, on compact sets of pairs of imaginary
   parameters with equal central components;
3. for holomorphic families and compact sets of imaginary parameters in the
   domain of holomorphy, beyond a threshold, joint almost everywhere strong
   measurability of `(x, y) ↦ Λ^T E(i e(x))(y)` and a bound on
   `∫ |Λ^T E(i e(x))|²` uniform in `x`.

`LocalTruncatedEisensteinFamilyUniformAsymptoticsStatement` is the same
proposition without part 1. Its binders, the four conditions on `K`, the
binders `D`, `hρ`, `hK₀`, `hK`, and parts 2 and 3 are copied word for word
from `LocalTruncatedEisensteinFamilyUniformInnerProductStatement`; the
conclusion after `∀ D hρ hK₀ hK` is the conjunction of parts 2 and 3. So the
proposition says: there is one maximal compact `K` with these four properties
for which Lapid's uniform asymptotic formula and the locally uniform `L²`
bounds of truncated holomorphic families hold together. The meaning of every
hypothesis and conclusion, the normalizations and the reasons the sources give
parts 2 and 3 for a suitable (admissible) `K` are in the Markdown of
`LocalTruncatedEisensteinFamilyUniformInnerProductStatement` and of
`LocalTruncatedEisensteinFamilyInnerProductStatement`.

## Why part 1 is left out

Part 1 is a property of every compact `K` with `P_0(𝔸)K = G(𝔸)`: the
Library's `iwasawaTruncationIdempotent` (module
`Langlands.Global.ArthurTruncationIdempotenceProof`) and
`truncationSelfAdjoint` (module `Langlands.Global.ArthurTruncationSelfAdjointProof`)
are stated for every such `K` and all reflection data, and the module
[`Langlands.Global.AdelicTruncatedEisensteinUniformAsymptoticsReduction`](AdelicTruncatedEisensteinUniformAsymptoticsReduction.md)
derives the projection property from them for every such `K`
(`exists_isOrthogonalL2Extension_of_isIwasawaCompact`). In the sources, which
work over `ℚ`, Arthur 2005, Proposition 13.1 (b), (c), pp.68–69, states the
pointwise identities on the norm-one quotient `G(ℚ) \ G(𝔸)¹`; the sentence
after its proof, p.69, asserts the projection on `L²(G(ℚ) \ G(𝔸))`, the full
quotient; and Arthur 1980, the Remark after Lemma 1.3, p.92, asserts it on
`L²(G(ℚ) \ G(𝔸)¹)`. Part 1 has both versions over a number field `F`; the
reduction module derives them from the pointwise identities. Parts 2 and 3, on the
other hand, are proved in the sources for a suitable maximal compact subgroup
(Arthur 2005, §4, p.24, citing Arthur 1981, p.9), a condition that the Library
does not express as a predicate on `K`; the existential over `K` keeps them
together for one such `K`. With part 1 available for every `K`, the
proposition here is what remains of
`LocalTruncatedEisensteinFamilyUniformInnerProductStatement`:
`localTruncatedEisensteinFamilyUniformInnerProduct_of_asymptotics` in the
reduction module proves that this proposition implies it.
