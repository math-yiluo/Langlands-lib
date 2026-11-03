# The upper bound of Waldspurger I.1 (5) for `GL_n`

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.DoubleCosetMeasureGL`,
namespace `Langlands.HarishChandraSchwartz`. It imports the published modules
`DoubleCosetMeasure` (`doubleCosetIndex`, `translate_smul_eq_iff`, `measure_doubleCoset`;
through it `conjSubgroup` of `Translations`) and `Langlands.Group.GL.CartanCellCountProof`
(Worker 23: `cartanCellCount`, the proof of `CartanCellCountStatement`, with the definitions
`maximalCompact`, `representative` and `delta` of `Langlands.Group.GL.CartanQuotientDefinitions`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. I.1 (5), printed p. 241 (PDF p. 7): there are `C_1, C_2 > 0` with
`C_1 δ_0(m)^{-1} ≤ mes(K m K) ≤ C_2 δ_0(m)^{-1}` for `m ∈ M̄_0^+`, `δ_0 = δ_{P_0}`. This module
treats the upper bound for `GL_n`; its proof differs from the article's (it uses Worker 23's
cell count rather than the factorization of `[H : mHm^{-1} ∩ H]`).

## Scope

This is a `GL_n`-specific instance. `F` is a `p`-adic field (`PadicField p`) with topological
data `T`, `K = maximalCompact T n` is the image of `GL_n(O_F)` in `GL_n(F)`, and for
`λ : Fin n → ℤ` the element `representative T λ` is the diagonal matrix `a(λ)` with entries
`ϖ^{λ_i}` for the uniformizer `ϖ` of `T`. `delta T λ = q^{-deg λ}`, with
`deg λ = Σ_{i < j} (λ_i - λ_j)` and `q` the residue cardinality, is the modulus of the upper
Borel subgroup at `a(λ)`; for antitone `λ` (Waldspurger's `M̄_0^+` with his sign convention
`q^{-⟨χ, H(g)⟩} = |χ(g)|`) it is `δ_0(a(λ))`. The measure result holds for any measurable
structure on `GL_n(F)` with measurable multiplication in which `K` is measurable (hypothesis
`hK`), and any left invariant measure `μ`; no Haar property and no normalization is needed.
The lower bound of I.1 (5) is not treated.

## Definitions

- `GLDoubleCosetIndexBound T n`: there is `c` such that for every antitone `λ`, the index
  `doubleCosetIndex K a(λ) = [K : K ∩ a(λ) K a(λ)^{-1}]` is finite (nonzero in Mathlib's
  convention) and at most `c δ(λ)^{-1}`.

## Results

- `doubleCosetIndex_le_of_cover` (any group): if every `k_1 g k_2` with `k_1, k_2 ∈ K` equals
  `r g k` for some `r` in a finite set `R` and some `k ∈ K` (`hR`), then
  `[K : K ∩ g K g^{-1}]` is finite and at most the cardinality of `R`.
- `glDoubleCosetIndexBound`: `GLDoubleCosetIndexBound T n` holds, for every `p`, `F`, `T`, `n`.
- `exists_measure_doubleCoset_le_delta`: there is `c` with
  `μ(K a(λ) K) ≤ c δ(λ)^{-1} μ(K)` for every antitone `λ`.

## Proof notes

For each class `q` in `K / (K ∩ g K g^{-1})`, the cover gives `r(q) ∈ R` and `k ∈ K` with
`q g = r(q) g k`, so the left cosets `(q g) K` and `(r(q) g) K` agree; since the left cosets
`(q g) K` of distinct classes are distinct (`translate_smul_eq_iff`), `q ↦ r(q)` is injective
and the quotient is finite with at most `|R|` elements. For `GL_n`, `cartanCellCount` supplies
`R` with `|R| ≤ c δ(λ)^{-1}`, and `measure_doubleCoset` turns the index bound into
`μ(K a K) = [K : K ∩ a K a^{-1}] μ(K) ≤ c δ(λ)^{-1} μ(K)`.

## Open obligations

The lower bound `C_1 δ_0(m)^{-1} ≤ mes(KmK)` for `GL_n` and I.1 (5) for general reductive
groups are not proved here.
