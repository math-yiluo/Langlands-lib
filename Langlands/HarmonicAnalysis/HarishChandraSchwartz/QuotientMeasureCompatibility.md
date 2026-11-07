# Compatibility of Haar measures on `G` and on `G / A` along an open subgroup

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.QuotientMeasureCompatibility`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceFamilyScalar` (Worker 249), for
  `measurable_quotientMk` (measurability of `G → G / A`);
- `Mathlib.MeasureTheory.Measure.Haar.Unique`, for `isMulLeftInvariant_eq_smul` and
  `haarScalarFactor` (uniqueness of Haar measure on a locally compact second countable group);
- from Mathlib also `IsHaarMeasure.comap` (a Haar measure restricts to a Haar measure on an open
  subgroup), `MeasurableEmbedding.map_comap`, `MeasurableEmbedding.comap_apply`,
  `Topology.IsOpenEmbedding.measurableEmbedding`, `IsOpen.locallyCompactSpace`,
  `TopologicalSpace.Subtype.secondCountableTopology`, `exists_compact_subset`,
  `IsCompact.elim_finite_subcover`, `measure_smul`, `measure_biUnion_finset_le`,
  `QuotientGroup.isOpenMap_coe`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. The quoted text carries no overline (checked on the rendered PDF page 6).

- I.1, printed p. 240 (PDF p. 6): "On munit tout sous-groupe algébrique fermé `H` de `G` de la
  mesure invariante par translations à gauche pour laquelle `mes(H ∩ K) = 1`. On en déduit une
  distribution positive (une 'mesure') sur l'espace des fonctions `f : G → ℂ` localement
  constantes et à support compact mod `H`, vérifiant `f(hg) = δ_H(h) f(g)` [...]".
- Proof of Proposition III.7.1, printed p. 274 (PDF p. 40): the integral over `G` is decomposed
  along `G¹` and compared with the integral over `A_G \ G`, through the finite group
  `G¹ A_G \ G`.

The Library's `TraceFamilyScalar`, `OrbitPolynomialOperator` and `TemperedTwistIntegrability`
replace these normalizations by the hypothesis `hcompat`: for an open subgroup `N` (`ker p`, in
place of `G¹`), the image in `G / A` of a Haar measure `μ` of `G` restricted to `N` is a constant
`m` times a Haar measure `ν` of `G / A` restricted to the image of `N`. This module defines that
relation (`IsQuotientCompatible`) and proves that a constant `m ≠ 0, ∞` exists whenever `A ∩ N`
is compact. The existence statement and its proof are derived; Waldspurger fixes the measures and
does not state this comparison. The value of `m` is not computed.

## Scope and hypotheses

`G` is a group with a topology and a Borel measurable structure, `μ` a measure on `G`, `A` a
normal subgroup, `G ⧸ A` with a Borel measurable structure, `ν` a measure on `G ⧸ A`, `N` a
subgroup of `G`.

- `IsQuotientCompatible μ A ν N m`: no further hypothesis.
- `map_mk_restrict_apply`: a measurable `E ⊆ G ⧸ A`; it uses neither the group topology nor
  normality.
- `map_mk_restrict_smul`: `G` a topological group, `μ` left invariant, `n ∈ N`, `E` measurable.
- `map_mk_restrict_lt_top`: `G` a locally compact topological group, `μ` a Haar measure,
  `N` open, `A ∩ N` compact (`hAN`), `K ⊆ G ⧸ A` compact and contained in the image of `N`.
- `exists_isQuotientCompatible`: `G` a locally compact second countable topological group, `μ`
  a Haar measure on `G`, `ν` a Haar measure on `G ⧸ A`, `N` open (`hN`) and `A ∩ N` compact
  (`hAN`).

In Waldspurger's setting `N = G¹` is open and `A_G ∩ G¹` is compact (the Library's
`isCompact_splitComponent_inf_commonNormKernel` for the actual group); this module does not make
that specialization.

## Definitions

- `IsQuotientCompatible μ A ν N m`: `Measure.map mk (μ.restrict N) = m • ν.restrict (mk '' N)`,
  the form of the hypothesis `hcompat` with `N = ker p`.

## Results

- `map_mk_restrict_apply`: `(mk_* μ|_N)(E) = μ(mk⁻¹(E) ∩ N)`.
- `map_mk_restrict_smul`: `mk_* μ|_N` is invariant under translation by the image of `n ∈ N`.
- `map_mk_restrict_lt_top`: `mk_* μ|_N` is finite on compact subsets of the image of `N`.
- `exists_isQuotientCompatible` (**existence of the compatibility constant**): there is
  `m ≠ 0, ∞` with `IsQuotientCompatible μ A ν N m`.

## Proof notes

1. `map_mk_restrict_smul`: `mk⁻¹(n̄ E) = n mk⁻¹(E)` and `n N = N`, so
   `mk⁻¹(n̄ E) ∩ N = n (mk⁻¹(E) ∩ N)`, which has the same `μ`-measure.
2. `map_mk_restrict_lt_top`: choose a compact `V ⊆ N` with `1` in its interior. Finitely many
   images `mk(g · int V)`, `g ∈ N`, cover `K`; their union `E` is open, and
   `mk⁻¹(E) ∩ N ⊆ ⋃ (g V)(A ∩ N)`, a finite union of compact sets.
3. `exists_isQuotientCompatible`: `U = mk(N)` is an open subgroup of `G ⧸ A`, a locally compact
   second countable group. The measures `λ = mk_* μ|_N` and `ν` pulled back to `U` are left
   invariant (step 1), the first is finite on compacts (step 2) and the second is a Haar
   measure (`IsHaarMeasure.comap`). Haar uniqueness on `U` (`isMulLeftInvariant_eq_smul`) gives
   `λ|_U = c ν|_U` with `c = haarScalarFactor`; pushing forward along the inclusion
   (`MeasurableEmbedding.map_comap`) and using that `λ` lives on `U` gives `λ = c ν|_U`. Then
   `c ≠ ∞` since `c` is in `ℝ≥0`, and `c ≠ 0` since `λ(G ⧸ A) = μ(N) > 0` (`N` is open).
