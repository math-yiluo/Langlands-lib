# Absolute upper ramification in either characteristic

This module is the characteristic-free generalization of the
published absolute construction of `Herbrand.Absolute`. The declarations are in
`Langlands.Ramification.Local`. The finite input is the actual integer-ring
filtration in `Herbrand.GeneralFinite`.

## Sources and meaning

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg, GTM 67,
Springer (1979), Chapter IV, §3, Remark 1 following Proposition 14, printed
p.75 (PDF p.82), defines upper ramification groups of an infinite Galois
extension as the inverse limit of the finite Galois upper groups. The
registered source is `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The finite real-index and upper-index conventions are on pp.73–74
(PDF pp.80–81). Those pages and the image of p.75 were consulted.
Serre's registered author corrections, `serre-book-corrections-2019`, PDF
pp.2–3, correct the phi glyphs at p.74 line −7 and p.75 Lemma 5; they do not
alter the cited infinite-extension definition.

Inside the actual automorphism group of a separable closure, compatible
restrictions already belong to one automorphism. Consequently the inverse
limit condition is the intersection of the preimages of the finite upper
groups. This construction does not assume that restriction maps each
absolute upper group onto its finite counterpart.

The named wild subgroup implements the closed positive upper limit
requested in the operator plan, `operator-external-inputs-plan-2026-11-16`,
§4.2, lines 513–570. The plan source is
`Operator note - Formalizing the large external inputs of the local
Langlands correspondence for GL_n (16 November 2026)/external-inputs-plan.tex`
under the project's literature directory. The registered directory fingerprint
is `c429afd5b4f28270a0619b3292f8825a9bfa77c3d842ac3a2a81fc2042cc0463`;
the cited LaTeX file has SHA256
`816bb31b7194dea7eb38a661bf53ae670c17a2ec0bd7d1e7e4bcfa2c94aad03a`.
The closure is taken in the
actual Krull topology. Identification with the intersection of finite
first lower groups is a separate arithmetic statement,
`Local.AbsoluteUpperWildInertia` in `Herbrand.LocalAbsoluteStatement`; its
p-adic case is proved as `absoluteUpperWildInertia` in
`Herbrand.InertiaProof`. The relevant finite
source is Serre IV §2, Corollaries 1–4 to Proposition 7, pp.67–68.

## Parameters and finite integer rings

The spectral construction has three independently sized fields:

- `K₀` has a complete, nontrivial, ultrametric norm and is locally compact.
  Its specified valuative relation must agree with norm comparison, as
  expressed by `hbase`.
- `K` is a finite extension of `K₀`.
- `Ω` is a separable closure of `K`, with the specified algebra structures
  forming the tower `K₀ → K → Ω`.

For every `L : FiniteGaloisIntermediateField K Ω`, finite dimensionality
over `K₀` follows by the tower through `K`. Its integer ring is precisely
the ring belonging to `LocalField.canonicalTopologicalData K₀ L hbase`.
Thus all finite levels use the spectral norm extending the same norm
on `K₀`; no arbitrary realization or normalization is an extra parameter.
The auxiliary finite-dimensional instance is private.

`absoluteFiniteRestriction K Ω L` is the continuous group homomorphism
whose underlying map is Mathlib's `AlgEquiv.restrictNormalHom`. Continuity
is `InfiniteGalois.restrictNormalHom_continuous`. This helper works for any
ambient extension, without requiring that it be a separable closure.
Both its source `Ω ≃ₐ[K] Ω` and target `Gal(L/K)` carry their existing
Krull topologies. The target is finite and discrete.

`absoluteUpperRamificationGroup K₀ K Ω hbase v` is the subgroup infimum
over all such `L` of the comaps of
`canonicalUpperRamificationGroup K₀ L hbase K v`.
The real parameter is unrestricted. As in the published finite layer,
lower numbering uses `ceil`, upper numbering evaluates at the inverse
Herbrand function, and the full group is retained below −1.

`wildInertia K₀ K Ω hbase` is
`(⨆ (v : ℝ) (_ : 0 < v), absoluteUpperRamificationGroup K₀ K Ω hbase v).topologicalClosure`.
The positive-index family is directed by choosing the smaller of two
positive indices, so the supremum is the union interpreted as a subgroup.
The implemented definition uses the subgroup supremum directly.

## Elementary proofs

The membership theorem expands infimum and comap membership. Its `_lower`
variant unfolds each finite upper group to the integer lower group at
`ceil(herbrandPsi ... v)`. The bound at one finite level is `iInf_le`;
image containment follows by the map/comap adjunction.

Normality follows by pulling back the finite normal subgroups and taking
their intersection. Closedness rewrites the subgroup carrier as an
intersection: each finite target subset is closed and restriction is
continuous. Antitonicity follows from the finite upper filtration at each
restriction. The −1 endpoint follows from the finite endpoint and subgroup
lattice simplification, and antitonicity gives the endpoint for every
smaller real parameter.

Wild normality uses normality of the two indexed suprema and
`Subgroup.is_normal_topologicalClosure`. These are elementary
construction proofs. No finite-image equality, inertia-at-zero theorem,
left continuity, or description of wild inertia by finite lower groups is
asserted.

## Nonarchimedean local fields and characteristic

For `[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`, `localAbsoluteUpperRamificationGroup K Ω`
and `localWildInertia K Ω` specialize the spectral construction to
`K₀ = K`. They install the published
`LocalGalois.localNormedField K`, its completeness theorem and its
ultrametric theorem locally. Compatibility with the specified valuative
relation follows from `LocalGalois.localNormedField_le` and the canonical
valuation's comparison equivalence. The adapter preserves the supplied
topology. No global norm or topology is replaced.

The only implicit characteristic-zero input at the old absolute level
was the use of `AlgebraicClosure F.Carrier` as a separable closure:
`PadicField` has characteristic zero, hence is perfect, and Mathlib
supplies `IsSepClosure.of_isAlgClosure_of_perfectField`. Here the closure
is instead an arbitrary specified `Ω` with `[IsSepClosure K Ω]`.
Finite Galois subextensions already carry separability and normality by
their type. Neither the restriction construction, the spectral
integer rings, nor the elementary intersection and closure proofs need
perfectness or any characteristic hypothesis.

## In-place specialization table

The p-adic declarations remain in `Herbrand.Absolute` with their original
names and types. They unfold to the general definitions at
`K₀ = Padic p`, `K = F.Carrier`, `Ω = AlgebraicClosure F.Carrier`;
norm/valuation compatibility is the existing p-adic norm comparison.
The finite canonical constructor and finite groups specialize by
unfolding as well. There is no comparison theorem between two theories.

| General declaration in `Langlands.Ramification.Local` | P-adic specialization in `Langlands.Ramification.Padic` |
| --- | --- |
| `absoluteFiniteRestriction K Ω L` | `absoluteFiniteRestriction F L` |
| `absoluteUpperRamificationGroup K₀ K Ω hbase v` | `absoluteUpperRamificationGroup F v` |
| `mem_absoluteUpperRamificationGroup_iff` | Same leaf name |
| `mem_absoluteUpperRamificationGroup_iff_lower` | Same leaf name |
| `absoluteUpperRamificationGroup_le_comap` | Same leaf name |
| `absoluteUpperRamificationGroup_map_restriction_le` | Same leaf name |
| `absoluteUpperRamificationGroup_normal` | Same leaf name |
| `absoluteUpperRamificationGroup_isClosed` | Same leaf name |
| `absoluteUpperRamificationGroup_antitone` | Same leaf name |
| `absoluteUpperRamificationGroup_neg_one` | Same leaf name |
| `absoluteUpperRamificationGroup_of_le_neg_one` | Same leaf name |
| `wildInertia K₀ K Ω hbase` | `wildInertia F` |
| `wildInertia_normal` | Same leaf name |

The `localAbsoluteUpperRamificationGroup_*` elementary lemmas and
`localWildInertia_normal` are the core lemmas specialized to the local
norm adapter. The p-adic field-packaging helpers and abelianized image
remain in the existing module; their types and meanings are unchanged.
All published statement files retain their text.
