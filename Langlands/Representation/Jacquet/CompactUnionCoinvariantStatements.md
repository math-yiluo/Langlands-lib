# Coinvariants: the Haar example and unions of compact subgroups (Renard III.2.9): statements

Module `Langlands.Representation.Jacquet.CompactUnionCoinvariantStatements`. Namespace
`Langlands.Jacquet`. Universe parameters `uH` (the group) and `uV` (the representation
space).
The module contains four **statements**, the `Prop`-valued definitions
`HaarCoinvariantsDimensionStatement`, `CompactSubgroupFilteredUnionStatement`,
`CompactAveragingRelationStatement` and `CoinvariantSubrepresentationRelationsStatement`. It
proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The published map
[iii2-hecke-induction](../../../notes/renard/iii2-hecke-induction.md) (Task 5296) lists these
III.2.9 items as gaps:

- the Haar Example: "an exact dimension-one declaration for this coinvariant carrier was not
  located";
- the Definition of a filtered increasing union and the following Remark: "the exact source
  filtered-union definition and its compact-containment implication are not separately
  packaged". The published `JL.IsLimitOfCompactSubgroups`
  ([LocalizationExactnessStatement](LocalizationExactnessStatement.md)) is the conclusion of
  the Remark, used as a hypothesis;
- the Proposition: the published `JL.mem_relations_iff_compact` "detect[s] a relation inside a
  single compact subgroup" but does "not state the literal averaging-kernel criterion";
- the Corollary: "its literal subrepresentation equality and the bridge from the source's
  filtered-union wording are not separately packaged".

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read III.2.9, printed pp.78–80 / PDF pp.84–86:

> Soient `H` un groupe t.d. et `(τ, E)` une représentation de `H`. On note `E(H, τ)` le
> sous-espace de `E` engendré par les vecteurs `(τ(h) · v − v)`, `v ∈ E`, `h ∈ H`. L'espace
> coinvariant est par définition le quotient `E_{H,τ} = E / E(H, τ)`. […]
>
> Exemple. Le théorème d'existence et d'unicité de la mesure de Haar sur un groupe t.d. `G`
> peut se reformuler en disant que `dim(𝒟(G)_{G,l}) = 1`.
>
> Définition. Soit `X` un ensemble et `(X_i)_{i∈I}` une famille de parties de `X`. On dit que
> `X` est réunion filtrée croissante des `X_i` si `X = ⋃_{i∈I} X_i` et pour tout
> sous-ensemble fini `J ⊂ I`, il existe `k ∈ I` tel que `⋃_{i∈J} X_i ⊂ X_k`.
>
> Remarque. Supposons que `H` soit un groupe t.d. et que `H` soit la réunion filtrée
> croissante de ses sous-groupes compacts. Il est alors clair que pour toute partie compacte
> `C` de `H`, il existe un sous-groupe compact `K` de `H` qui contient `C`. (Recouvrir `C` par
> une famille finie d'ouverts de la forme `g_j K_j`, […] et prendre `K` contenant tous les
> `g_j` et tous les `K_j`).
>
> Proposition. Supposons que `H` soit la réunion filtrée croissante de ses sous-groupes
> compacts. Soit `(τ, E)` une représentation lisse de `H`. Alors `E(H, τ)` est l'espace des
> vecteurs `v ∈ E` tels qu'il existe un sous-groupe compact `K` de `H` vérifiant
> `τ(e_K) · v = 0`.
>
> Démonstration. La proposition découle de la proposition III.1.5, qui traite le cas où `H`
> est lui-même compact.
>
> Corollaire. Avec les hypothèses de la proposition ci-dessus, si `E′` est une
> sous-représentation de `E`, alors `E′(H, τ) = E(H, τ) ∩ E′` et si
> `0 → E′ → E → E″ → 0` est une suite exacte dans `M(H)`, alors
> `0 → E′_{H,τ′} → E_{H,τ} → E″_{H,τ″} → 0` est exacte. En particulier, le foncteur `j_H`
> défini dans la remarque 2 ci-dessus est exact dès que `H` est réunion de ses sous-groupes
> ouverts compacts.

## Published objects used

- `relations ρ N` and `Coinvariants ρ N`: the span `E(N, ρ)` of the vectors `ρ(n) v − v`,
  `n ∈ N`, and the quotient by it ([Coinvariants](Coinvariants.md)). Here `N = ⊤`.
- `HarmonicAnalysis.GroupAction.leftTests`: the left regular representation `l` of `G` on the
  test functions `𝒟(G) = SchwartzBruhat G`
  ([GroupAction](../../HarmonicAnalysis/GroupAction.md)).
- `Hecke.fixedProjection μ ρ hρ K hK`: the action `ρ(e_K)` of the normalized indicator
  `e_K = μ(K)⁻¹ 1_K` of a compact open subgroup `K`, with values in the `K`-fixed vectors
  ([ActionProjection](../Hecke/ActionProjection.md)). It does not depend on `μ`.
- `isSmooth_comp`: restriction of a smooth representation along a continuous homomorphism
  is smooth.
- Mathlib's `Subrepresentation τ`, with `toSubmodule` and `toRepresentation`.

## The statements

Let `H` be a t.d. group (Hausdorff, locally compact, totally disconnected). "`H` is the
filtered increasing union of its compact subgroups" is the source's Definition, applied to
the family of compact subgroups of `H`: their union is `H`, and every finite set of compact
subgroups is contained in a single compact subgroup.

**`HaarCoinvariantsDimensionStatement`** (Example). For a t.d. group `G`, the coinvariants of
`l` on `𝒟(G)` have dimension `1`.

**`CompactSubgroupFilteredUnionStatement`** (Remark). If `H` is the filtered increasing union
of its compact subgroups, every compact subset of `H` lies in a compact subgroup.

**`CompactAveragingRelationStatement`** (Proposition). Under the same hypothesis, for a smooth
representation `(τ, E)` of `H` and `v ∈ E`: `v ∈ E(H, τ)` if and only if there is a compact
subgroup `K` with `τ(e_K) v = 0`. Here `τ(e_K)` is `fixedProjection` for the compact group `K`,
its restricted representation, its Borel structure, any Haar measure `μK` on `K`, and the
open subgroup `K` of itself.

**`CoinvariantSubrepresentationRelationsStatement`** (Corollary, first assertion). Under the
same hypothesis, for a smooth `(τ, E)` and a subrepresentation `E′`, the image of `E′(H, τ′)`
in `E` is `E(H, τ) ∩ E′`.

## Formalization choices

- **The Definition** is applied once, to the family of compact subgroups, and written out in
  each statement. It is not a separate declaration.
- **`e_K` for a compact subgroup that need not be open.** Renard's proof applies III.1.5 to the
  compact group `K` itself. The statement does the same: `K` is a compact t.d. group, `K` is a
  compact open subgroup of itself, and the published `fixedProjection` gives the action of
  its normalized Haar measure. The Borel structure on `K` is chosen inside the statement. The
  condition is required for every Haar measure on `K`, which is equivalent to one of them,
  since `e_K` does not depend on the choice.
- **The rest of the Corollary.** The exactness of `0 → E′_H → E_H → E″_H → 0` and the
  exactness of `j_H` are the published, proved `JL.characterLocalizationExactness`
  ([LocalizationExactnessProof](LocalizationExactnessProof.md)) at the trivial character,
  under `IsLimitOfCompactSubgroups`. The Remark statement gives that hypothesis from the
  filtered union. The sentence "dès que `H` est réunion de ses sous-groupes ouverts compacts"
  is read with the Proposition's hypothesis, a filtered increasing union, which the Corollary
  assumes ("avec les hypothèses de la proposition ci-dessus").
- **Lemma (i)–(ii)** of III.2.9 are the published `JL.TowerDatum.equiv` and
  `JL.TowerDatum.smoothIso` in general form (see the map). They are not restated.

## Why the statements are true

1. **Example.** The algebraic dual of `𝒟(G)_{G,l}` is the space of left-invariant linear
   forms on `𝒟(G)`. Such a form `λ` is determined by its values on the indicators `1_{gK}` of
   cosets of compact open subgroups. Left invariance gives `λ(1_{gK}) = λ(1_K)`. Comparing
   `K` with a smaller compact open `K′` gives `λ(1_K) = [K : K′] λ(1_{K′})`. So `λ` is a
   multiple of the Haar integral, and the Haar integral is a nonzero invariant form. The dual
   is a line, so the quotient is a line.
2. **Remark.** Cover `C` by finitely many `g_j K_j` with `K_j` compact open subgroups. Each
   `g_j` lies in a compact subgroup `L_j`, because the union is `H`. A compact subgroup
   containing all `L_j` and `K_j` contains `C`.
3. **Proposition.** If `v ∈ E(H, τ)`, then `v = Σ (τ(h_i) w_i − w_i)` with finitely many
   `h_i`. These lie in one compact subgroup `K`, by the union and filtering conditions, and
   `τ(e_K) τ(h) = τ(e_K)` for `h ∈ K`, so `τ(e_K) v = 0`. Conversely, if `τ(e_K) v = 0`, then
   `v = v − τ(e_K) v` lies in `E(K, τ) ⊂ E(H, τ)`. This is III.1.5 (ii) for the compact group
   `K`: for smooth `v`, `τ(e_K) v` is the average of the finitely many `τ(k) v`.
4. **Corollary.** Clearly `E′(H) ⊂ E(H) ∩ E′`. If `v ∈ E(H) ∩ E′`, the Proposition gives a
   compact `K` with `τ(e_K) v = 0`. The average `τ(e_K) v` is the same computed in `E′`, and
   `E′` is smooth, so the Proposition for `E′` gives `v ∈ E′(H)`.

## Remaining obligations

The proofs are a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Jacquet.Coinvariants` | `relations`, `Coinvariants`; Mathlib's `Subrepresentation` |
| `Langlands.Representation.Hecke.ActionProjection` | `Hecke.fixedProjection` |
| `Langlands.Representation.Smooth.Transfer.PullbackProof` | `isSmooth_comp` |
| `Langlands.HarmonicAnalysis.GroupAction` | `GroupAction.leftTests` |
