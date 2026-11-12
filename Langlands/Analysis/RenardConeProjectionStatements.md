# Projection on a cone in a Euclidean space: statements

Module `Langlands.Analysis.RenardConeProjectionStatements`.
Namespace `Langlands.Renard`.
Entry proposition `ConeProjectionStatements`; nothing is proved here.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The statements are the Proposition and the Corollary of V.5.5, "Démonstration
du lemme combinatoire de Langlands", printed pp.127–128 / PDF pp.133–134.
Worker 1222 read V.3.18 (printed pp.114–115 / PDF pp.120–121) and all of
V.5.5 (printed pp.127–129 / PDF pp.133–135):

> Soit donc `V` un tel espace [euclidien], de dimension finie, où l'on note
> `⟨ . , . ⟩` le produit scalaire. Fixons un cône ouvert `C` de `V`, et notons
> `Č` son dual `Č = {v ∈ V | ∀ w ∈ C, ⟨v, w⟩ > 0}`. Notons `C̄` et `Č̄` les
> adhérences respectives de `C` et `Č`.
>
> **Proposition.** Pour tout `v ∈ V`, il existe un unique élément `v₀ = p_C(v)`
> de `C̄`, appelé projection de `v` sur `C`, vérifiant
> (i) `∀ w ∈ C̄, ‖v − v₀‖ ≤ ‖v − w‖`.
> De plus, l'élément `v₀` est caractérisé par l'une des propriétés suivantes,
> équivalentes à (i),
> (ii) `∀ w ∈ C̄, ⟨v − v₀, w − v₀⟩ ≤ 0`,
> (iii) le vecteur `v₀ − v` est dans `Č̄` et `⟨v − v₀, v₀⟩ = 0`.
>
> L'existence de la projection est un résultat établi plus généralement pour
> toute partie convexe fermée d'un espace de Hilbert. L'équivalence des
> conditions (i), (ii) et (iii) pour les cônes est élémentaire et laissée au
> lecteur.
>
> Fixons maintenant une base `{α₁, …, αₙ}` de `V`, et notons `{ω₁, …, ωₙ}` la
> base duale. On suppose désormais que `C` est le cône ouvert engendré par les
> vecteurs `ω₁, …, ωₙ`, c'est-à-dire `C = {v = ∑ tᵢ ωᵢ, tᵢ > 0}`. On a alors
> `Č = {w = ∑ sᵢ αᵢ, sᵢ > 0}`.
>
> **Corollaire.** Pour tout `v ∈ V`, il existe une partie unique `F(v)` de
> `{1, …, n}` telle que `v = ∑_{i ∉ F(v)} tᵢ ωᵢ − ∑_{j ∈ F(v)} sⱼ αⱼ`, avec
> `tᵢ > 0`, `sⱼ ≥ 0`. On a alors `v₀ = p_C(v) = ∑_{i ∉ F(v)} tᵢ ωᵢ`.

The rest of V.5.5 applies the Corollary to `V = (𝔞_M^G)^*` with the basis
`Δ(P)` and deduces the combinatorial lemma of Langlands, V.3.18; see "Scope".

## The Lean statements

Both statements use Mathlib's real inner product spaces
(`[NormedAddCommGroup E] [InnerProductSpace ℝ E]`), with
`[FiniteDimensional ℝ E]`, and `inner ℝ` for `⟨ , ⟩`. `closure` is the
topological closure in the norm topology.

### `ConeProjectionStatement` (Proposition)

For every finite-dimensional real inner product space `E : Type v` and every
`C : Set E` that is open, convex, nonempty and stable under multiplication by
positive reals, put `Č = {u | ∀ w ∈ C, 0 < ⟨u, w⟩}`. For every `v : E`:

1. there is a unique `v₀ ∈ closure C` with `‖v − v₀‖ ≤ ‖v − w‖` for all
   `w ∈ closure C` (existence and uniqueness of `p_C(v)` with (i));
2. for every `v₀ ∈ closure C`, (i) holds iff (ii) holds:
   `⟨v − v₀, w − v₀⟩ ≤ 0` for all `w ∈ closure C`;
3. if moreover `C ≠ E`, then for every `v₀ ∈ closure C`, (i) holds iff (iii)
   holds: `v₀ − v ∈ closure Č` and `⟨v − v₀, v₀⟩ = 0`.

### `ConeProjectionBasisStatement` (Corollary)

For every finite index type `ι : Type u` (with decidable equality), every
finite-dimensional real inner product space `E : Type v`, every basis
`α : Module.Basis ι ℝ E` and every family `ω : ι → E` with
`⟨αᵢ, ωⱼ⟩ = δᵢⱼ` (the dual basis), put `C = {∑ᵢ tᵢ ωᵢ | ∀ i, tᵢ > 0}`. For
every `v : E`:

1. there is a unique `F : Finset ι` for which there are `t s : ι → ℝ` with
   `tᵢ > 0` for `i ∉ F`, `sⱼ ≥ 0` for `j ∈ F`, and
   `v = ∑_{i ∉ F} tᵢ ωᵢ − ∑_{j ∈ F} sⱼ αⱼ`;
2. for every such `F`, `t`, `s`, the vector `∑_{i ∉ F} tᵢ ωᵢ` lies in
   `closure C` and is nearest to `v` among the points of `closure C`. That is,
   it is `p_C(v)`.

The complement of `F` is `Finset.univ \ F`. Only `F` is bound by the
uniqueness quantifier. The coefficient functions are existential on all of
`ι`, and their values outside the relevant index sets are unconstrained.

### `ConeProjectionStatements`

The conjunction `ConeProjectionStatement.{v'} ∧
ConeProjectionBasisStatement.{u', v'}`.

## Formal choices

- **Hypotheses on `C`.** Renard says only "cône ouvert". The Lean statement
  takes `C` open, stable under positive scalars, convex and nonempty. The
  sentence after the Proposition obtains the projection from the theorem for
  closed convex subsets of a Hilbert space, so convexity is implicit; the cone
  of the Corollary has all four properties. Without nonemptiness the closure
  is empty and no projection exists.
- **`C ≠ E` in (iii).** If `C = E`, then `Č` is empty: no `u` satisfies
  `0 < ⟨u, 0⟩`. Its closure is empty, so (iii) fails, although `p_C(v) = v`.
  The equivalence with (iii) therefore needs `C ≠ E`, and the Lean statement
  adds this hypothesis to that clause only. For a nonempty convex open cone
  `C ≠ E`, the closure of `Č` is the dual cone
  `{u | ∀ w ∈ C, 0 ≤ ⟨u, w⟩}` of the closure of `C`, and (iii) is the usual
  characterization of the projection on a closed convex cone. In the
  Corollary, `C = E` only when `ι` is empty, and then `E = 0` and everything is
  trivial. The Corollary is stated without any such hypothesis.
- **Dual basis.** "La base duale" is the basis dual to `α` for the inner
  product. It is given as a family `ω` with `⟨αᵢ, ωⱼ⟩ = δᵢⱼ`; such a family is
  unique and is a basis.
- **The displayed `Č`.** For the cone of the Corollary, Renard displays
  `Č = {∑ sᵢ αᵢ, sᵢ > 0}`. With the definition of `Č` above, the exact set is
  `{∑ sᵢ αᵢ | sᵢ ≥ 0, not all zero}` (for orthonormal `α`, `α₁ ∈ Č`). When `ι`
  is nonempty, the two sets have the same closure `{∑ sᵢ αᵢ | sᵢ ≥ 0}`, which
  is all the proof uses. When `ι` is empty, `E = 0` and `C = {0} = E`; then `Č`
  and its closure are empty (`0 < ⟨0, 0⟩` fails), whereas the cones of
  strictly positive and of nonnegative `α`-coefficients are both `{0}` (empty
  conditions, empty sum). In that case the Corollary holds directly in the zero
  space, with `F = ∅`, and does not use characterization (iii). The display is
  not stated.
- **Index set.** `{1, …, n}` is an arbitrary finite type `ι`; `n = 0` is
  allowed.
- **Universes.** The space universe `v` and the index universe `u` are
  independent.

## Relation to existing work

The published `Langlands.RootWeightConeDecompositionStatement` (Worker 19) is a
related Euclidean lemma from Silberger (1978), Lemma 7.1. It has the opposite
labelling of the index set (its `F` indexes the weight terms) and assumes in
addition `⟨αᵢ, αⱼ⟩ ≤ 0` for `i ≠ j`. The present Corollary has no such
hypothesis, since Renard's proof goes through the projection on the closed
cone. It also identifies the weight part with that projection. Applied with
`F` replaced by its complement, the first part of the present Corollary gives
the conclusion of that statement, without its extra hypothesis. The converse
fails as stated, because of that hypothesis. This comparison is not
formalized.

## Scope

This file states the two assertions of V.5.5 and proves neither. Proofs belong
to a separate `lean.proof@1` task targeting `ConeProjectionStatements`.
Renard's route is the projection theorem for closed convex sets, the
equivalences (i) ⟺ (ii) ⟺ (iii), which he leaves to the reader, and for the
Corollary the expansion of `v₀` in the basis `ω` and of `v₀ − v` in the basis
`α`.

Not stated: the combinatorial lemma of Langlands itself (V.3.18, printed
pp.114–115 / PDF pp.120–121), and its deduction at the end of V.5.5. These
need the spaces `𝔞_M^*`, `(𝔞_M^G)^*`, the simple roots `Δ(P)` and the cones of
V.3.16 for an actual reductive group. Those belong to the structural Chapter V
interface (rows D04–D05 of `notes/renard/chapter-v-structural-inputs.md`).

The file imports only Mathlib (`Analysis.InnerProductSpace.Basic`,
`Analysis.Convex.Basic`, `LinearAlgebra.Basis.Defs`,
`Topology.Algebra.Module.FiniteDimension`; environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
