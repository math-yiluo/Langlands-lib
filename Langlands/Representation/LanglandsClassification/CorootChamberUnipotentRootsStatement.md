# Roots positive on a coroot chamber are the roots in `N`: statement

Module `Langlands.Representation.LanglandsClassification.CorootChamberUnipotentRootsStatement`.
Namespace `Langlands.GroupScheme`. Universe parameter `u`.
The module contains one **statement**, the `Prop`-valued definition
`CorootChamberUnipotentRootsStatement`; it proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read V.3.13–V.3.17, printed pp.112–114 / PDF pp.118–120.
V.3.17 is on printed p.114 / PDF p.120:

> **Lemme.** Soit `P = MN` un sous-groupe parabolique standard de `G` et soit
> `μ` un élément de `^G_P[(𝔞^G_M)^*]^+`. Alors l'ensemble des racines `γ` dans
> `Σ_∅` telles que `⟨μ, γ̌⟩ > 0` est l'ensemble des racines de `A_∅` dans `N`.
>
> *Démonstration.* Par définition, `^G_P[(𝔞^G_M)^*]^+` est l'ensemble
> `{x ∈ (𝔞^G_∅)^* | α ∈ Δ^M_∅ ⇒ ⟨x, α̌⟩ = 0, α ∈ Δ_∅ \ Δ^M_∅ ⇒ ⟨x, α̌⟩ > 0}`.
> Toute racine `γ ∈ Σ_∅` s'écrit `γ = Σ_{α ∈ Δ_∅} n_α α` où tous les
> `n_α ∈ ℤ` sont de même signe. D'autre part, `γ` est une racine de `A_∅`
> dans `N` si et seulement s'il existe `α ∈ Δ_∅ \ Δ^M_∅` tel que `n_α > 0`.
> Comme tous les `n_α` sont de même signe, ceci est équivalent à
> `⟨μ, γ̌⟩ > 0`.

Renard's root sets (V.3.4, printed p.110 / PDF p.116, and V.3.12, printed
p.112 / PDF p.118): `Σ′(A)` is the set of roots of `A` in `Lie(G)` (all
nonzero weights); `Σ(A)` is its subset of reduced roots, the `α ∈ Σ′(A)` with
`α/n ∉ Σ′(A)` for `n ≥ 2`; and `Σ′_∅ = Σ′(A_∅)`, `Σ_∅ = Σ(A_∅)`. The Lemma
quantifies `γ ∈ Σ_∅`, the reduced roots.

The Library's gap scans and the Chapter V ledger
(`notes/renard/chapter-v-structural-inputs.md`, row D04: "V.3.17 includes its
own proof") list V.3.17 as not stated. The provenance is source; the
statement is an extension of the Lemma from `Σ_∅` to `Σ′_∅` (see "Formal
choices").

## Published objects

All objects are published; this file constructs nothing.

- `G` is a connected reductive group scheme over a field `k`
  (`IsConnectedReductive G`), `i : T → G` a maximal split torus
  (`IsMaximalSplitTorus i`; Renard's `A_∅`), and `ν` a generic cocharacter
  of `T` (`IsGenericCocharacter i ν`). These fix the relative roots
  `relativeRoots i`, all nonzero weights of `T` on `Lie(G)` (Renard's
  `Σ′_∅`, not his reduced `Σ_∅`; the system may be nonreduced), the positive
  roots and the simple roots `simpleRelativeRoots i ν` (Renard's `Δ_∅`), and
  the standard subgroups. Renard's `Σ_∅` is the subset of indivisible
  elements of `relativeRoots i` (published `RelativeRoot.indivisibleRoots`).
- `D : RelativeRootReflectionData i` supplies, for every relative root `γ`, a
  cocharacter `D.coroot γ` with `⟨γ, D.coroot γ⟩ = 2` and a normalizer point
  acting by the reflection `χ ↦ χ - ⟨χ, D.coroot γ⟩ γ`; these are the
  coroots `γ̌`. The pairing of the real character space `Vstar T` with
  cocharacters is `RealTorusSpace.pair T x (1 ⊗ γ̌)`.
- `J ⊆ simpleRelativeRoots i ν` is Renard's `Δ^M_∅`; the standard parabolic
  `P = MN` is the one of `J`, and `N` is the published choice-free
  `standardUnipotent i ν J` (intersection of the dynamic unipotent subgroups
  of the standard cocharacters of `J`).
- The chamber is the published `restrictedCorootChamber i ν J (𝟙 T) D`
  (Worker 6, module `LanglandsTriplet`) with `A = T` and `f` the identity:
  the elements `x ∈ 𝔞*_∅ = Vstar T` with `⟨x, α̌⟩ = 0` for `α ∈ J` and
  `⟨x, α̌⟩ > 0` for the simple roots `α ∉ J`. This is the set displayed in
  Renard's proof, except that it is not intersected with `(𝔞^G_∅)^*`.
- "The roots of `A_∅` in `N`" are the published
  `RelativeRoot.subgroupRelativeRoots i (standardUnipotent i ν J)`: the
  nonzero weights of the conjugation action of `T` with a nonzero tangent
  vector in `N`, as in the published VII.3.5 statements. This is the set of
  all roots (in `Σ′_∅`) of `A_∅` in `N`; its reduced elements are Renard's
  roots `γ ∈ Σ_∅` of `A_∅` in `N`.

## The statement

`CorootChamberUnipotentRootsStatement`: for all such `k`, `G`, `T`, `i`, `ν`,
`D`, `J`, every `x` in the chamber and every relative root `r`,

`0 < ⟨x, ř⟩ ↔ r ∈ subgroupRelativeRoots i (standardUnipotent i ν J)`.

## Formal choices

- **All roots `Σ′_∅` instead of the reduced roots `Σ_∅`.** The Lean
  statement quantifies over every relative root `r ∈ relativeRoots i`
  (Renard's `Σ′_∅`), not only over the reduced ones. This is an extension of
  the Lemma: restricting `r` to the indivisible roots gives exactly Renard's
  statement for `γ ∈ Σ_∅` (with "roots of `A_∅` in `N`" read inside `Σ_∅`).
  The extension adds the non-reduced roots `r = 2β` (`β ∈ Σ_∅`) of a
  nonreduced system. For them both sides agree with those for `β`: the
  coroot of `2β` is `β̌/2`, a positive multiple of `β̌`, so
  `⟨x, (2β)ˇ⟩ > 0 ↔ ⟨x, β̌⟩ > 0`; and `2β` is a weight of `T` in `Lie(N)`
  exactly when `β` is, since `N` contains the root subgroup `U_β` (whose Lie
  algebra contains the `2β` weight space) exactly when `β` is positive with
  support outside `J`.
- **`(𝔞^G_∅)^*`.** Renard's `μ` lies in `(𝔞^G_∅)^*`. The statement allows any
  `x ∈ 𝔞*_∅` with the chamber conditions. This is more general and still
  true: the component of `x` in `𝔞*_G` (characters of `G`) pairs to zero with
  every coroot, because the Weyl reflections fix the characters of `G`.
- **Coroots from `D`.** The coroots are those of the supplied reflection data,
  as in the published chamber. For a connected reductive `G`, the reflection
  condition determines `γ̌` (uniqueness of reflections preserving a finite
  root system, and vanishing on the characters of `G`), so any `D` gives
  Renard's coroots; `D` is quantified.
- **Ground field.** Any field `k`. Renard works over a nonarchimedean local
  field; the lemma is a statement about the relative root system.

## Why the statement is true

Every relative root is `r = Σ n_α α` over the simple roots with all `n_α` of
one sign, and its coroot is `ř = Σ m_α α̌` with each `m_α` of the same sign
as `n_α` and nonzero exactly where `n_α ≠ 0` (so `ř` is a nonnegative
combination of simple coroots for positive `r` and a nonpositive one for
negative `r`, e.g. `(-α)ˇ = -α̌`; for a non-reduced root `2β`,
`(2β)ˇ = β̌/2`). With `⟨x, α̌⟩ = 0` for `α ∈ J` and `> 0` otherwise,
`⟨x, ř⟩ = Σ_{α ∉ J} m_α ⟨x, α̌⟩`. It is positive exactly when `r` is positive
with some `n_α > 0`, `α ∉ J`; it is `≤ 0` for negative roots and `0` for
positive roots supported in `J`. The Lie algebra of
`N = standardUnipotent i ν J` is the sum of the root spaces of the positive
roots with some `n_α > 0`, `α ∉ J`.

## Remaining obligations

The proof is a separate obligation. It needs the root-system structure of
the relative roots of a connected reductive group (published
`HasRelativeRootSystem` and related modules), the description of the
coroots by `D`, and the root-space description of the Lie algebra of the
dynamic unipotent subgroups.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.LanglandsClassification.LanglandsTriplet` | `restrictedCorootChamber`, and through it `RelativeRootReflectionData`, `relativeRoots`, `simpleRelativeRoots`, `standardUnipotent`, `RealTorusSpace.pair`, `IsMaximalSplitTorus`, `IsGenericCocharacter`, `IsConnectedReductive` |
| `Langlands.GroupScheme.Rational.SubgroupRelativeRoots` | `RelativeRoot.subgroupRelativeRoots` |
