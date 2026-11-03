# Jacquet–Cartan data on general reductive rational points

Statement: Worker 276 (task `173e44ba-079b-4597-a13b-1aab371a4ec9`). The datum
`Langlands.JacquetCartanDatum` and the abstract admissibility theorem are Worker
23's published module
[`Smooth.Admissibility.JacquetCartan`](../../Smooth/Admissibility/JacquetCartan.md).

This module states, as a closed proposition, that the rational points `G(F)` of
every connected reductive group `G` over every nonarchimedean local field `F`
carry a Jacquet–Cartan datum. The datum is the group-theoretic input of
Jacquet's proof that irreducible smooth representations are admissible (Renard
VI.2.2). The module does not assume or prove the proposition.

## Setting

The binders and the group are exactly those of the published target
`RationalPointsIrreducibleAdmissibleStatement` in
[`IrreducibleAdmissibleStatement`](IrreducibleAdmissibleStatement.md):

* a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]` and Mathlib's
  `[IsNonarchimedeanLocalField F]`;
* a group scheme `G : GroupScheme (Spec (CommRingCat.of F))` and
  `hG : IsConnectedReductive G` (published `GroupScheme.Reductive.Basic`).

`G(F)` is the type `RationalPoint F G.X` of rational points, with the group
structure that comes from the group object `G`. Its topology is pinned inside
the statement by `letI := rationalPointTopology F G.X`, Conrad's evaluation
topology (`PointTopology.RationalPoints`). That topology needs
`IsAffine G.X.left`. As in the target, the statement gets it from
`hG.isAffineHom` by `isAffine_of_isAffineHom`. No topology and no topological
property of `G(F)` is a hypothesis.

## The statement

`RationalPointsJacquetCartanDatumStatement.{u}`: for every such `F` and `G`,

```
Nonempty (JacquetCartanDatum.{u, u} (RationalPoint F G.X))
```

for the pinned topology. A `JacquetCartanDatum` is data, so the proposition
asserts that a datum exists. The datum's index type `ι` and its wall types
`wall i` lie in `Type u`, the universe of `F`. The fields are listed in
[`JacquetCartan.md`](../../Smooth/Admissibility/JacquetCartan.md). Spelled out
for `G(F)`, a datum consists of:

* an index type with a natural-number rank. For each index `i` it has subgroups
  `levi i` and `unipotent i` of `G(F)`, where `levi i` is closed and normalizes
  `unipotent i`. One index `top` has trivial `unipotent top`;
* for each `i`, a compact set `C` with `G(F) = levi i · unipotent i · C`;
* for each `i`, a type of walls and, for each wall `a`, a subgroup
  `wallUnipotent i a ≤ levi i`. Each wall has an index `j` of smaller rank with
  `unipotent j ⊆ wallUnipotent i a · unipotent i`;
* for each `i`, a compact set `cartanCompact i ⊆ levi i` and a countable set
  `cartanSet i ⊆ levi i` with `levi i = cartanCompact i · cartanSet i ·
  cartanCompact i`;
* the contraction property. For every neighbourhood `O` of `1` in `G(F)` and
  every family of finite sets `S a ⊆ wallUnipotent i a`, there is a compact
  `D ⊆ G(F)` such that every `t ∈ cartanSet i` either
  - is `d * z` with `d ∈ D` and `z ∈ levi i` commuting with all of `levi i`, or
  - satisfies `t * u * t⁻¹ ∈ O` for all `u ∈ S a`, for some wall `a`.

The choice of `Type u` for the index universe is a design choice. The intended
indices below, finite sets of relative simple roots, are built from characters
of a torus over `F`, which live in `Type u`.

## Relation to the target

The companion module
[`IrreducibleAdmissibleOfDatum`](IrreducibleAdmissibleOfDatum.md) proves that
this proposition implies `RationalPointsIrreducibleAdmissibleStatement.{u, uV}`
for every carrier universe `uV`. It applies
`SmoothRep.isAdmissible_of_jacquetCartanDatum` to the datum, with the published
facts that `G(F)` is a topological group and has a compact open subgroup.

## Provenance and intended realization

The proposition is internal to this project (provenance `derived`). It
reformulates the structural facts about `G(F)` that Renard's proofs of
VI.2.1 and VI.2.2 use. Below, `D. Renard` is the 2026 French version
(PDF page = printed page + 6).

Fix a minimal parabolic subgroup `P_∅ = M_∅ N_∅` with simple relative roots
`Δ_∅` (V.3.12, printed p. 112) and a maximal compact subgroup `K₀` adapted to `A_∅`
(V.5.1 Théorème, printed p. 122). The datum the proposition asks for is meant to
be realized as follows:

* **Indices.** The standard parabolic subgroups `P_I = M_I N_I` for `I ⊆ Δ_∅`
  (V.4.2 Proposition, printed p. 118), with `rank I = |I|` and `top = Δ_∅`, where `P_{Δ_∅} = G` and
  `N_{Δ_∅} = 1`. `levi I = M_I(F)` normalizes `unipotent I = N_I(F)` and is
  closed.
* **Iwasawa.** `G = P_∅ K₀` (V.5.1 (1)), so `G = M_I N_I K₀` and `C = K₀`
  serves.
* **Walls.** A wall of `M_I` is a root `α ∈ I`. Its subgroup is
  `N_{I∖{α}} ∩ M_I`, the unipotent radical of the maximal standard parabolic
  subgroup of `M_I` attached to `I ∖ {α}` (V.3.11, printed p. 112; V.4.8,
  printed p. 122). The descent index is `I ∖ {α}`, by the decomposition
  `N_{I∖{α}} = (N_{I∖{α}} ∩ M_I) N_I`, which the proof of the VI.2.1
  Corollaire uses through VI.1.4 (printed p. 139).
* **Cartan.** `M_I = ⋃ (K₀ ∩ M_I) a (K₀ ∩ M_I)`, where `a` runs over the
  countable set `C̃⁺_∅ = C⁺_∅ F_∅` taken for the minimal parabolic
  `P_∅ ∩ M_I` of `M_I` (V.5.1 (4) and (5), printed p. 122; notation V.3.23,
  printed p. 117). This set is countable because it lifts the lattice
  `Λ(M_∅)` into `M_∅` (V.3.23).
* **Contraction.** The dichotomy in the proof of `a) ⇒ b)` of the VI.2.1
  Théorème (printed pp. 138–139), applied to `M_I`. A set of dominant elements
  that is not compact modulo the centre has a simple root `α` with
  `|α(t_n)| → 0` (VI.2.1.1). Conjugation by such elements then contracts
  compact subsets of the unipotent radical of the maximal parabolic of `α`
  (V.5.2 (iii) and (iv), printed p. 123).

These realization notes explain the intended meaning. The Lean proposition
asserts only that some datum exists; it does not require this realization.

## Scope

The statement covers all nonarchimedean local fields, positive characteristic
included, and all connected reductive `G`, including nonsplit and
non-quasi-split groups. It is not restricted to `PadicField`, `GL_n`, split
groups or rank conditions.

## Sources

* D. Renard, *Représentations des groupes réductifs p-adiques* (2026 version),
  `renard-2026-representations-groupes-reductifs-padiques`:
  - V.3.11 (printed p. 112);
  - V.3.12 (printed p. 112) and V.3.23 (printed p. 117);
  - V.4.2 Proposition (printed p. 118) and V.4.8 (printed p. 122);
  - V.5.1 Théorème (1)–(5) and V.5.2 Théorème (printed pp. 122–123);
  - VI.2.1 Théorème, proof of `a) ⇒ b)`, and VI.2.1 Corollaire with its proof
    (printed pp. 138–139);
  - VI.2.2 Théorème (printed p. 140).
* B. Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
  `conrad-2011-weil-grothendieck-adelic-points`: Proposition 2.1, printed
  pp. 2–3 (the pinned topology).
