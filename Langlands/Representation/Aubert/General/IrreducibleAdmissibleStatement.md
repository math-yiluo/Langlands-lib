# Jacquet's theorem for general reductive rational points

Statement: Worker 261 (task `aa8bb3a4-42d3-47db-9a48-98eb87ad9327`).

This module states, as a closed proposition, that every irreducible smooth
complex representation of `G(F)` is admissible. Here `F` is any nonarchimedean
local field and `G` any connected reductive group over `F` (Renard VI.2.2,
Théorème; the result goes back to Jacquet). Nothing here assumes or proves it.

## Setting

The binders and the group are exactly those of the published
`RationalPointsFiniteLengthAdmissibleStatement` in
[`PrerequisiteStatements`](PrerequisiteStatements.md):

* a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]` and Mathlib's
  `[IsNonarchimedeanLocalField F]`;
* a group scheme `G : GroupScheme (Spec (CommRingCat.of F))` and
  `hG : IsConnectedReductive G` (published `GroupScheme.Reductive.Basic`).

`G(F)` is the actual type of rational points `RationalPoint F G.X`, the points
tested by the identity of `Spec F`, with the group structure coming from the group
object `G`. Its topology is pinned inside the statement by
`letI := rationalPointTopology F G.X`: Conrad's evaluation topology (Conrad,
Proposition 2.1), as in `PointTopology.RationalPoints`. That topology needs
`IsAffine G.X.left`. The statement gets it from `hG.isAffineHom` by
`isAffine_of_isAffineHom`, as the published targets do. No topology and no
topological property of `G(F)` is a hypothesis.

## The statement

`RationalPointsIrreducibleAdmissibleStatement.{u, uV}`: for every such `F` and
`G`, and every `A : SmoothRep.{0, u, uV} ℂ (RationalPoint F G.X)`,
`A.IsIrreducible → A.IsAdmissible`.

* `SmoothRep.{0, u, uV} ℂ G(F)` is the category of smooth complex
  representations of `G(F)` with carriers in `Type uV`. The carrier universe `uV`
  is independent of the field universe `u`.
* `A.IsIrreducible` is Mathlib's `Representation.IsIrreducible` of the
  underlying representation. It says the lattice of subrepresentations is simple:
  the representation is nonzero and has no `G(F)`-stable subspace other than `0`
  and the whole space. This is Renard's notion of an irreducible representation.
* `A.IsAdmissible` is the Library's `Langlands.IsAdmissible`: the representation
  is smooth, and for every open subgroup `K` of `G(F)` the fixed vectors `V^K`
  are finite-dimensional over `ℂ`. This is Renard's definition (III.1.7,
  Définition, printed p. 62), which also quantifies over all open subgroups.

## Provenance and scope

* Source: Renard VI.2.2, Théorème (printed p. 140): "Soit (π,V) une
  représentation lisse irréductible de G. Alors (π,V) est admissible." Renard's
  `G` is the group of `F`-points of a connected reductive group over a
  nonarchimedean local field, with its locally profinite topology (Chapter V).
  That is the setting of the binders above. Renard considers only
  representations on complex vector spaces (introduction to Chapter III, printed
  p. 57), which matches the coefficient field `ℂ` here.
* Purpose: Howe's theorem (Renard VI.6.3, printed pp. 178–179) proves "finite
  length ⇒ admissible" by induction on length, starting from VI.2.2. The induction
  is generic. Worker 585's conditional helper
  `SmoothRep.isAdmissible_of_finiteLength_of_irreducible` (module
  `Langlands.Representation.Smooth.Admissibility.FiniteLengthReduction`) takes
  as its hypothesis exactly the inner clause of this statement, for one group and
  one carrier universe. Applying it to a proof of this statement gives
  `RationalPointsFiniteLengthAdmissibleStatement`. That application belongs to
  the proof of the finite-length target, not to this module.
* Renard's proof of VI.2.2 needs several results that the Library does not have
  for general `G`:
  - IV.1.3: compact representations of finite type are admissible;
  - VI.2.1: a supercuspidal representation restricts to a compact
    representation of `⁰G`. The proof uses the Cartan decomposition (V.5.1)
    and compact open subgroups with an Iwahori decomposition (V.5.2);
  - V.2.6: `G/⁰G Z(G)` is finite;
  - III.1.8: Schur's lemma;
  - VI.2.1 Corollaire: every irreducible representation embeds in a parabolic
    induction of an irreducible supercuspidal representation. The proof uses
    VI.1.3 (Jacquet modules of finite type), VI.1.4 (transitivity) and
    Frobenius reciprocity;
  - III.2.3: parabolic induction preserves admissibility.
  This module states the theorem only.
* Generality: the statement covers all nonarchimedean local fields, positive
  characteristic included, and all connected reductive `G`, including nonsplit
  and non-quasi-split groups. It is not restricted to `PadicField`, `GL_n`, split
  groups or rank conditions.

## Sources

* D. Renard, *Représentations des groupes réductifs p-adiques* (2026 version),
  `renard-2026-representations-groupes-reductifs-padiques` (PDF page = printed
  page + 6): VI.2.2 Théorème and its proof, printed p. 140; VI.6.3, printed
  pp. 178–179; III.1.7 Définition, printed p. 62; introduction to Chapter III,
  printed p. 57.
* B. Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
  `conrad-2011-weil-grothendieck-adelic-points`: Proposition 2.1, printed
  pp. 2–3 (the pinned topology).
