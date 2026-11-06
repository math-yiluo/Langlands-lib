# Reduction of the cover-preimage statement to three structural inputs

Author: Worker 1413.

Module `Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageReduction`.

## The statement

`Langlands.GroupScheme.SplitTorusCentralizerCoverPreimageReductionStatement.{u}`
is the proposition

```text
ReductiveCentralDerivedProductStatement.{u} →
  DynamicCentralizerReductiveStatement.{u} →
  SplitTorusCentralizerDerivedSimplyConnectedStatement.{u} →
  SplitTorusCentralizerCoverPreimageStatement.{u}
```

All four propositions are published and unchanged:

- `ReductiveCentralDerivedProductStatement` (module
  `Reductive.CentralDerivedProductStatement`). Every connected reductive group
  `G` over a field has a closed central torus `i : Z ⟶ G` and a derived
  subgroup `d₀ : D₀ ⟶ G` whose multiplication morphism
  `subgroupProductMap i d₀` is an epimorphism of schemes over the base.
- `DynamicCentralizerReductiveStatement` (module
  `Dynamic.CentralizerReductiveStatement`). Every closed representative of the
  dynamic centralizer of a cocharacter of a connected reductive group is
  connected reductive.
- `SplitTorusCentralizerDerivedSimplyConnectedStatement` (module
  `SimplyConnected.SplitTorusCentralizerDerivedStatement`). In a simply
  connected group, the derived subgroup of the centralizer of a split
  subtorus is simply connected.
- `SplitTorusCentralizerCoverPreimageStatement` (module
  `SimplyConnected.SplitTorusCentralizerCoverPreimageStatement`) is the
  target. Its Markdown lists its data, hypotheses and six clauses.

The theorem `Langlands.GroupScheme.splitTorusCentralizerCoverPreimage_of_inputs`
proves the implication for every universe `u`. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`. Once the three inputs are proved, the
target follows by applying this theorem.

## The proof

Fix the data of the target: `G, D, C, d, π, A, a, M, j, DM, CM, dM, πM, T, t`.
Let `f = π ≫ d`. The helper modules carry the substance:

- [`CoverPreimageToolkit`](CoverPreimageToolkit.md),
- [`CoverPreimageCentralProduct`](CoverPreimageCentralProduct.md),
- [`CoverPreimageCentralizer`](CoverPreimageCentralizer.md),
- [`CoverPreimageCharacters`](CoverPreimageCharacters.md),
- [`CoverPreimageDerived`](CoverPreimageDerived.md),
- [`CoverPreimageTorus`](CoverPreimageTorus.md).

1. *Central product.* The first input gives `Z`, `i` and `d₀`. Both `d₀` and
   `d` represent the derived subgroup, so they differ by an isomorphism
   `D₀ ≅ D` over `G` (published `isoOfIsRepresentedBy`). Then
   `subgroupProductMap i d₀` is the whiskered isomorphism followed by
   `subgroupProductMap i d`, so the latter is an epimorphism. By
   `isCentralFppfCover_centralProduct`, `centralProduct i d : Z × D ⟶ G` is
   quasi-compact, flat, surjective and locally of finite presentation, with
   central kernel killed by a positive integer.
2. *Clauses 1–3.* `exists_splitSubtorus_torusCentralizer_eq_comap` gives a
   split subtorus `a' : A' ⟶ C` with
   `torusCentralizer a' = (torusCentralizer a).comap f`.
   - *`j` is closed.* By the published `centralizingCocharacter_spec`,
     `torusCentralizer a` is a dynamic centralizer, so the published
     `Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer` makes
     `j` closed.
   - *`M'`, `j'`, `p`.* Put `M' = subgroupIntersection f j`,
     `j' = subgroupIntersectionFst f j` and `p = subgroupIntersectionSnd f j`.
     The published `IsRepresentedBy.comap_subgroupIntersectionFst` shows that
     `j'` is closed and represents `(torusCentralizer a).comap f`, that is,
     `torusCentralizer a'`.
   - *Clause 1.* `M'` is connected reductive by the second input, applied to
     the centralizing cocharacter of `a'` in the connected reductive group `C`
     (`C` is semisimple).
   - *Clauses 2 and 3.* Clause 2 is the intersection square. Clause 3 is the
     representation equality together with `range j = torusCentralizer a`.
3. *`Z ⊆ M`.* Every point of `i` is central, hence in `torusCentralizer a`.
   So `i` factors as `iM ≫ j` (published `IsRepresentedBy.liftOfLE`).
4. *Clause 4.* `exists_nsmul_eq_characterRestrict`, with `π` a central fppf
   cover (`isCentralFppfCover_of_isCentralIsogeny`).
5. *Clause 5.* The published `derivedSubgroupRepresentability` gives a
   derived subgroup `d' : D' ⟶ M'`. The third input makes `D'` simply
   connected. `exists_derivedSubgroup_lift` gives `b : D' ⟶ CM` with
   `b ≫ πM ≫ dM = d' ≫ p`.
6. *Clause 6.* `exists_maximalTorus_preimage`.

## Provenance

This is an internal reduction, proved in Lean. It introduces no assertion
beyond its three published inputs. The target is the derived formulation, in
`SplitTorusCentralizerCoverPreimageStatement`, of facts used in the proof of
Corollary 2.6.28 of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), printed pp. 105–106 (PDF pp. 136–137). There the preimage `M'_0` of a
minimal Levi subgroup `M_0` in `G_sc` is compared with `M_0`.

The route differs from the sketch in that statement's Markdown. It does not
use the maximal subtorus of the preimage of a split torus or Galois averaging
of characters. Instead it works with the central product `Z × D ⟶ G` given by
the first input. That input's own provenance is Milne, *Algebraic Groups*
(2017), Proposition 12.46(b) (printed p. 245, PDF p. 261): for a central torus
`T` of a connected group variety `G` with `G/T` perfect, `T × D(G) ⟶ G` is a
quotient map with kernel `T ∩ D(G)`. From the central product the proof uses
power lifts of cocharacters and of maximal tori, fppf descent of characters,
and finite-hom rigidity for derived subgroups, all published Library results.
