# Restricting a corrected filtration step to its new support

Author: Worker 1018, task `277860be-2aeb-4a85-8ccb-f1e2e5c573b9` (the right-exactness
part of the split agreed with Worker 1312).

This internal reduction works with the published `CorrectedFiltration.step`, the
image of `inductionStep` in the actual normalized Jacquet module `r_I(E_J)`. It
shows that a change of the step at `i` is detected by the `U_I`-coinvariants of the
restrictions to the new support `G_{θ_{i+1}'} \ G_{θ_i'}`. The functions restricted
here are those supported in `G_{θ_{i+1}'}`.

## Context in the erratum

Aubert's erratum (printed p. 4688) states, for `θ_1 ⊂ θ_2`, the exact sequence
`0 → Ẽ^{θ_1}_J → Ẽ^{θ_2}_J → Ẽ^{θ_2 − θ_1}_J → 0`, where the second map is the
restriction `Res^{θ_2}_{θ_2−θ_1}` to `G_{θ_2 − θ_1}`. It cites [C, lem. 6.1.1] for
this sequence and then applies the Jacquet functor `r_I`. This module proves only
the elementary part of that argument. The kernel of the restriction lies in the
lower step, and that holds by the definition of the supports. Coinvariants are
right exact. The image of the restriction is kept as the abstract
`restrictionImage`. The module does not prove surjectivity onto compactly
supported functions on the difference, which uses the topology of the cells. It
does not use openness, closedness or disjointness of cells either.

## Generic layer

Let `σ` be a representation of a subgroup `P` of a topological group `G`.

* `restrictTo σ D` is the linear map sending a smooth induced function `f` to
  `D.indicator f`. This is `f` on `D` and `0` off `D`, a plain function `G → V`.
* `rightTranslate q` is the linear map `φ ↦ φ(· q)` on functions `G → V`. If `D`
  is right `q`-stable in both directions, restriction to `D` commutes with
  `Induction.smoothInduced P σ q` and `rightTranslate q`
  (`restrictTo_smoothInduced`).
* `restrictionImage σ X D` is the image under `restrictTo σ D` of
  `functionSupport σ X`, the functions supported in `X`.
* `translationRelations Y N` is the span of the differences `φ(· n) − φ` for
  `φ ∈ Y` and `n ∈ N`. If `Y` is right `N`-stable, it is contained in `Y`
  (`translationRelations_le`), and `Y ⧸ translationRelations Y N` is the space of
  `N`-coinvariants of `Y` for the right-translation action. The module does not
  construct this quotient.

For right `N`-stable sets `X' ⊆ G` and `X ⊆ G`, `X \ X'` is right `N`-stable in
both directions (`mul_mem_sdiff_iff`). The restriction image on `X \ X'` is then
right `N`-stable (`rightTranslate_mem_restrictionImage`). The main generic lemma
is `exists_lower_of_restrictTo_mem_translationRelations`. Let `f` be supported in
`X`, and suppose its restriction to `X \ X'` lies in the translation relations of
the restriction image. Then there is an `f'` supported in `X'` such that `f − f'`
lies in the span of the differences `n · g − g`, with `g` supported in `X` and
`n ∈ N`.

Proof: each generator `φ(· n) − φ` with `φ = restrictTo g` is the restriction of
`n · g − g` (by `restrictTo_smoothInduced`). So the restriction of `f` equals the
restriction of some `k` in that span. Then `f' := f − k` is supported in `X`,
because `k` is. It vanishes on `X \ X'`, so it is supported in `X'`.

## Corrected filtration

Use the standard setting of `CorrectedFiltration`. The terms are
`E_J = term P M U h hclosed A s` with `J = S \ s`. The group supports are
`G_{θ_i'} = groupSupport P T cs I s i`, and `inductionStep` holds the functions
supported in `G_{θ_i'}`. Every group support is right `P_I`-stable
(`groupSupport_mul_mem`, from `cellSupport_mul_right`), and hence right
`U_I`-stable.

* `mk_mem_step_of_restrictTo_mem`: suppose `f ∈ inductionStep (i + 1)` and the
  restriction of `f` to `G_{θ_{i+1}'} \ G_{θ_i'}` lies in the `U_I`-translation
  relations of the restriction image. Then the class
  `Jacquet.Localization.mk (U I) 1 f` of `f` in `r_I(E_J)` lies in `step i`.
  Write `f = f' + k` with `f'` in the lower step and `k` in the span of the
  differences `n · g − g`. Each such difference lies in
  `Jacquet.Localization.relations` for the trivial character
  (`Jacquet.Localization.sub_mem_relations`). So `mk f = mk f'`
  (`Jacquet.Localization.mk_eq_iff`).
* `step_succ_eq_of_restrictionImage_le`: suppose the whole restriction image on
  the new support lies in its own `U_I`-translation relations, that is, its
  `U_I`-coinvariants vanish. Then `step (i + 1) = step i`. The other inclusion is
  `step_monotone`.
* `exists_restrictTo_not_mem_of_step_succ_ne` and
  `not_restrictionImage_le_of_step_succ_ne` are the contrapositives. If the step
  changes at `i`, some function in `inductionStep (i + 1)` has a restriction to
  the new support outside the `U_I`-translation relations. Equivalently, the
  restriction image does not lie in its translation relations.

The new support is contained in the cell union of the whole new double coset
`W_J w W_I`. Worker 1312's separate helper `CorrectedFiltrationWitnesses` proves
this as `groupSupport_succ_sdiff_subset`; this module does not import it.

## Scope and provenance

The only project import is
`Langlands.Representation.Aubert.General.CorrectedFiltration`. The proofs use its
`functionSupport`, `functionSupport_smoothInduced`, `cellSupport_mul_right`,
`mem_jacquetImage` and `step_monotone`, together with
`Jacquet.Localization.sub_mem_relations` and `Jacquet.Localization.mk_eq_iff`.
Everything else is elementary submodule and set reasoning. This is a derived
reduction. It attributes no new theorem to an original source.

The universes of the root index, the group and the representation carrier stay
independent. The input `A` is an arbitrary smooth complex representation. There
is no finite-length, admissibility, Bruhat-cover, endpoint, compact-limit or
Jacquet-exactness premise.

These lemmas do not compute the coinvariants of the restriction image. In
particular, they do not identify them with a Jacquet module of `r_J E` on a Levi
subgroup; that identification is the Bernstein–Zelevinsky localization on one
cell. They also do not prove support/Jacquet vanishing or
`RationalCorrectedGradedVanishingStatement`.
