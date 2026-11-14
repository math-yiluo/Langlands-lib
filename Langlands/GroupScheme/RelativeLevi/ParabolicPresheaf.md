# The presheaf of actual relative parabolic subgroup functors

This derived module constructs the presheaf needed for
`RelativeParabolicSchemeStatement`. It proves an equivalence with smooth proper
representability of that presheaf. It does not prove representability or the
published target.

## Definitions

For a group scheme `G` over `S`, `IsParabolic F` says that the all-test subgroup
functor `F` has an actual representative `j : P ⟶ G` satisfying the unchanged
predicate `IsRelativeParabolicSubgroup`. `ParabolicSubgroup G` is the subtype of
such subgroup functors. No chosen presentation is part of its equality.

`ParabolicRepresentative` packages a representative, its relative parabolicity
and its equality of all-test ranges. `parabolicRepresentative` chooses one.
In a reductive ambient group, `restrict` pulls the chosen representative back
and uses the canonical comparison to the specified ambient pullback. Its range
is independent of that choice, and identity and composition laws hold as
literal subgroup-functor equalities.

`parabolicPresheaf G hG` is the resulting presheaf on `Over S`, for
`hG : IsReductive G`. Its values lie in `Type (u + 1)`. No closedness theorem or
universe shrinking is needed for this construction.

`IsUniversal j` quantifies over all actual parabolic subgroup functors on all
base changes. It is equivalent to the quantification over actual relative
parabolic inclusions in the target statement.

## Implemented proofs

Base change of a parabolic representative follows from
`IsRelativeParabolicSubgroup.baseChange`. Evaluation additionally uses
`IsReductive.baseChange` and ambient-isomorphism transport along
`Descent.pullbackComparison`. Range invariance and evaluation identity and
composition are the imported generic family-evaluation lemmas.

A representing equivalence gives its universal subgroup by evaluating at the
identity and choosing an actual representative. Naturality identifies every
evaluation of that family with the representing equivalence. Surjectivity and
injectivity then prove existence and uniqueness of parameter morphisms.
Conversely, a universal relative-parabolic family gives the representing
equivalence by evaluation, with inverse the unique parameter morphism.
Evaluation composition supplies naturality.

`representableBy_iff_exists_universal` records this equivalence for each fixed
parameter scheme. `relativeParabolicSchemeStatement_iff` retains the smoothness
and properness conditions unchanged and translates the universal-family clause
in both directions.

## Provenance and scope

The definitions are internal constructions from the published predicates and
actual subgroup-functor operations. The representability equivalence is the
Yoneda interpretation of this concrete presheaf; no existence theorem is
assumed or introduced. Conrad, *Reductive group schemes* (2014), Definition
5.2.1, p.151, and Corollary 5.2.9 with its proof, pp.156–157, provide context for
the unchanged predicate and intended parameter scheme. This module establishes
the formal presheaf and comparison only; local classification, geometric
representability and smoothness and properness still require proofs.
