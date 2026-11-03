# Split-solvable group schemes over an arbitrary field

Worker 1333 implemented this module using the interface design of Worker 1305
and the scope coordinated by Worker 1293.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), the beginning of Section B.1 and Example B.1.1, printed pp.561–562,
one-based PDF pp.587–588. The registered source ID is
`conrad-gabber-prasad-2015-pseudo-reductive`, with SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

## Scope and source correspondence

For every field `k : Type u`, put `B := Spec (CommRingCat.of k)`. The public
predicate `Langlands.GroupScheme.IsSplitSolvableGroupScheme H` applies to an
actual `H : GroupScheme B`. Its fields require:

- `smooth : Smooth H.X.hom`;
- `isAffineHom : IsAffineHom H.X.hom`;
- `connectedSpace : ConnectedSpace H.X.left`;
- `isSolvableGroupScheme : IsSolvableGroupScheme H`;
- `hasSeries : ∃ n : ℕ, SplitSolvable.HasSeries n H`.

The source defines splitting of a smooth connected solvable algebraic group
by a composition series with quotients isomorphic over the ground field to
Ga or GL₁. Here affineness and the existing notion of solvability are
explicit outer requirements, as required by this interface.
`IsSolvableGroupScheme` is imported unchanged from
`Langlands.GroupScheme.Absolute.Borel`; its definition uses solvability of
the abstract group of algebraic-closure points. The comparison with other
definitions of solvability discussed in that module's Markdown is not proved
here.

Appendix B concentrates on positive characteristic, where the imperfect-field
issues arise. This module uses the same Ga/Gm-series definition in every
characteristic, with no perfection or characteristic hypothesis. All schemes,
series members and test schemes use universe `u`.

## The finite series and actual quotients

`SplitSolvable.IsElementaryQuotient V` is the disjunction of
`RelativeRoot.IsVectorGroupOfDimension V 1` and
`Nonempty (V ≅ (Gm B).toGrp)`. The first is the existing natural all-test
description of the one-dimensional additive vector group; the second is an
actual isomorphism of group schemes over `B`.

`SplitSolvable.HasSeries` is a recursive proposition:

- At zero, `SubgroupFunctor.range (𝟙 H) = ⊥`. Thus the entire represented
  group functor is trivial on every relative scheme test.
- At `n + 1`, there are actual group schemes `N,V`, a homomorphism
  `j : N ⟶ H` and a homomorphism `q : H ⟶ V`. The map `j` is a closed
  subgroup, `N` is smooth and connected, its all-test image is normal, `q`
  satisfies `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q`, `V`
  is an elementary quotient, and `N` has a length-`n` series.

This is the series pattern already used by `RelativeRoot.HasSplitSeries`,
with the additional Gm alternative. Normality is required for each subgroup
in its immediate successor. The finite normal-series witness is retained
explicitly; no induction may replace it by an arbitrary smooth subgroup.

The imported `RelativeRoot.IsFppfQuotient` is reused without modification.
It requires flatness, surjectivity of the scheme morphism, local finite
presentation, and equality between the actual kernel's all-test image and
the specified subgroup functor. It expresses the represented fppf quotient
using the actual morphism and kernel. It does not require surjectivity on
the group of points of each original test scheme.

## Basic laws

The outer structure has its generated constructor and projections.
`isSplitSolvableGroupScheme_iff` exposes its five clauses as a conjunction.
`SplitSolvable.hasSeries_zero_iff` and `hasSeries_succ_iff` are the exact
recursive constructor/destructor equivalences, proved by definitional
equality. `SplitSolvable.HasSeries.zero` and `.succ` provide constructors
from the corresponding data.

`SplitSolvable.HasSeries.of_splitSeries` sends a Ga-only series to a Ga/Gm
series by induction on its length, choosing the left disjunct at each step.
`IsSplitSolvableGroupScheme.of_isSplitUnipotent` uses this conversion with
all four outer structure hypotheses supplied explicitly. It does not derive
those hypotheses from the series. The existing `RelativeRoot.HasSplitSeries`
and `RelativeRoot.IsSplitUnipotent` remain unchanged.
These recursive formulations and elementary laws are internal formal
packaging of the source definition.

## Imperfect fields and remaining structural obligations

Splitting is not inherited by arbitrary smooth connected subgroups over an
imperfect field, even when the subgroup is normal. In Example B.1.1, if the
characteristic is `p > 0` and `a ∈ k` is not a pth power, the subgroup of
Ga² cut out by `y^p = x - a*x^p` is smooth and connected, becomes Ga after
adjoining a pth root of `a`, but is not Ga over `k`. It is the source's
counterexample to inheritance of split solvability. This source example is
documented here; this module does not formalize it.

Showing that every split torus is split solvable with the required finite
Gm-series remains a separate structural obligation. This module supplies no
general subgroup inheritance, fixed-point theorem, properness or
pseudo-completeness theorem for quotients, radical existence, or conjugacy
conclusion, and includes none of those conclusions as fields.
