# Finite-height maximal split normal unipotent subgroups

This derived unit defines `SplitUnipotentRadicalExistence.IsSplitCandidate` as
the six conditions in the published `IsSplitUnipotentRadical` that precede
greatestness. It extends the published
`UnipotentRadicalExistence.IsCandidate`, which records a closed immersion, a
smooth connected source, fixed-vector unipotence and normal range on every
relative scheme test. It then adds the published
`RelativeRoot.IsSplitUnipotent` of the source. It changes none of the published
predicates and introduces no second notion of splitness.
The candidate predicate and the trivial-candidate lemmas allow any ambient group
scheme over the field; they impose no ambient affineness or finite-type condition.

The trivial group has the empty split series `RelativeRoot.HasSplitSeries 0`.
At length zero this series asks only that the range of the identity morphism be
trivial on all tests, which is the published `range_trivial_eq_bot`. Together with the published
`trivial_isCandidate`, this makes the unit inclusion of the trivial group a split
candidate.

The height and greatestness lemmas assume that the ambient group scheme `G` is
affine and locally of finite type over the field, expressed by
`IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`. The host split-radical
existence target supplies the latter condition through its smoothness
hypothesis. Under these hypotheses, `exists_minimal_height_splitCandidate`
chooses a split candidate whose `BorelExistence.coordinateKernel` has least
height among all split candidates. The heights are finite by the published
`coordinateKernel_height_ne_top`, and `Nat.find` selects the least value.

With the same ambient hypotheses, `isSplitUnipotentRadical_of_minimal_height`
proves `IsSplitUnipotentRadical` for such a minimal split candidate **under an
explicit common-upper-bound hypothesis**. The hypothesis says that the chosen
candidate and every split competitor lie in the range of a further split
candidate. Given a competitor, the proof takes that upper bound and applies the
published `range_eq_of_minimal_height` to the chosen candidate and the bound.
That result identifies their ranges on every test because the chosen height is
minimal. The competitor's containment in the bound then transfers to the chosen
candidate. The remaining radical fields are the candidate fields. No product
representative is constructed here, and this unit does not establish
`SplitUnipotentRadicalExistenceStatement` until the upper-bound hypothesis is
discharged.

The route follows Milne, *Algebraic Groups* (2017), Proposition 6.42 (printed
p.134). It replaces greatest dimension by least finite prime-kernel height, as
in the published `UnipotentRadicalMaximal`. The split radical is the object
whose existence Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), assert in the discussion preceding Proposition 2.2.4, printed p.63
(PDF p.89). Closure of split smooth connected unipotent normal subgroups under
products is a separate obligation, and this unit does not prove it.
