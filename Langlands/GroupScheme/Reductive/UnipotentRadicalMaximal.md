# Finite-height maximal normal unipotent subgroups

This derived unit defines `UnipotentRadicalExistence.IsCandidate` as the five
conditions in the published `IsUnipotentRadical` preceding greatestness: a closed
immersion, smooth connected source, fixed-vector unipotence, and normal range on
every relative scheme test. It changes none of the published predicates.
The candidate predicate and the trivial-candidate lemmas allow any ambient group
scheme over the field; they impose no ambient affineness or finite-type condition.

The trivial group is a candidate. Its functor of points is terminal, so each of
its points is the identity and every coefficient representation fixes every
vector. A constant vector with value one witnesses unipotence for each nonempty
finite coordinate index. The unit inclusion is closed, smooth over the field,
connected, and has identity range on all tests; the latter is normal.

The height, rigidity, and final greatestness lemmas assume that the ambient group
scheme `G` is affine and locally of finite type over the field, expressed by
`IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`. The host existence target
supplies the latter condition through its smoothness hypothesis.
Under these ambient hypotheses, the implemented maximality argument reuses the published
`BorelExistence.coordinateKernel` and its finite prime-height and rigidity
lemmas. Coordinate-kernel heights of candidates are finite.
`Nat.find` therefore chooses a candidate of least height. An inclusion from it
into another candidate is an isomorphism by
`isIso_of_coordinateKernel_height_le`; composing with the inverse proves
equality of their ranges on every test scheme.

With the same ambient affine and locally finite-type hypotheses, the final lemma
proves greatestness **under an explicit common-upper-bound hypothesis**:
combine the chosen candidate with each competitor inside a further
candidate, identify the first and third ranges by minimal height, then transfer
the competitor's containment. No product representative is constructed here,
and this lemma does not establish `UnipotentRadicalExistenceStatement` without
discharging that structural hypothesis.

The mathematical route is Milne, *Algebraic Groups* (2017), Proposition 6.42
(printed p.134), with finite prime-kernel height replacing greatest dimension.
Corollary 14.8 (printed p.282) applies that proposition to unipotence. This unit
implements the order-theoretic part of that argument; the product closure in
Lemma 6.41 and Corollary 14.7 remains a separate obligation.
