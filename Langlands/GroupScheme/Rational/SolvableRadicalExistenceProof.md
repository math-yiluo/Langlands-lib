# Existence of the represented ground-field solvable radical

Original draft: Worker 1378. Current-Library verification and submission: Worker 1576.

`Langlands.GroupScheme.solvableRadicalExistence` proves
`SolvableRadicalExistenceStatement.{u}` from
`Rational.SolvableRadicalExistenceStatement`. For every field `k`
and every actual group scheme `G` over `Spec k` with `Smooth G.X.hom`,
`IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`, it constructs an actual
group scheme `R` and a morphism `r : R ⟶ G` with the published
`IsSolvableRadical r`. The proof uses no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`, and no structural-theorem premise.

The proof follows the published proof of `UnipotentRadicalExistenceStatement`
in `Reductive.UnipotentRadicalMaximal` and
`Reductive.UnipotentRadicalExistenceProof`, with unipotence replaced by
solvability.

## Candidates and minimal height

In the namespace `SolvableRadicalExistence`:

- `IsCandidate i` collects the conditions of `IsSolvableRadical i` other than
  greatestness: `i` is a closed subgroup, its source is smooth with connected
  underlying space, it satisfies `IsSolvableGroupScheme`, and its range is
  normal on every test scheme.
- `trivial_isSolvableScheme`: every point group of the trivial group scheme
  is trivial, because its underlying object is terminal, so it satisfies
  `RelativeRoot.IsSolvableScheme` with derived length zero.
- `trivial_isCandidate`: the unit inclusion of the trivial group is a
  candidate. The closed-subgroup, smoothness, connectedness and normality
  parts are those of the published
  `UnipotentRadicalExistence.trivial_isCandidate`. Solvability comes from
  `trivial_isSolvableScheme` and the published comparison
  `RelativeRoot.IsSolvableScheme.isSolvableGroupScheme`.
- `exists_minimal_height_candidate`: when `G` is affine and locally of
  finite type, there is a candidate whose coordinate kernel has least height
  among all candidates. The height of a candidate's coordinate kernel is
  finite by the published `BorelExistence.coordinateKernel_height_ne_top`.
  The trivial candidate shows that some natural number occurs, and
  `Nat.find` selects the least.
- `range_eq_of_minimal_height`: if `i` and `j` are candidates, the height
  for `i` is at most that for `j`, and `range i ≤ range j`, then the ranges
  are equal. The containment gives a factorization `f` with `f ≫ j = i`.
  The published `isIso_of_coordinateKernel_height_le` makes `f` an
  isomorphism, so the inverse factorization gives the reverse containment.
- `isSolvableRadical_of_minimal_height`: a minimal-height candidate `i` is
  the solvable radical if every candidate `j` has a common candidate upper
  bound `p` with `range i ≤ range p` and `range j ≤ range p`. For a
  competitor `j`, minimality and the previous lemma give `range p = range i`,
  so `range j ≤ range i`.
- `IsCandidate.isSolvableScheme`: a candidate inside an affine `G` satisfies
  the all-test `RelativeRoot.IsSolvableScheme`. Its structure morphism is the
  closed immersion `i` followed by the affine structure morphism of `G`, so it
  is affine. The published
  `RelativeRoot.isSolvableScheme_of_isSolvableGroupScheme` for smooth affine
  groups then applies.

## The upper bound

`solvableRadicalExistence` chooses a minimal-height candidate `i : U ⟶ G`
and verifies the upper-bound hypothesis. For a candidate `j : V ⟶ G`, the
published `smoothConnectedNormalFppfProductExistence` supplies a smooth
connected closed subgroup `p : P ⟶ G` representing the fppf-local product
of `range i` and `range j`. It uses that `range i` is normal and that both
factors are smooth connected closed subgroups. The required local finite type
hypothesis on `G` follows from its smooth structure morphism. Then:

- `p` is a closed subgroup, by `IsFppfProduct.isClosedSubgroup`;
- `range p` is normal, by the published `IsFppfProduct.isNormal`, since both
  factor ranges are normal;
- `P` is solvable: `SubgroupFunctor.isSolvableScheme_of_isFppfProduct` from
  `SubgroupFunctor.FppfProductSolvable` makes `P` uniformly solvable on all
  tests, because `U` and `V` are (`IsCandidate.isSolvableScheme`), `i` is
  monic and `range i` is normal. The comparison
  `RelativeRoot.IsSolvableScheme.isSolvableGroupScheme` turns this into
  `IsSolvableGroupScheme P`;
- `range i ≤ range p` and `range j ≤ range p`, by `IsFppfProduct.left_le` and
  `right_le`.

So `p` is a candidate upper bound, and `isSolvableRadical_of_minimal_height`
gives `IsSolvableRadical i`.

## Relation to the source

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
proves the existence of the largest smooth connected normal subgroup with a
property stable under extensions and quotients in Proposition 6.42, printed
p.134 (PDF p.150). Its proof takes a maximal such subgroup and uses
Lemma 6.41, by which the product `H N` keeps the property. The
implementation uses a minimal coordinate-kernel height in place of a
maximal dimension. It uses the represented fppf product in place of `H N`,
and all-test uniform solvability in place of the quotient argument for
`H N / N`.

The source is the 2017 edition cited by the target statement, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The registered errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to
Lemma 6.41, Proposition 6.42 or §6.44. The target statement and its imports
are reused unchanged.
