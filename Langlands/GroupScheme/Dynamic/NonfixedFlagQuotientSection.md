# A nonfixed section of an actual homogeneous quotient

This internal construction concerns a smooth connected group scheme `G` over
an algebraically closed field `k : Type u`, an actual maximal torus `i : T → G`,
and a closed subgroup `j : P → G`. It assumes a factorization of `i` through
`j`, conjugacy of maximal tori inside `P`, and containment of the whole-torus
centralizer's rational points in `P(k)`. The subgroup functor represented by
`j` must differ from the whole group.

The supplied morphism `q : G → Q` is flat, surjective and quasi-compact, and
its fibers on every scheme test are exactly right `P`-cosets. The target is
locally of finite type and separated over `k`; it need not be proper, smooth
or reduced. The canonical quotient action is the actual descended action
from `Dynamic.FlagQuotientSchemeAction`.

`Dynamic.nonfixedFlagQuotientLift` assumes finiteness of the actual quotient
`relativeWeylGroup i = N(k)/Z(k)`. It returns a rational group point `g` together
with a proof that its quotient section `g ≫ q` is not fixed by the restricted
torus action on all scheme tests.

The construction proves existence by contradiction. If every lifted section
were torus-fixed, every rational section of `Q` would be fixed: algebraic
closedness, local finite type of `G`, and surjectivity of `q` give rational lifts.
The published `torusFixedPointWeylEmbedding` then embeds all these fixed sections
into the finite actual Weyl quotient. Hence `Q(k)` is finite.

The published `SchemeAction.isFixed_of_finite_rationalPoints` applies to the
full connected smooth `G`-action. It makes the identity quotient section fixed
by `G` on all tests. The exact fiber law then says that every test point of
`G` belongs to the range of `j`, contradicting properness of that subgroup
functor. The definition chooses the resulting nonfixed lift with
`Classical.choice`.

`Dynamic.rankOneNonfixedFlagQuotientLift` specializes to connected reductive
`G`, a split maximal torus, and pairwise integral dependence of all actual
roots. The published rank-one Weyl sign embedding supplies finiteness by
embedding the Weyl quotient into `Bool`. No assumption about the existence of
a nonidentity Weyl class is needed for this step.

The provenance is internal: the rational-lifting argument is the one used in
`Dynamic.RankOneFixedCosetBound`; fixed-point finiteness comes from
`Absolute.TorusFixedCosetBound`; the connected-action argument comes from
`SchemeActionFiniteTarget`; and the identity-section comparison uses
`SchemeActionQuotientIdentity`. The remaining geometric inputs are explicit.
This construction does not produce a proper quotient or its line stabilizer,
prove centralizer containment in an arbitrary prescribed subgroup, establish
a dimension bound, or prove `RankOnePositiveRootUniquenessStatement`.
