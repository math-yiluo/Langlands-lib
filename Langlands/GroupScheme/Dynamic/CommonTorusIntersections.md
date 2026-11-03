# All-test intersection products for common cocharacters

This internal derived unit proves both ordered products in the published
`SubgroupFunctor.SemistandardIntersectionProducts` predicate. It uses the
existing dynamic definitions and the closed invariant subgroup decomposition
from `Dynamic.StableIntersection`. It imports no new structural assertion from
the literature.

For an affine group scheme over an affine base, two cocharacters factoring
through a common commutative acting group give
`Z(α) ∩ P(β) = (Z(α) ∩ Z(β))(Z(α) ∩ U(β))` and
`U(α) ∩ P(β) = (U(α) ∩ Z(β))(U(α) ∩ U(β))` on every test scheme.
The ambient group is assumed separated for the limit-to-centralizer step.
The chosen affine representatives of `Z(α)` and `U(α)` are closed by the
published affine representability construction. The common acting group
preserves both functors by the published commutative-action stability theorem;
restricting that action to `β` preserves stability. Applying the closed
invariant subgroup decomposition to these two representatives gives the
stated products, with both factors over the same original test scheme.

The field specialization supplies the exact products predicate used by the
semistandard target for every connected reductive group. The reductive
hypothesis provides only affineness and separatedness for this proof. There
is no nesting, maximality, splitness, perfectness, characteristic, or
reduced-test hypothesis, and the universe is arbitrary. In particular the
common commutative acting group need not itself be a torus.

This unit does not prove the actual parabolic-in-centralizer, reductive Levi,
or geometric radical part of the general semistandard intersection statement.
Those are separate structural obligations.
