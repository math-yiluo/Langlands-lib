# Fubini and measurable coordinates for smooth weak integration

This is an internal deduction from `SmoothWeakIntegral` and Mathlib's scalar
Fubini and change-of-variables theorems. It supplies an analytic step needed
for the standard-intertwiner factorization in Waldspurger, *La formule de
Plancherel pour les groupes p-adiques*, IV.1, printed p.279 / PDF p.45, and
the composition assertion IV.1(12), printed p.283 / PDF p.49. It does not
construct the complementary unipotent subgroups, their quotient coordinates,
or their normalized Haar measures.

The group `G` has a topology, and `rho` is a complex representation on an
algebraic vector space `V`. The measurable spaces `X`, `Y`, `Z`, the group,
and the vector carrier have independent universes. There is no norm or
topology on `V`. All weak integrals use the existing smooth contragredient,
and every representing vector belongs to `V` itself.

`ScalarProductIntegrable rho mu nu f` means that every smooth-functional
scalar test of `f : X × Y → V` is absolutely integrable for `mu.prod nu`.
It makes no representability assertion. For S-finite measures and jointly
almost-everywhere strongly measurable scalar tests,
`scalarProductIntegrable_iff` characterizes this condition by
almost-everywhere integrability in `X` and integrability in `Y` of the
integral in `X` of the absolute value. Convergence of iterated signed
integrals alone does not supply this condition.

Suppose `j y` represents the weak integral in `X` of `f (x,y)` for almost
every `y`. Under `ScalarProductIntegrable`, `hasIntegral_prod_iff` proves
that `v` represents the product weak integral exactly when it represents
the weak integral of `j` in `Y`. For each fixed smooth functional, the
fiber hypothesis identifies its partial scalar integral with its value on
`j` almost everywhere. Mathlib's `Integrable.integral_prod_right` gives
outer scalar integrability. `integral_prod_symm` then gives the equality of
the scalar integrals. The implication constructing a product integral is
also named `HasIntegral.prod`; existential quantification gives
`integrable_prod_iff`.

`integralLinear_prod` compares the existing chosen integrals on their
actual representability domains. It additionally assumes a topological
group, a smooth representation, and cofinal compact open subgroups, exactly
as required by `integralLinear` for uniqueness. Its proof applies the
product weak-integral relation and the existing uniqueness theorem. The
other Fubini results require neither separation nor smoothness of the
representation.

`hasIntegral_map_equiv_iff` transports the weak-integral relation along a
measurable equivalence with the exact pushforward measure. Its proof
applies `integrable_map_equiv` and `integral_map_equiv` to every scalar
test. `hasIntegral_measurePreserving_equiv_iff` gives the same equivalence
for a supplied target measure when the coordinate equivalence is
measure-preserving. These coordinate results require no S-finiteness.

For an application to Waldspurger's actual standard integrals, product
absolute convergence and the exact quotient-measure comparison remain
analytic and geometric obligations. This module does not assume them as
permanent reductive-structure inputs, and proves no rational continuation,
root-distance composition law, or Plancherel theorem.
