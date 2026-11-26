# Derived étale compact-support comparison

## Source

Vladimir Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(1995–1996 unfinished manuscript), Proposition 1.5.1 and Corollary
1.5.2(i), printed and PDF pp. 10–12. The retained PDF,
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
has SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
It is in registered folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
[Author's copy, Corollary 1.5.2(i)](https://www.wisdom.weizmann.ac.il/~vova/Equish_1996.pdf#page=11)

The corollary's first assertion is the comparison in all degrees
`H_c^q(X{G}, F) ≅ H_c^q(X, b^*F)`. It follows from the degree-zero
inclusion of smooth compact sections and the softness in Proposition
1.5.1. This module states its derived consequence for the actual
bounded-below compact-section complexes.

## Lean proposition

`Langlands.Cohomology.AnalyticEtaleCompactComparison.AnalyticEtaleCompactDerivedComparisonStatement`
uses the same geometric and coefficient hypotheses as the
[cohomology comparison](Statement.md). These include a continuous
analytic action over a fixed complete ultrametric field `K` on a
Hausdorff analytic space `X`, and supports in the `L`-valued points
of `X`, with point axioms and surjectivity of `pointProjection L X`.
The group fits in the module universe by `Small G`, and the
admissible refinements for `distinguishedLiftSystem` provide the
category of étale `G`-sheaves and its derived compact-section functor.
The target uses coefficients in a commutative ring `R`, with separate
derived-category universes for smooth `R`-representations and for
`R`-modules.

The conclusion is invertibility of `etaleCompactComplexComparison`.
Its source is `RΓ_c(X{G}, -)` followed by the derived functor of exact
forgetting of the `G`-action. Its target is the restriction along
`b^*` followed by `RΓ_c(X, -)`. Both use the Library's actual
complex-valued functors. The comparison is a natural isomorphism of functors with values in
the derived category of `R`-modules.

`etaleCompactComplexComparison_homology` identifies the given map
on cohomology in degree `q ≥ 0` with `etaleCompactComparison` in that
degree. Both sides have vanishing negative cohomology because the
complexes are derived from sheaves placed in degree zero by right
derived functors, and forgetting the action is exact. Invertibility
in every cohomological degree therefore suffices to prove the
proposition. The geometric cohomology comparison remains the input
for that proof. The claimed isomorphism has module coefficients
after forgetting the action. Smoothness and the comparison in
smooth representations on cohomology use the separate action
compatibility from `AnalyticEtaleCompactSmoothness`.
