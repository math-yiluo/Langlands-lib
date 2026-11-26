# Derived global étale comparison on compact analytic spaces

## Source

Vladimir Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(1995–1996 unfinished manuscript), Theorem 1.6.1(ii), printed and PDF
pp. 13–14. The retained PDF,
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
has SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
It is in registered folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
[Author's copy, Theorem 1.6.1(ii)](https://www.wisdom.weizmann.ac.il/~vova/Equish_1996.pdf#page=13)

The first assertion of Theorem 1.6.1(ii) gives the comparison
`H^q(X{G}, F) ≅ H^q(X, b^*F)` for compact `X`. This module states its
derived consequence for étale sheaves of modules, using the same
hypotheses as the [degreewise comparison](Statement.md).

## Lean proposition

`Langlands.Cohomology.AnalyticEtaleGlobalComparison.AnalyticEtaleGlobalDerivedComparisonStatement`
uses a compact Hausdorff analytic `X` over a fixed complete ultrametric
field `K`, with a continuous analytic action `ρ` of a topological
group `G` over `K`. The `Small G` instance places `G` in the module
universe. The admissible refinements for the distinguished étale lift
system give the category of étale `G`-sheaves and its derived global
section functor. Coefficients are in a commutative ring `R`, with
independent derived-category universes for smooth `R`-representations
and for `R`-modules.

The conclusion is `IsIso` of the natural transformation
`etaleComplexComparison`. Its source takes derived smooth global
sections `RΓ(X{G}, -)` and applies the derived functor of exact
forgetting of the action. Its target restricts an étale `G`-sheaf by
`b^*` and takes ordinary derived global sections `RΓ(X, b^*(-))`.
Both use the Library's bounded-below global-section complexes in
the derived category of `R`-modules.

`etaleComplexComparison_homology` identifies the map on cohomology
in every degree `q ≥ 0` with the degreewise `etaleComparison`, under
the canonical cohomology identifications. The smooth and ordinary
complexes have zero negative cohomology, and exact forgetting of the
action preserves that vanishing. A morphism in the derived category
is invertible when it induces isomorphisms in all cohomological
degrees. This gives the derived implication from the degreewise
theorem.
