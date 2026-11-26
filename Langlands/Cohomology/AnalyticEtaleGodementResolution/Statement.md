# Exact compact-acyclic Godement resolutions on the analytic étale site

## Sources

Vladimir Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(1995–1996 unfinished manuscript), §1.5(a)–(b), exactness property (ii)
and Proposition 1.5.1, printed and PDF pp. 10–11, and the proof of
Corollary 1.5.2(i), pp. 11–12. The retained file
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
It is in registered folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
[Author's copy, §1.5](https://www.wisdom.weizmann.ac.il/~vova/Equish_1996.pdf#page=10)

Michael Harris, *Galois properties of cohomological automorphic forms on
GL(n)*, J. Math. Kyoto Univ. 39 (1999), §2, printed p. 304 (PDF p. 6),
Fact 3 and Lemma 2.2, and p. 305 (PDF p. 7), (2.3). Registered ID
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Berkovich takes the adjunction map to `ν_*ν^*`, then applies the same
functor to successive cokernels. Every term functor is exact. The
restriction of each term is soft by Proposition 1.5.1, which gives
compact-support acyclicity in the proof of Corollary 1.5.2(i). The
comparison in that corollary identifies the derived smooth and ordinary
compact cohomologies. Harris uses the compact-support acyclicity and the
exactness of the first functor to construct his resolution in smooth
sheaves, compatibly over the torsion levels.

## Lean proposition

`Langlands.Cohomology.AnalyticEtaleGodementResolutionStatements` concerns
module sheaves over one commutative ring `R` on the Library's analytic
étale site over a fixed complete ultrametric field `K`. The base `X` is
Hausdorff and `ρ : G →* Aut X` is a continuous analytic action of a
topological group by automorphisms over `K`. Smallness of `G` in the
module universe `max u (v + 1) uL` and admissible refinements for
`distinguishedLiftSystem` supply the categorical infrastructure. The
normed field extension `L` carries the stated point axioms, and its
`L`-valued points cover `|X|` by the map `pointProjection L X`. The same
points index the Godement construction and test compact support. This
is the Library's point model, with the étale `G`-sheaves in the locally
discrete subcategory of the twisted site. The identification with
modules on the equivariant site uses the separate Theorem 1.4.2
comparison. No restriction on residue characteristics is needed for
this Godement assertion.

The specific functor is `etaleGodementZeroFunctor` and the map into it
is `etaleGodementCoaugmentation`. The first clause gives additivity
and preservation of finite limits and colimits for every
`CokernelComplex.term` of this construction, including degree zero.
The second gives a quasi-isomorphism from the sheaf in degree zero to
the constructed complex via `CokernelComplex.augmentationMap`. The
last clause gives vanishing in each positive degree for each term,
both on the underlying restricted étale sheaf and in the smooth
compact-support functor. This expresses the acyclicity consequence of
Berkovich's softness assertion. The literal softness condition and
Harris's coefficient systems are separate from this proposition.

## Ingredients for a proof

`etaleRestrictedGodementPointProductIso` identifies the restricted
zero term with the actual point product in the stalk coefficients.
The product is exact in its coefficients by
`coefficientRestrictedSmoothPointProductFunctor_preservesHomology`.
Together with exactness of the stalk functors and faithful exact
restriction, this gives the route to exactness of the smooth zero
term. Joint point-fiber faithfulness is supplied by
`analyticEtalePointFibersJointlyFaithful`, and gives a monic
coaugmentation by `mono_etaleGodementCoaugmentation_of_jointlyFaithful`.
The generic `CokernelResolutionStatement` and
`CokernelResolutionFunctorExactnessStatement` express the subsequent
cokernel arguments.

For compact acyclicity, `AnalyticEtaleGodementCompactAcyclicStatement`
is the degree-zero case on the ordinary site. Every term is itself the
zero functor applied to the corresponding residual sheaf. The
isomorphism of `AnalyticEtaleCompactComparisonStatement` supplies the
vanishing for the smooth compact functor as well. The resolution
proposition includes these conclusions without assuming these
comparison or acyclicity statements in its type.
