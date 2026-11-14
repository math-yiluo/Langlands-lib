# Acyclicity after restriction of injective quasi-étale G-sheaves

Author: Worker 512.

`QuasiEtaleRestrictedInjectivesAcyclicStatement` isolates the higher-cohomology
vanishing premise needed by the compact quasi-étale comparison theorem. It is a
proposition definition, with no proof of the vanishing claim.

For a complete ultrametric normed field K, an analytic space X, a topological
group G and an action ρ, it assumes that X is compact and Hausdorff and that ρ is
continuous. For every injective object I in the category of quasi-étale G-sheaves
of R-modules and every natural number q, it asserts

`IsZero ((quasiEtaleCohomology X R (q + 1)).obj ((quasiEtaleGSheafRestriction ρ R).obj I))`.

The sheaf category, restriction b*, and cohomology are exactly the published
constructions used by `AnalyticQuasiEtaleGlobalComparisonStatement`. In
particular, injectivity is in the category of discrete quasi-étale G-sheaves,
and the vanishing is in ordinary quasi-étale cohomology after forgetting the
G-action. The statement retains the same smallness and finite equivariant
refinement instance as the comparison target. It does not assume any of the
unproved action-lift or refinement propositions. The coefficient ring R is any
commutative ring in `Type (max u (v + 1) uL)`, with modules in that universe;
K, X, and G retain all universes of the published target.

The source is Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*,
unfinished 1995–1996 manuscript, printed/PDF p.13, proof of Theorem 1.6.1(ii),
the paragraph beginning “We claim that if X is compact”. Source ID:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder `Berkovich (1995-1996), Etale equivariant sheaves on p-adic analytic spaces, Equish_1996 manuscript`,
file `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`.
The source states the abelian-sheaf version. This is its module-coefficient
analogue, needed for the already published module-coefficient comparison target;
it asserts injectivity and derived cohomology within the R-module sheaf
categories. It does not infer that forgetting R sends injectives to injective
abelian sheaves.

Berkovich's proposed route uses finite compact quasi-étale covers, lifts over
sufficiently small open subgroups, preservation of injectivity under restriction
to those subgroups, and a filtered-limit description of the Čech groups. This
module records only the resulting vanishing obligation. It supplies none of
those auxiliary bridges and makes no claim that they have been formalized.
