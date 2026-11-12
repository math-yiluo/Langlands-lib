# Renard IV.3.3: coefficient independence

Author: Worker 89.

`Langlands.Renard.CompactRepresentation.coefficientLinearIndependence`
proves the exact published `CoefficientLinearIndependenceStatement`, with
independent group and carrier universes. The source is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, IV.3.3 Corollary, printed p.102 / PDF p.108. Source ID:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256:
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Scope and provenance

The final theorem retains all hypotheses of the published target, including
the given Haar measure, essential square integrability, irreducibility,
pairwise absence of smooth-representation isomorphisms, the common central
character, and the nonzero vectors and smooth functionals. No hypothesis is
added. The analytic and central-character premises are not needed by the
stronger algebraic helper proved here.

Renard obtains the corollary by integrating against selected reverse
coefficients and applying Schur orthogonality. The implemented proof instead
uses Mathlib's independently proved algebraic independence of distinct
simple isotypic components. It therefore does not depend on a proof of the
Schur orthogonality component or on admissibility.

## Coefficients as equivariant maps

`coefficientRightRegular G` abbreviates the published
`Whittaker.rightTranslation ℂ G`, the representation on all actual functions
`G → ℂ` with right action `(h ⋅ f)(g) = f(gh)`. There is no topology on this
function carrier. Fixing an algebraic functional `ℓ` makes the published
matrix-coefficient map into the actual intertwiner
`coefficientRightIntertwiner ρ ℓ` from `ρ` to this right regular representation.
This name abbreviates the existing
`HarishChandraSchwartz.coefficientIntertwiningMap ρ ℓ`; integration removes
the repeated construction while retaining its exact carrier and action.
The equivariance equation is exactly `ρ(gh) = ρ(g)ρ(h)`.

If `ρ` is irreducible and `ℓ` is nonzero, this map is injective. Schur's
injective-or-zero lemma for a simple source supplies the alternative, and
evaluating a zero coefficient map at `g = 1` would force `ℓ = 0`.
This is `coefficientRightIntertwiner_injective`.

## Independent isotypic components

`coefficients_linearIndependent_of_irreducible` works for an arbitrary
index type, pairwise nonisomorphic irreducible smooth representations,
nonzero vectors, and nonzero algebraic functionals.
It transfers their coefficient intertwiners to linear maps over the group
algebra through `IntertwiningMap.equivLinearMapAsModule`. The image `N i`
is isomorphic to the simple source module, so it is simple. It lies in its
isotypic component `P i` of the ambient right regular module.

The components `P i` are distinct. If `P i = P j`, the characterization
`isIsotypicOfType_submodule_iff` applied to the simple submodule `N i`
would give an isomorphism `N i ≃ N j`. Composing with the source-image
isomorphisms would produce an invertible intertwiner, hence an actual
smooth-representation isomorphism `π i ≅ π j`, contrary to the hypothesis.

Mathlib's `sSupIndep_isotypicComponents`, restricted along this injective
index map, gives independence of `P`. In a finite linear relation among
coefficients, each scalar multiple is a vector in its own `P i`. The
independent-submodule finite-sum criterion forces every such multiple to
vanish. Injectivity of the coefficient map gives `a i • x i = 0`, and
`x i ≠ 0` forces `a i = 0`. This proves linear independence over `ℂ`
without imposing a domain condition on the group algebra.

The final exact theorem applies this helper to `Fin r` and to the underlying
algebraic functionals of the target's smooth-dual vectors. Their nonzeroness
passes through the injective subtype inclusion. All helper definitions and
arguments are internal derived constructions from published objects and
Mathlib's simple-module API.
