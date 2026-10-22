# Spherical test vectors and Jacquet's restriction-invariance clause

The coefficient field is the complex numbers. The matrix field and the two
representation carriers have independent universes. The matrix field carries
the supplied valuation; the regularity section also uses its supplied
topology and the nonarchimedean local-field hypothesis. No topology is placed
on a representation carrier. The smaller positive rank is `n + 1` and the
larger rank is `(n + 1) + 1`, so the case of a rank-one spherical test against
a rank-two representation is included.

## Spherical tests

The representation `σ` of `GL_(n+1)(F)` and the functional
`ℓ ∈ functionals (upperUnipotent (n + 1) F) θ σ` are explicit, for an arbitrary
character `θ` of the actual upper unitriangular group. The coefficient image
`coefficientModel σ ℓ` and its right-translation action `modelRepresentation σ ℓ`
are the published constructions of `Langlands.Representation.Whittaker.Algebraic`.
Taking `θ` to be the source's standard character (or its inverse) gives the
source's Whittaker model; the definitions here do not depend on that choice.

`sphericalModelSpace σ ℓ` is exactly the published level-zero fixed subspace
`levelFixedVectors (modelRepresentation σ ℓ) 0` of the coefficient image.
`mem_sphericalModelSpace` proves that this condition is equivalent to right
invariance of the model function under the actual image of `GL_(n+1)(O_F)`,
using the published identification of the level-zero subgroup with the
integral subgroup.

`modelEvaluation σ ℓ` is evaluation at the identity, constructed as a linear map
on the coefficient image. `SphericalTest σ ℓ` is the subtype of spherical
vectors with identity value one. Given a specified spherical vector with
nonzero identity value, `normalizeSphericalTest` constructs one by inverse
scaling. For the function `sphericalTestFunction σ ℓ w` of a test, the module
proves the normalization `W(1) = 1`, right `GL_(n+1)(O_F)` invariance,
left `θ`-covariance `W(u g) = θ(u) W(g)`, and that the test is not the zero
model vector. `nonempty_sphericalTest_iff` proves that a test exists exactly
when identity evaluation is nonzero on some spherical vector. The subtype may
be empty: existence, one-dimensionality of the spherical space, the Hecke
eigenfunction property and the Satake parametrization of the source's
spherical functions are neither assumed nor proved here.

Over a nonarchimedean local field, `sphericalTest_isSmoothVector` proves that
each test is a smooth vector of the coefficient-image representation, because
it is fixed by the published open subgroup `levelOpenSubgroup F n 0`.
`sphericalTestFunction_isLocallyConstant` proves that its function is locally
constant: for each `g`, the open set `g · K`, where `K` is that open level-zero
subgroup, contains `g`, and right `K`-invariance makes the function constant
on it. Openness is the published `OpenSubgroup` field, and continuity of left
multiplication comes from Mathlib's topological-group structure on the
general linear group. These assertions do not require the whole source
representation `σ` to be smooth.

## Restriction invariance

The representation `π` of `GL_((n+1)+1)(F)` and the functional
`ell ∈ functionals (upperUnipotent ((n + 1) + 1) F) θ' π` are again explicit,
for an arbitrary character `θ'`. `IsIntegralInvariantOnRestriction π ell w`
encodes exactly the additional invariance clause after Jacquet's corrected
Theorem 1: for every `g ∈ GL_(n+1)(F)` and every `k` in the actual integral
image of `GL_(n+1)(O_F)`,

`W(diag(g k, 1)) = W(diag(g, 1))`,

where `diag(g, 1)` is the published `rankInclusion 1 g`. Only the restriction
of the larger function to `diag(GL_(n+1), 1)` is tested; the predicate is not
strengthened to an invariance assertion on the whole larger group. The source
fixes an additive character `ψ` of conductor `O_F` and uses
`θ_(r,ψ)(u) = ψ(Σ_(1 ≤ i ≤ r-1) u_(i,i+1))`; the predicate is stated for an
arbitrary character `θ'` because the clause does not involve the character.
This is a derived generalization, not a change of the source condition.

`rankInclusion_mem_congruenceSubgroup` proves that the embedded smaller
integral group lies in every larger congruence group, over any subring of a
field and any ideal of that subring. An actual integral representative is
mapped by the published block inclusion. Its final row is exactly the
identity row, so its row differences lie in every ideal. Entrywise
compatibility of the block inclusion with the coefficient map identifies
the field-valued matrix. Consequently
`isIntegralInvariantOnRestriction_of_mem_levelFixedVectors` proves that every
coefficient-image vector fixed by some level subgroup `K_((n+1)+1)(a)`
satisfies the restriction-invariance condition. This is an algebraic
implication; it supplies neither a nonzero fixed vector nor the essential
integral identity.

## Provenance and scope

Hervé Jacquet, *A correction to Conducteur des représentations du groupe
linéaire*, Pacific Journal of Mathematics 260 (2012), 515–525,
DOI 10.2140/pjm.2012.260.515.

- Literature ID: `jacquet-2012-conductor-correction`.
- SHA-256: `98f02c2aef04bff162c1ceb0a42dd122da746d1304a90d82366a848f22713adf`.
- Retained PDF:
  `/home/taskhub/central-library/Jacquet--A correction to Conducteur des representations du groupe lineaire--2012.pdf`.

The additive character of conductor `O_F`, the measure normalizations and
`θ_(r,ψ)` are on pages 515–516. The spherical function `W(g; x; ψ)`, with
right `G_r(O_F)` invariance, left character covariance, the Hecke
eigenfunction property and `W(e) = 1`, is on page 516. Theorem 1 and the
following restriction-invariance uniqueness clause are on page 517. These
pages were read directly.

This pair is a derived preparation for Theorem 1. The source's spectrally
indexed spherical functions, their Satake properties, the corank-one integral
with `|det g|^(s - 1/2)` (page 517, and page 519) and the normalized
L-polynomial must still be constructed before a test from this space can
instantiate the theorem's identity; the integral is deliberately not part of
this module. It does not define an essential vector by choosing an arbitrary
nonzero newvector or an unconstrained factor function. Statements of the
corrected existence and uniqueness theorems are owned by Worker 11's
statement task.

## Dependencies

Imports are the published modules
`Langlands.Representation.Conductor.Definitions` (with its import
`Langlands.Representation.Conductor.Congruence`),
`Langlands.Representation.Whittaker.Algebraic`,
`Langlands.Group.GL.RankMaps` and `Langlands.Group.GL.UpperUnipotent`, all
present in Library commit `3b5205fa6ae98b1b2f57b8bfc33e99d78771f240`, and
Mathlib's `Mathlib.Topology.LocallyConstant.Basic` for `IsLocallyConstant`.
Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Worker 43 authored this module.
