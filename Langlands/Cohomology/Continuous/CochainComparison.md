# The canonical continuous-to-ordinary cohomology map

Author: Worker 22. Task `c6ea3f74-2826-48db-9ab1-46587ae2dd92`, revision 1.

Let `k` be a commutative ring with a topology, let `G` be a topological
group, and let `A : TopRep k G`. All three carriers lie in arbitrary `Type u`.
The selected definition `Langlands.Continuous.continuousToOrdinary A q`
is a morphism in `ModuleCat k` from the underlying module of Mathlib's
`continuousCohomology q A` to the ordinary
`groupCohomology (Rep.of A.ρ.toRepresentation) q`. The coefficient action is
unchanged. This definition is available for every natural degree and does
not require discreteness, compactness, or an assumed comparison equivalence.

The source uses Mathlib's actual nested continuous homogeneous-cochain
complex. In degree `n`, its cochains are the invariant elements of
`TopRep.resolutionX A (n + 1)`. The recursive linear map `nestedEval`
evaluates the outer continuous function at the first coordinate and then
evaluates its value at the remaining coordinates. At level zero it returns
the coefficient. It is defined on the existing resolution, not on a
replacement complex.

The identity `nestedEval_action` proves that acting by `g` evaluates as
the action of `g` on the value at the tuple translated by `g⁻¹`. Invariance
therefore produces a covariant tuple function: its value at `g * x` is
`g` acting on its value at `x`. `covariantFunctions` is the submodule of
these functions. `covariantToRepHom` extends such a function linearly to the
diagonal permutation representation on the tuple basis. Equivariance is
proved on basis elements. Restriction to the basis gives the inverse
`repHomToCovariant`; the two inverse and linearity identities constitute
`covariantHomEquiv`. This elementary free-module equivalence does not assert
that continuous and arbitrary tuple functions coincide.

The canonical degree map `homogeneousTermMap` evaluates a nested invariant
cochain and applies this linear extension. Its value on a basis element
`single x r` is `r` times the nested evaluation at `x`.
`nestedEval_d` proves by induction that the actual nested differential
becomes the alternating sum of tuple deletions. The successor step expands
Mathlib's constant-minus-coinduced differential and separates the first
summand of the finite sum. This identity and the actual differential formula
for `Rep.standardComplex` certify `homogeneousComparison` as a cochain map
to `Hom(standardComplex, A)`.

`standardToInhomogeneousIso` applies linear Yoneda and the opposite/unop
complex functors to Mathlib's proved `Rep.barComplex.isoStandardComplex`.
It then uses the inverse of Mathlib's `groupCohomology.inhomogeneousCochainsIso`.
The composite `continuousToOrdinaryCochains` is thus a map to the existing
ordinary inhomogeneous cochain complex. These are explicit applications of
proved resolution isomorphisms, not an assumed equivalence of cohomology.

Finally, the forgetful functor from `TopModuleCat k` to `ModuleCat k`
preserves homology, as supplied by Mathlib's functor and homology instances.
The inverse of its `ShortComplex.mapHomologyIso` identifies the underlying
module of continuous cohomology with the homology of the forgotten complex.
Composing with the homology map of `continuousToOrdinaryCochains` defines
`continuousToOrdinary`.

This contribution defines the canonical maps with their intrinsic
linearity, equivariance and differential certificates. It does not claim
that these maps are isomorphisms. Invertibility for discrete groups,
compatibility with change of group and coefficients, the profinite
finite-quotient comparison, and transfer remain separate proof obligations.
The more general `TopRep` hypotheses are sufficient for this map; they do
not replace the joint continuity hypothesis on the discrete modules used
in the profinite comparison.

The original mathematical context is Serre, *Local Fields*, English
translation by Marvin Jay Greenberg, Springer, 1979, Chapter VII, Section 3,
printed pages 112–113 / PDF pages 118–119 (homogeneous covariant cochains
and conversion to inhomogeneous cochains), and Chapter X, Section 3,
printed pages 154–155 / PDF pages 160–161 (continuous cochains).
The recursive treatment of the nested model is derived implementation
work for the pinned Mathlib definitions.

Literature ID: `serre-1979-local-fields`.
Content SHA-256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Retained original: `C:/Central-Library/Serre--Local Fields--1979.pdf`.

The only project artifact dependency is environment
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1:
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The source imports Mathlib's continuous and ordinary cohomology
functoriality modules. No unpublished project construction is imported.
