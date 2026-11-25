# Base-change naturality of the actual Deligne class actions

This module proves that the constructed shift and frame operations on Deligne
four-data classes commute with actual scheme base change. It constructs their
natural automorphisms on `nilpSheafClassFunctor`, including one for every element
of Mathlib's actual matrix projective general linear group.

The source background is V. G. Drinfel'd, *Coverings of p-adic Symmetric Regions*
(1976), Section 2 A, printed pp.109–110 (PDF pp.3–4): the four-data point
description and conditions (a)–(c), and the natural PGL action mentioned in the
theorem on printed p.109. Proposition 2.4 on printed p.110 motivates
base-change compatibility for four data attached to special formal modules.
Registered source: `drinfeld-1976-coverings-p-adic-symmetric-regions`,
SHA256 `7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.

The declarations here are derived infrastructure on the four-data
point model. They use the actual comparisons of `DeligneShiftBaseChange`, the
arithmetic action of `DeligneShiftReframe`, its DVR specialization in
`DeligneValuedReframe`, the scalar quotient in `DeligneProjectiveAction`, and the
actual scalar-aware Nilp functor in `DeligneNilpFunctor`. They do not assert the
formal-module comparison in Proposition 2.4.

## Parameters and conventions

All carriers have a common universe u. The general declarations use a
commutative ring O, a positive integer d, an element pi of O, and an O-algebra
field F. Integer shifts and admissible classes require that the image of pi in
F is nonzero. The class pullbacks use arbitrary scheme maps f: S' → S and
phi: O → Gamma(S, top), with target scalar map `pulledGlobalScalar f phi`.
The scalar-aware versions allow any proved equality of that map with a
specified phi'. No flatness or nilpotence hypothesis on f is required.

The normalized and projective declarations additionally assume that O is a
discrete valuation domain, F is its fraction field, and pi is irreducible.
These hypotheses construct the required nonzero scalar and the normalized
determinant correction. The correcting shift is minus the coefficient order
of det(g); new degree i is old degree i+k. Frame precomposition follows the
right-action convention.

The Nilp declarations use the existing category of O-algebras in which pi
has nilpotent image, its actual contravariant affine scheme map, and the
proved naturality of `nilpGlobalScalar`.

## Descent of actual comparisons

`SheafPreDatum.IsoClass.pullback_shiftInt` descends the genuine
`pullbackShiftIntIso` by quotient induction and quotient soundness. This
comparison preserves the full frame and u, as required by the existing
isomorphism relation. `pullback_reframe` descends the corresponding equality
of complete preliminary objects. `pullback_shiftReframe` combines these two
equations.

For admissible classes, `SheafDatum.IsoClass.pullback_reframe` and
`pullback_shiftReframe` apply the injectivity of `toPreliminary`. Forgetting
admissibility commutes with both operations and pullback, so the preceding
preliminary equalities prove the desired admissible equalities. The
determinant-unit and corrected-pair operations retain the existing
arithmetically proved admissibility conditions.

`pullback_normalizedReframe` specializes the corrected-pair equation along
`normalizedReframeHom`. `pullback_projectiveReframe` uses induction on
Mathlib's actual PGL quotient. For each matrix representative, the
representative formula reduces its square to the normalized GL square.
No new choice of quotient representative or scalar-triviality assumption is
introduced.

Each `pullbackTo_*` theorem includes the specified equality of actual global
scalar maps. Substituting the target scalar map reduces the assertion to the
corresponding ordinary pullback equation; proof irrelevance removes dependence
on the equality proof.

## Natural automorphisms on Nilp

`nilpSheafClassMap_shiftReframe`, `nilpSheafClassMap_normalizedReframe`, and
`nilpSheafClassMap_projectiveReframe` apply these scalar-aware squares to the
actual affine scheme map of a Nilp morphism and
`nilpGlobalScalar_naturality`.

`nilpSheafShiftReframeAut` constructs a natural automorphism of the existing
`nilpSheafClassFunctor`. Its component at B is the categorical isomorphism of
types associated to the already constructed `shiftReframeEquiv`. The inverse
component comes from the inverse corrected pair. The proved square supplies
naturality; `NatIso.ofComponents` derives inverse naturality.

`nilpSheafNormalizedReframeAut` specializes this construction to the canonical
determinant-corrected pair. `nilpSheafProjectiveReframeAut` uses
`projectiveReframeEquiv` for each actual projective element and the projective
Nilp square. The three `*_hom_app` equations identify their forward components
with exactly the existing corrected, normalized, and projective operations.

## Scope

This module constructs natural automorphisms element by element. Packaging their
right-action product laws as homomorphisms to opposite natural automorphism
groups is done separately, in `DeligneNilpAction`. The imported point model and admissibility
predicate are retained. In particular, the independent comparison of its
determinant condition with an equality of exterior-power subsheaves is outside
this module; `DeligneDeterminantSubsheaf` proves it
(`determinantSubsheavesNormalized_iff`). This module asserts no representing or
universal object, formal-module comparison, representability theorem, or
level-covering theorem.
