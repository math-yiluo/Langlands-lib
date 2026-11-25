# Natural group actions on the constructed Deligne Nilp functor

This module packages the natural automorphisms of
`nilpSheafClassFunctor` as group homomorphisms. It supplies corrected-pair,
normalized GL, and actual PGL right actions, their component formulas, scalar
triviality, and the associated ordinary left PGL action.

The original background is V. G. Drinfel'd, *Coverings of p-adic Symmetric
Regions* (1976), Section 2 A, printed pp.109–110 (PDF pp.3–4): the four-data
point description and conditions (a)–(c), and the natural PGL action in the
theorem on printed p.109. Registered source:
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.

These are derived constructions on the point model. The natural
automorphisms come from `DeligneActionBaseChange`. Their component group laws
come from `DeligneShiftReframe` and `DeligneProjectiveAction`; the normalized
correction and scalar triviality come from `DeligneValuedReframe` and
`DeligneScalarClass`. This module proves that these actual natural operations
obey the group laws, rather than taking such laws as additional inputs.

## Parameters and conventions

All carriers have one common universe u. The corrected-pair results assume a
commutative ring O, a positive dimension d, an element pi of O, and an O-algebra
field F in which the image of pi is nonzero. The functor is defined on the
existing category `FormalGroup.Nilp O pi` of O-algebras with nilpotent image of
pi, with values in `Type (u + 1)`.

The normalized and projective results additionally assume that O is a discrete
valuation domain, F is its fraction field, and pi is irreducible. These data
supply the nonzero scalar used in the point functor. The normalized operation
uses shift k equal to minus the coefficient order of det(g), with new degree i
equal to old degree i+k. The corrected subgroup consists of pairs (g,k) for
which pi^k det(g) is the image of an integral unit; its preservation of the
admissibility condition is already proved in the imported modules.

Write A(g) for the natural automorphism given by a frame change. The existing
frame precomposition convention satisfies

    A(g*h) = A(h) * A(g).

Here multiplication in `CategoryTheory.Aut` is function-composition order:
`f * g = g.trans f`, so its forward component applies g and then f. The
homomorphisms for this right convention therefore take values in the
multiplicative opposite of the natural automorphism group. Their evaluations
are exactly the point operations, with no change of convention.

## Corrected and normalized homomorphisms

`nilpSheafShiftReframeAut_one` and `nilpSheafShiftReframeAut_mul` prove the
identity and reversed product laws as equalities of natural automorphisms.
Their proofs use `Aut.ext`, natural-transformation extensionality, and function
extensionality at each Nilp algebra and each genuine admissible class. The
existing class identity and product laws close the resulting component goals.
Thus inverse components and naturality remain those of the imported natural
isomorphisms.

`nilpSheafShiftReframeHom` packages these two laws as a homomorphism from the
corrected subgroup to the opposite natural automorphism group. Its
`*_hom_app` equation identifies evaluation with
`SheafDatum.IsoClass.shiftReframe`.

`nilpSheafNormalizedReframeHom` composes this homomorphism with
`normalizedReframeHom`, the canonical determinant correction on linear
self-equivalences of F^d. Its `*_apply` and `*_hom_app` equations identify its
values with `nilpSheafNormalizedReframeAut` and its components with
`SheafDatum.IsoClass.normalizedReframe`.

`nilpSheafNormalizedReframeAut_scalar` applies the proved scalar-triviality
theorem to every component, giving the identity natural automorphism for every
unit of F. `nilpSheafNormalizedReframeHom_scalar` states the same fact in the
opposite group. `nilpSheafNormalizedReframeHom_scalarMatrix` translates it to
actual scalar matrices via `matrixReframeEquiv_scalar`.

## Actual projective action and the ordinary left convention

`nilpSheafProjectiveReframeAut_mk` identifies the natural automorphism of an
actual matrix class with the normalized automorphism of that matrix's linear
frame map. Component extensionality reduces this to the
`projectiveReframe_mk` equation. The actual PGL identity and reversed product
laws follow in the same way from the pointwise projective laws.

`nilpSheafProjectiveReframeHom` packages these laws into a homomorphism from
Mathlib's actual `PGL(d,F)` to the opposite natural automorphism group.
`nilpSheafProjectiveReframeHom_mk` gives its matrix representative formula,
and `*_hom_app` gives its actual pointwise evaluation. This reuses the existing
projective quotient action; no additional representative choice or assumption
of scalar invariance is made.

`nilpSheafProjectiveLeftHom` is an ordinary homomorphism from PGL to the natural
automorphism group. Its value at g is A(g inverse). The reversed product law
and `(g*h) inverse = h inverse * g inverse` prove multiplicativity. Its
`*_hom_app` equation gives inverse projective precomposition, and
`*_mk_hom_app` expresses the result on a matrix class as the normalized frame
change of the inverse matrix. These agree with the pointwise
`projectiveLeftAction` convention.

## Scope

The constructions act on the existing admissible four-data classes and the
existing scalar-aware Nilp functor. The independent comparison of the model's
determinant condition with equality of exterior-power subsheaves is proved in
`DeligneDeterminantSubsheaf` (`determinantSubsheavesNormalized_iff`);
comparison with special formal modules, representability, and level coverings
remain separate. No representing object, universal object, uniformization
map, or such theorem is constructed or assumed in this module.
