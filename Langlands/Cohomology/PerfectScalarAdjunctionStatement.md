# Canonical scalar extension adjunction for strictly perfect sources

Author: Worker 606. This is an internal algebraic prerequisite for the relative
rigidified cube project, not a geometric base-change assertion.

For arbitrary commutative rings `R S : Type u`, including universe zero, an actual
ring homomorphism `φ : R →+* S`, and an actual strictly perfect cochain complex `K`
of `R`-modules, `PerfectScalarAdjunctionStatement.{u}` asserts a bijection

`Hom_D(S)(Q(baseChange φ K), Q L) → Hom_D(R)(Q K, Restrict_D(φ)(Q L))`

for every actual cochain complex `L` of `S`-modules. Strict perfection is exactly
the published `IsStrictlyPerfect`: boundedness above and below and finite
projectivity in every degree. The proposition quantifies the rings and ring
structures, homomorphism, complexes, and strict-perfection proof in that order.
It uses Mathlib's actual derived categories with the standard localization
instances, the same convention as `LocalMinimalPerfectStatement`. No field,
noetherian, coherence, flatness or finite-dimensionality assumption is imposed.

The asserted bijection is a specified function, not just the existence of an
arbitrary equivalence. `scalarExtensionComplexUnit φ K` has degree component
`(ModuleCat.extendRestrictScalarsAdj φ).unit.app (K.X i)`, the usual tensor unit
`x ↦ 1 ⊗ x`. Naturality of the module unit proves the chain-map equality.
`scalarExtensionDerivedUnit φ K` applies the actual localization functor `Q` to
this chain map and then composes with the inverse of
`(ModuleCat.restrictScalars φ).mapDerivedCategoryFactors` at `baseChange φ K`.
Scalar restriction is exact for any ring homomorphism, as supplied by Mathlib's
`ChangeOfRingsExact`. Its functor on derived categories therefore exists without
a flatness hypothesis. The specified function takes a derived morphism `f` to
this derived unit followed by the derived scalar restriction of `f`.

The scalar extension `baseChange φ` is the published ordinary degreewise
extension on complexes. This statement does not define a functor of derived
scalar extension and does not assert that ordinary extension preserves arbitrary
quasi-isomorphisms. The bounded projective source is essential to the proposed
route: compute its derived Hom sets by homotopy classes, use the ordinary
extension/restriction adjunction there, and compare with the exact restriction
functor on derived categories. Proving that route is a later exact-target proof
obligation. This file contains only the two canonical unit definitions and the
Prop-valued target, not that proof.

The content is internally derived from Mathlib's module adjunction, complex
mapping and exact-functor localization APIs, together with the Library's existing
strictly perfect complex definition. It is not a transcription of a separately
cited literature assertion. This algebraic proposition supplies no cohomological
perfectness, geometric base-change isomorphism, restriction compatibility or
fibre-section lifting theorem. Those remain separate project obligations.
