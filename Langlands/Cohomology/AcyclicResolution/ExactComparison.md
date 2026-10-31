# Exact comparison through an arbitrary right resolution

This internal homological algebra construction computes two already published
exact-functor derived comparisons through an arbitrary right resolution. Object
and morphism universes of all abelian categories are independent, and the degree
`n` is any natural number.

An augmentation here is an actual cochain map `ε : A[0] → K`, with cochains
indexed by `ℕ`. A right resolution means that this augmentation is a
quasi-isomorphism. The complex `K` need not consist of injective objects or of
objects acyclic for any of the functors below.

## Mapping the augmentation

For an additive functor `T : C → D` preserving homology,
`quasiIso_mapResolutionAugmentation` proves that the actual mapped augmentation
from `AcyclicResolution.Composition`,

`T(A)[0] → T(K)`,

is a quasi-isomorphism whenever `ε` is one. Its first factor is the inverse of
Mathlib's comparison between applying `T` to a single complex and taking the
single complex of `T(A)`; its second factor is the mapped `ε`. Both factors
are quasi-isomorphisms. No preservation of injective objects is needed for
this assertion.

## Comparison on the cohomology of a complex

Let `Φ : C → E`, `P : E → E'`, `T : C → D`, and `Ψ : D → E'` be additive,
let `P` preserve homology, and specify a natural isomorphism
`e : Φ ⋙ P ≅ T ⋙ Ψ`. Define

`resolutionComplexComparisonIso Φ P T Ψ e K n :`
`P(Hⁿ(Φ(K))) ≅ Hⁿ(Ψ(T(K)))`.

Its first factor is the inverse of the published `mapHomologyIso` for `P`.
Its second factor is the cohomology of the published termwise
`DerivedComparison.complexIso` induced by `e`.
`resolutionComplexComparisonIso_hom_naturality` proves that this isomorphism
commutes with every cochain map `t : K → L`: applying `P` to `Hⁿ(Φ(t))`
and then the comparison at `L` equals the comparison at `K` and then
`Hⁿ(Ψ(T(t)))`. The proof uses the two published naturality identities and
functoriality of cohomology. These constructions do not need injective
resolutions in any category.

## Computing the exact source-functor comparison

Now suppose `C` and `D` have injective resolutions and `T` preserves homology
and injective objects. For any quasi-isomorphism `ε : A[0] → K`, the theorem
`resolutionComparison_rightDerivedCompIso` states

`P(resolutionComparison Φ ε n) ≫ rightDerivedCompIso(e,n).hom.app A`
`= resolutionComplexComparisonIso(e,K,n).hom`
`  ≫ resolutionComparison Ψ (mapResolutionAugmentation T ε) n`.

Both sides are actual morphisms
`P(Hⁿ(Φ(K))) → RⁿΨ(T(A))`. The mapped augmentation on the right is a
quasi-isomorphism by the first result. Neither `Φ` nor `Ψ` is assumed left
exact.

The implemented proof takes the chosen injective resolution `I` of `A` and
an augmentation-compatible lift `t : K → I`. The published independence
formula `resolutionComparison_eq` computes the source comparison using
`I`, and computes the target comparison using the mapped injective resolution
`mapInjectiveResolution T I`. Mapping the augmentation square verifies that
`T(t)` is the required compatible map. Expanding the published
`compIsoOfResolution` cancels the mapped inverse and forward cohomology
isomorphisms of `I`. The cochain naturality formula above then gives the
asserted equality.

## Computing exact postcomposition

There is a second theorem that needs injective resolutions only in `C`.
Let `Φ : C → E` and `H : C → E'` be additive, let `P : E → E'` be additive
and preserve finite limits and finite colimits, and specify
`e : Φ ⋙ P ≅ H`. For the same arbitrary right resolution,
`resolutionComparison_rightDerivedCompIsoOfResolution` states

`P(resolutionComparison Φ ε n)`
`  ≫ (DerivedPlus.rightDerivedCompIsoOfResolution Φ P e (injectiveResolution A) n).hom`
`= (mapHomologyIso P (Φ(K)) n).inv`
`  ≫ Hⁿ((Functor.mapHomologicalComplexCompIso e).hom.app K)`
`  ≫ resolutionComparison H ε n`.

Both sides go from `P(Hⁿ(Φ(K)))` to `RⁿH(A)`. Exactness of `P` supplies
its homology-preservation instance. No injective-preservation premise is
imposed on `P`, and no exactness premise is imposed on `Φ` or `H`.

The proof again lifts `K` to the chosen injective resolution and applies
`resolutionComparison_eq` twice. It expands the published explicit
postcomposition formula, cancels the mapped inverse and forward isomorphisms,
and uses naturality of the inverse homology comparison and of Mathlib's
termwise composite-functor comparison. The raw short-complex homology
comparison is definitionally the wrapped `DerivedComparison.mapHomologyIso`;
expressing it in that form permits the published naturality lemma to apply.

The inverse formula is also proved as
`resolutionComparison_inv_rightDerivedCompIsoOfResolution`:

`resolutionComparison H ε n`
`  ≫ (DerivedPlus.rightDerivedCompIsoOfResolution Φ P e (injectiveResolution A) n).inv`
`= Hⁿ((Functor.mapHomologicalComplexCompIso e).inv.app K)`
`  ≫ (mapHomologyIso P (Φ(K)) n).hom`
`  ≫ P(resolutionComparison Φ ε n)`.

It uses the same hypotheses. The proof postcomposes with the forward
isomorphism, applies the forward formula, and cancels the forward/inverse
homology and termwise comparison pairs.

## Provenance and scope

These are internal consequences of the published
`AcyclicResolution.Comparison`, `AcyclicResolution.Composition`,
`DerivedComparison`, and `DerivedExactComposition` constructions, and of
Mathlib's actual single-complex, homology, and termwise-composition
isomorphisms. No additional external mathematical assertion is used.

The results identify specified derived comparisons with specified resolution
maps. They do not prove that a general augmentation is a resolution, that a
resolution comparison for an arbitrary complex is invertible, or any
geometric base-change or relative cube statement.
