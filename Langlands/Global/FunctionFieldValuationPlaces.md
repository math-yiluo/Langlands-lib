# All valuation-subring places of function fields with finite constants

This module constructs an equivalence between the published concrete curve
places and all nontrivial valuation subrings of a function field over a finite
field. The latter side has no principal-ideal or discreteness hypothesis.
It supplies a place-index comparison for the function-field adelic construction.

The provenance is derived arithmetic infrastructure. The mathematical inputs
are the existing `AlgebraicCurve.Place` construction, the published
Krull--Akizuki theorem, and Mathlib's finite-extension and valuation results,
imported by Lean name below. This auxiliary equivalence is not presented as a
separate assertion from Conrad's paper.

## Objects and hypotheses

The fields `k` and `F` have the same arbitrary universe and an algebra structure
`k → F`. For the function-field constructions there is also a specified
`RatFunc k`-algebra structure, compatible with `k → F`, and
`FunctionField k F`. Mathlib's last class asserts finite dimensionality over
that specified rational-function field.

`ValuationRingPlace F` is the subtype
`{O : ValuationSubring F // O ≠ ⊤}`. Its elements are actual valuation
subrings of `F`, with no choice of a value group and no restriction on rank or
discreteness.

The existing `AlgebraicCurve.Place k F` consists of an actual valuation subring
`O`, proofs that it contains the image of `k` and is not the whole field, and
`IsPrincipalIdealRing O`. Its existing discrete valuation ring instance follows
from these conditions. Thus the comparison needs to prove the principal-ideal
condition for the previously unrestricted subrings.

## Automatic principal ideals

`functionField_valuationSubring_principal` takes any valuation subring `O`
containing the image of `k` and proves `IsPrincipalIdealRing O`.
This theorem allows `O = ⊤` and does not require `k` finite or perfect, or
the specified extension of `RatFunc k` separable.

The implemented argument is as follows.

1. Set `s` to the image of `RatFunc.X`. Mathlib's
   `FunctionField.FiniteDimensional.adjoin_algebraMap_X` makes `F` finite
   dimensional over `k⟮s⟯`.
2. A valuation subring contains `s` or `s⁻¹`. In the second case
   `k⟮s⁻¹⟯ = k⟮s⟯`, so the same finite-dimensional statement applies to the
   inverse parameter.
3. For whichever parameter belongs to `O`, put
   `R = Algebra.adjoin k {s}`. The published scoped instance
   `CurveModel.isPrincipalIdealRing_adjoin_singleton` makes `R` principal,
   by surjective evaluation from `k[X]`. Mathlib's
   `IntermediateField.algebraAdjoinAdjoin` instances identify `k⟮s⟯` as its
   fraction field.
4. The published `CurveModel.adjoin_le_valuationSubring` puts `R` in `O`.
   Regard the same underlying subring `O` as an `R`-subalgebra `B` of `F`.
   Apply
   `Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite`
   to `B` and take its Noetherian conclusion. This is the published
   Krull--Akizuki input; it applies to the finite field extension without a
   separability assumption.
5. The underlying ring of `B` is the underlying ring of `O`. A valuation
   ring is Bézout, so Mathlib's Noetherian Bézout instance makes `O` a
   principal ideal ring.

The first four steps are packaged by the private
`principal_valuationSubring_of_mem_parameter` helper and then applied to the
two parameter cases. `functionFieldPlaceOfValuationSubring` adds `O ≠ ⊤`
and packages the result as an existing `Place k F`. Its underlying valuation
subring is definitionally `O`, as recorded by the paired simp theorem.

## Finite constants and the equivalence

For `[Finite k]`, `finiteConstants_mem_valuationSubring` proves that every
valuation subring of `F` contains the image of `k`. It applies
`FiniteField.valuation_algebraMap_le_one` to `O.valuation` and converts the
result back to membership in `O`.

`curvePlaceValuationRingEquiv k F` maps a curve place to its actual underlying
valuation subring. Its inverse uses
`functionFieldPlaceOfValuationSubring`, the just-proved finite-constant
membership, and the subtype's nontriviality proof. The inverse laws follow
from `Place.ext` and subtype extensionality, since neither map changes the
underlying subring. The two final simp lemmas expose this fact in both
directions.

## Scope

The equivalence covers every nontrivial valuation subring, rather than an
index set defined by an assumed discrete valuation. The result is an
equivalence of place indices. This module does not construct a quotient of
real absolute values, compare the corresponding completions or adelic
topologies, or prove local compactness or geometric point-space comparisons.
Those are separate obligations in the adelic-points development.
