# Spectral residue comparisons and the inertia degree criterion

This is a derived helper unit for
`Langlands.LocalGalois.Separable.SeparableUnramifiedStatement`. It constructs
explicit integer and residue equivalences and proves the group theoretic
criterion used by that target. It does not assert arithmetic unramifiedness or
prove the whole target. Worker 1199 implemented the helpers in coordination
with Worker 60's complementary finite arithmetic proof.

## Scope and provenance

In the namespace `Langlands.LocalGalois`, let `K` be a complete nontrivially
normed ultrametric field, let `L/K` be algebraic, and let
`E : IntermediateField K L` be finite dimensional over `K`. The norm on `E`
is `spectralNorm.nontriviallyNormedField K E`. All integer rings and residue
maps below are the published canonical spectral constructions from
`SpectralDefinitions` and `AbsoluteDefinitions`.

These definitions are internal comparisons of existing objects; they are not
translations of an additional external definition. Their proofs use Mathlib's
uniqueness of the extended field norm, finite-field Galois theory, the
published `residueHom_surjective`, and the Galois correspondence and subgroup
index theorems in Mathlib. The finite-set construction uses the published
normality of the actual inertia fixed field and Mathlib's normal closure.

## Definitions and compatibility

* `spectralBaseIntegers_eq` identifies `baseIntegers E`, for this spectral
  norm, with `extensionIntegers K E`. `spectralBaseIntegersEquiv` is the induced
  ring equivalence and `spectralBaseResidueEquiv` its residue-field equivalence.
* `spectralValuation_tower_eq` identifies `spectralValuation E L` with
  `spectralValuation K L`. The proof applies
  `spectralNorm_unique_field_norm_ext` to the absolute value of
  `spectralMulAlgNorm K L`; `spectralNorm.eq_of_tower` verifies extension from
  `E`. `spectralTowerIntegersEquiv` is the ring equivalence induced by that
  equality, and `spectralTowerIntegersEquiv_coe` states that it preserves the
  underlying element of `L`.
* `spectralTowerResidueEquiv` is the induced residue-field equivalence
  `ResidueField (extensionIntegers E L) ≃+*
  ResidueField (extensionIntegers K L)`.
  `spectralTowerResidueEquiv_base` identifies its action on base residues with
  `residueInclusion K L E` after `spectralBaseResidueEquiv`.
  `spectralTowerResidueEquiv_aut` intertwines the residue actions of an
  `E`-automorphism and its restriction of scalars to `K`.

## Stabilizer and degree theorems

`isGalois_of_finite_base` proves that an algebraic extension of a finite field
is Galois. For each element, its finite simple extension has a splitting
minimal polynomial; mapping this splitting into the ambient extension gives
normality. Finite-field perfectness gives separability.

Assume further that `L/K` is Galois and
`ResidueField (extensionIntegers K E)` is finite.
`map_residueHom_fixingSubgroup` proves that the image of `E.fixingSubgroup`
under `residueHom K L` is the fixing subgroup of
`(residueInclusion K L E).fieldRange`. One inclusion follows by evaluating
residues of integers. For the other, conjugate the residue automorphism by
`spectralTowerResidueEquiv`, use its base compatibility to make it an
`E`-residue automorphism, and apply `residueHom_surjective E L`. The explicit
base residue equivalence supplies the required finite base residue field.
No normality of `E/K` is assumed.

If `ResidueField (baseIntegers K)` is finite as well,
`fixingSubgroup_sup_inertia_index` proves

```text
(E.fixingSubgroup ⊔ inertia K L).index
  = [ResidueField (extensionIntegers K E) : ResidueField (baseIntegers K)].
```

The residue extension is Galois by the finite-base lemma. The stabilizer
identity, surjectivity of `residueHom K L`, and
`IntermediateField.finrank_eq_fixingSubgroup_index` compute the index.
The final linear equivalence is `AlgHom.equivFieldRange` for the canonical
residue inclusion.

`inertia_le_fixingSubgroup_iff_residue_finrank` then proves

```text
inertia K L ≤ E.fixingSubgroup
  ↔ [ResidueField (extensionIntegers K E) : ResidueField (baseIntegers K)]
      = [E : K].
```

The proof compares the indices of `E.fixingSubgroup` and its join with
inertia using `Subgroup.relIndex_mul_index`. Equality of the two finite
indices forces the relative index to be one; conversely, containment makes
the join equal to the fixing subgroup. Positivity of `[E : K]` justifies
cancellation.

## Actual separable-closure exhaustion

In `Langlands.LocalGalois.Separable`, for an arbitrary nonarchimedean local
field `F`, `finiteGaloisExhaustion_in_inertiaFixedField` puts every finite set
of the actual `inertiaFixedField F` inside a finite Galois intermediate field
of `SeparableClosure F`. It adjoins the image of the finite set under the
actual `fixedFieldToSepClosure F`, then takes its normal closure. The inertia
fixed field is Galois, so the normal closure remains inside it. This also
handles the empty set.

`finiteUnramifiedGaloisExhaustion_of_maximality` adds the target's independent
`ArithmeticUnramified` predicate assuming `FiniteUnramifiedMaximality F`.
The present unit supplies neither that maximality assumption nor the finite
integer-ring arithmetic needed to prove it. No characteristic zero,
perfectness of `F`, or completeness of the infinite fixed field is assumed.
