# Degree-zero horizontal cohomology of the actual constant automorphic line

For a number field `F : Type u` and positive natural rank `n`, this module
constructs a complex linear equivalence

```text
horizontalScalarEquiv F n :
  ℂ ≃ₗ[ℂ] (ConstantFunctions.realization F n).HorizontalCohomology 0.
```

The codomain is the existing cohomology of the actual horizontal differential,
with its original cycles and boundary quotient. The coefficient realization
is the embedded line of actual constant automorphic functions constructed in
`ConstantFunctions`; its carrier is not replaced by an abstract scalar module.
There are no existence, differentiation or nonvanishing assumptions. The
number-field universe is arbitrary, and the scalars are `ℂ`.

## Simultaneous invariants

`compactRepresentation_eq_self` uses the inverse identities of the published
`scalarEquiv` and the actual compact-translation formula to show that every
element of the full standard infinite compact group fixes every vector.

`complexLieAction_eq_zero` rewrites the genuine complex Lie action through
the published enveloping generator. The enveloping action on constants is
multiplication by its augmentation, and augmentation kills every Lie
generator. Thus every complex Lie direction acts by zero.
`reducedLieAction_eq_zero` restricts the same result through the actual
reduced complex Lie inclusion.

These two identities prove `horizontalJointInvariants_eq_top`.
`horizontalInvariantScalarEquiv` maps a scalar to the actual constant vector
with both invariant conditions proved; its inverse is the original
`scalarEquiv.symm`. These constructions and identities do not require
positive rank.

## Original cycles, classes and scalar coordinates

For positive rank, `horizontalZeroCycle` composes the preceding invariant
equivalence with the inverse of the existing
`horizontalCyclesDegreeZeroEquiv`. It therefore constructs a closed cochain
for the actual differential. `horizontalZeroCycle_apply` identifies its
value at every empty tuple with `scalarEquiv c`.
`evaluate_horizontalZeroCycle` evaluates the corresponding adelic function
at every adelic group element to `c`.

`horizontalClass` applies the original `horizontalCohomologyClass 0`
projection to that zero cycle. `horizontalScalarEquiv` composes the invariant
equivalence with the inverse of the existing `horizontalDegreeZeroEquiv`.
`horizontalScalarEquiv_apply` identifies it with that original class
constructor. The existing degree-zero equivalence uses vanishing of the
actual boundary inclusion range inside cycles.

`horizontalScalarEquiv_symm_class` computes the inverse on the original
class of any closed zero cochain: evaluate its coefficient at the empty
tuple, then evaluate the represented function at the adelic identity. The
proof unfolds the existing equivalence and representative formula and applies
`scalarEquiv_symm_apply`.

`horizontalCohomology_finrank` transfers scalar dimension along the
equivalence and proves complex dimension one.
`horizontalClass_eq_zero_iff` uses injectivity to show that the constructed
class vanishes exactly when its scalar is zero.
`horizontalClass_one_ne_zero` applies this to one, giving an explicit
nonzero class in the original quotient.

## Provenance and scope

This is an internal construction from `ConstantFunctions` and the generic
and actual `HorizontalDegreeZero` constructions. Its proof uses their
implemented action, differentiation, kernel and quotient formulas and the
pinned Mathlib linear-equivalence dimension result. No additional
original-literature assertion enters.

The result computes degree zero for this particular actual coefficient
realization. It makes no assertion about cuspidal cohomology, higher degrees,
general cohomological occurrence, or comparison with geometric cohomology.
