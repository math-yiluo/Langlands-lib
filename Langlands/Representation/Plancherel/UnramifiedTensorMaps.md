# Regular-linear tensor maps and actual operator families

This is derived supporting algebra for the conditional standard intertwining
theorem. It does not construct a continuation operator, a Jacquet filtration,
an annihilator or a denominator. In particular, it does not prove
`ConditionalParabolicIntertwiningStatement`.

Let `B = unramifiedRegularFunctions ν`, the existing algebra of actual
evaluation-generated functions on `unramifiedCharacters ν`. The group,
norm-character index, source carrier and target carrier have independent
universes. Both carriers are arbitrary complex vector spaces. No dimension,
admissibility, length or topology hypothesis on either carrier is imposed.

`unramifiedTensorMapLift` extends a complex-linear map from `V` to
`B ⊗[ℂ] W` to a `B`-linear map from `B ⊗[ℂ] V` to `B ⊗[ℂ] W`.
Its value on `b ⊗ v` is `b • f v`. The construction uses Mathlib's
heterobasic tensor lift and the regular scalar action on complex-linear maps.

For a `B`-linear map `T` between these tensor modules,
`unramifiedTensorMapSpecialization ν T χ` is the complex-linear operator
on the original carriers sending `v` to the evaluation of `T (1 ⊗ v)`
at the actual character `χ`. The evaluation theorem proves, for every
tensor `t`,

`evalχ (T t) = specializeχ(T) (evalχ t)`.

On pure tensors this follows from `B`-linearity, scalar evaluation and
complex linearity; tensor induction gives the general identity. Consequently
every such specialization is polynomial on every parameter subset, using
the previously established finite expansion of each tensor.

The specialization operation is injective when its values at all actual
characters are supplied. Equality of the specialized operators yields
equality of evaluation of each image tensor, and faithful simultaneous
evaluation yields equality of the maps. This does not assert uniqueness on
an arbitrary subset.

`isPolynomialOperatorOn_iff_exists_unramifiedTensorMap` identifies the
existing polynomial-operator predicate on any subset `Ω` with existence of
one `B`-linear map satisfying the displayed identity with the specified
operator family at each `χ ∈ Ω`. For the forward implication, choose a
basis of `V`, lift the polynomial vector family for each basis vector to
one tensor, extend these choices complex-linearly, and apply the tensor lift.
Equality of complex-linear maps is checked on that basis, then the general
evaluation identity supplies the assertion for every tensor. For the reverse
implication, evaluate the image of `1 ⊗ v` for each fixed `v`. The construction
needs no density assumption on `Ω`, and its conclusion asserts existence,
not uniqueness. Empty parameter subsets and zero carriers are included.

`isRationalOperatorOn_iff_exists_unramifiedTensorNumerator` applies the
polynomial equivalence to a denominator-cleared family. It retains exactly
one `b ∈ B`, nonzero at every point of `Ω`, and one `B`-linear numerator
map `T`, before quantification over a parameter or a source tensor. Thus its
identity is

`evalχ (T t) = b(χ) • Aχ (evalχ t)`.

This is an equivalent form of the existing rationality predicate. It does
not establish the required nonvanishing for an actual standard intertwiner
or produce the numerator of that operator.

The provenance is internal and derived: the only inputs are the concrete
regular algebra and family predicates in `UnramifiedOperatorFamilies`,
the tensor evaluation and polynomial-lift results in
`UnramifiedUniversalTwist`, and Mathlib's tensor and basis universal
properties. No additional representation-theoretic or analytic assertion
is used.
