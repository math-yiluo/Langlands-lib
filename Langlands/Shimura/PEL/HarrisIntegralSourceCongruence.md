# Principal congruence on the actual integral Harris source

This internal construction uses the actual adelic source span `Λf` of
`HarrisIntegralTateImages` and the open stabilizer from `HarrisIntegralSourceLevels`.
It is a source-side operation on the existing scalar-extension similitude group,
not a new definition of the Harris moduli problem or a change of action convention.

For `m : ℕ`, `harrisIntegralSourceMultiples` is the submodule `mΛf` of `Λf` and
`HarrisIntegralSourceMod` is the quotient `Λf / mΛf`. The stabilizer acts through
`harrisIntegralSourceOperator`, the restriction of its actual linear operator.
The restriction preserves `mΛf` by linearity. `harrisIntegralSourceReduction`
is the resulting monoid homomorphism into the endomorphisms of the quotient.

`harrisIntegralAdeleCongruence` is the image of its kernel under the inclusion
of the stabilizer. It lies in the stabilizer and is normal **in the stabilizer**.
For a stabilizing operator `g`, `mem_harrisIntegralAdeleCongruence` says that
membership is exactly `g(v) - v ∈ mΛf` for every `v ∈ Λf`. In this test the
multiples are viewed inside the ambient adelic module.

For `m ≠ 0`, `harrisIntegralAdeleCongruence_isOpen` proves openness in the
actual adelic similitude topology, and `harrisIntegralAdeleOpenCongruence`
packages the resulting open subgroup. The proof takes a finite integral basis
of the Harris source lattice and uses its images in the adelic span as
module generators. The linear operator `g - id` sends the span into `mΛf` if
and only if it does so on those generators. Multiplication by `m` is a
homeomorphism of the ambient space because the image of the nonzero rational
integer `m` in the finite adeles is a unit. Thus `mΛf` is open by the published
openness of `Λf`. Pointwise evaluation of the operator is continuous, so the
finite set of conditions at the generators gives open conditions inside the
already open source stabilizer.

The construction makes no division assumption and does not compare the source
quotient to geometric torsion or construct a moduli representer.
