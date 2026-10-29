# An integer alternating pairing for the actual Harris regular module

## Provenance and inputs

This is the actual Harris specialization of the derived integral-lattice
construction in `IntegralPairing`. It continues `HarrisHodgeInput` and
`HarrisIntegralOrder`; all their arithmetic, signature and Hodge choices are
reused. Its original source context is Kottwitz, *Points on some Shimura
varieties over finite fields* (1992), section 5, printed page 389 (PDF page 17),
registered as `kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
That passage requires an involution-compatible nondegenerate rational
alternating form and a preserved self-dual lattice over the chosen p-adic
field. This module supplies a global finite full integer lattice with an
integer-valued nondegenerate alternating form and a faithful compatible
order action. Perfectness, p-adic self-duality and prime-local maximality
remain further obligations.

The inputs are the same as in `HarrisIntegralOrder`:

- `E` is a totally real number field, and `K/E` is a totally imaginary
  quadratic number-field extension.
- `A` is a ring with compatible `E`-, `K`- and rational-algebra structures
  and the stated scalar towers.
- `D : CentralSimpleUnitaryData E K A n` supplies the actual central simple
  algebra and second-kind involution, with the degree and arithmetic
  hypotheses of that published definition.
- `C : HarrisSignatureCharts D.toSecondKindInvolution n Φ` supplies the
  published Harris signature charts for the original involution and the
  indicated complex embeddings.

There is no supplied lattice, integer pairing, order action or adjoint proof.
The imported construction already derives finite rational dimension from `D`,
constructs `D.harrisHodgePELLattice` and the positive-involution-stable order
`D.harrisHodgePELIntegralOrder C`. The rational form
`D.harrisHodgePELForm C` is the same normalized trace form built from the one
fixed Hodge-positive skew unit in `HarrisHodgeInput`. The new lattice scaling
neither changes that form nor makes a new choice of Hodge-positive unit.

## The lattice and integer restriction

`harrisHodgePELIntegralLattice` specializes `integralPairingLattice` to this
rational form and the previously constructed lattice. In formulas, if `m` is
the chosen nonzero common integer denominator of the old Gram values, the new
lattice is `m D.harrisHodgePELLattice` inside the actual rational regular
module `A`. `harrisHodgePELIntegralLattice_isLattice` proves finite integer
generation and full rational span. Its underlying module is therefore finite
over the integers through the existing `Submodule.IsLattice.finite` instance.

`harrisHodgePELIntegralLattice_isInteger` proves integrality of the unchanged
rational form on the new lattice. `harrisHodgePELIntegralPairing` uses this
proof and `integerPairing` to construct an integer bilinear form on the
lattice subtype. `harrisHodgePELIntegralPairing_cast` states exactly that its
integer value, cast to the rationals, is the original rational form evaluated
on the included vectors.

`harrisHodgePELIntegralPairing_isAlt` inherits alternation from the published
rational form. `harrisHodgePELIntegralPairing_nondegenerate` combines its
published rational nondegeneracy with full rational span of the new lattice.
The generic proof extends vanishing linear functionals from the lattice to
all of `A` and then uses rational nondegeneracy in each variable.

## The unchanged order and its adjoint action

The order and its restricted involution remain the ones constructed in
`HarrisIntegralOrder`, using the positive auxiliary **left** involution of
`D.harrisHodgePELAlgebra C`. They are not replaced by a new stabilizer order
or by the original right-adjoint involution.

The private helper `harrisIntegralOrder_le_stabilizer` records preservation of
the old lattice. The generic preservation theorem then proves
`harrisHodgePELIntegralOrder_mul_mem_integralLattice`: the same order
preserves the new lattice. `harrisHodgePELIntegralPairingAction` is its
ring-homomorphism action by integer-linear endomorphisms of the new lattice.
`harrisHodgePELIntegralPairingAction_apply` identifies it with actual left
multiplication. `harrisHodgePELIntegralPairingAction_injective` proves
faithfulness using the generic full-span argument and injectivity of the
order's inclusion in its original lattice stabilizer.

Write `ψℤ` for the constructed integer form, `ρ` for this action and `τ`
for `D.harrisHodgePELIntegralInvolution C`. Then
`harrisHodgePELIntegralPairingAction_adjoint` proves the equality of integers

`ψℤ (ρ(a)x, y) = ψℤ (x, ρ(τ(a))y)`.

Its proof casts both sides to the rationals, uses the cast and action
formulas to recover the published rational left-adjoint identity for the
same auxiliary involution, and concludes by injectivity of integer cast.
All action, preservation and adjoint laws are proved for the constructed
objects.

This is one integral algebraic prerequisite. It asserts neither a perfect
integer pairing nor a self-dual local lattice, and does not construct a PEL
moduli scheme, its level tower or the coefficient descent.
