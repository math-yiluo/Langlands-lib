# Finite full orders preserved by an algebra involution

Worker 57. This derived algebraic prerequisite constructs a finite full
integer order in a finite-dimensional rational algebra, stable under a
specified rational involution. It also constructs the restricted order
involution and a faithful action on an actual finite full integer lattice.
No order or lattice with these properties is an input.

## Source and provenance

Kottwitz, *Points on Some Shimura Varieties over Finite Fields* (1992),
section 5, printed p.389 (PDF p.17), requires an order preserved by the
positive left involution and a preserved lattice. The source is registered
as `kottwitz-1992-points-shimura-finite-fields`, original SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
No source-specific errata note was found in the consulted project notes.

The construction here is a derived prerequisite, not a transcription of
the source's full local input. Its stabilizer and denominator arguments
are implemented in Lean using Mathlib's localization, span and Noetherian
module results. Kottwitz requires a prime-local order maximal after
completion and a self-dual local lattice. This file constructs an integer
order and a preserved rationally full integer lattice. It establishes
neither prime-local maximality nor self-duality, and makes no claim about
integrality of an alternating form. `HarrisIntegralOrder` gives the actual
positive Harris specialization of this generic construction.

## Denominator lemmas

For an additive commutative group `V` with `Module ℚ V`, an integer
submodule `L` and `x ∈ span_ℚ L`, `exists_int_multiple_mem` proves that
some nonzero integer multiple of `x` belongs to `L`. Span induction treats
members and zero directly; addition multiplies the two denominators;
the rational scalar step clears the coefficient using
`IsLocalization.exists_integer_multiple`.

If `span_ℚ L = ⊤`, `exists_common_int_multiple` clears denominators
simultaneously for a family indexed by any finite set. Its proof uses
finite-set induction and multiplies the new denominator into the old one.
These lemmas require no finite-dimensionality of `V`.

## Lattice stabilizers and involution-stable cores

For any unital ring `A` and integer submodule `L`, `latticeStabilizer L`
is the integer subalgebra

```text
O(L) = {a ∈ A | for every x ∈ L, a*x ∈ L}.
```

The ring and integer-scalar closure laws follow from multiplication and
submodule closure. `latticeStabilizerAction` is the ring homomorphism from
`O(L)` to `Module.End ℤ L` given by left multiplication. Its application
formula is proved, as are all ring-homomorphism laws. When `1 ∈ L`,
evaluation at `1` proves `latticeStabilizerAction_injective` and constructs
the integer-linear inclusion `latticeStabilizerEmbedding : O(L) →ₗ[ℤ] L`.
If in addition `L.FG`, this inclusion proves
`latticeStabilizer_finite` by Noetherianity over the integers.

For a rational algebra `A`, if `L` is finite and rationally full,
`exists_int_multiple_mem_latticeStabilizer` proves that each `a : A` has
a nonzero integer multiple in `O(L)`. The proof clears the finitely many
products of `a` with chosen generators of `L`, then extends preservation
by integer-span induction. `span_eq_top_of_int_multiples` turns such a
denominator property into full rational span, by inverting the nonzero
integer in the rationals.

For `σ : AlgebraInvolution ℚ A` and an integer subalgebra `O`,
`involutionStableCore σ O` is the integer subalgebra of `a ∈ O` satisfying
`σ(a) ∈ O`. Multiplication reversal under `σ` proves multiplication
closure. `involutionStableCore_le` embeds the core in `O`; involutivity
proves that `σ(a)` belongs to the core exactly when `a` does.
`involutionStableCore_finite` transfers finiteness along that inclusion.
If every algebra element has a nonzero integer multiple in `O`,
`exists_int_multiple_mem_involutionStableCore` proves the same for the
core by combining denominators for `a` and `σ(a)`.

## The constructed order, involution and action

Now assume `[Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A]`.
`basisLattice A` is the integer span of `1` and the vectors of
`Module.finBasis ℚ A`. The theorem `one_mem_basisLattice` and instance
`basisLattice_isLattice` prove that it contains `1`, is finitely generated
over the integers, and spans all of `A` over the rationals.

For any rational involution `σ`, the construction is

```text
integralOrder A σ = involutionStableCore σ (latticeStabilizer (basisLattice A)).
```

`integralOrder_finite` proves finiteness over the integers.
`exists_int_multiple_mem_integralOrder` proves the nonzero integer-multiple
property, and `integralOrder_isLattice` proves full rational span of the
order's underlying integer submodule. `involution_mem_integralOrder`
proves stability in both directions. These facts make the actual unital
integer subalgebra a finite full order.

`integralOrderInvolution` restricts `σ` to that subalgebra. Its integer
linearity, unitality, multiplication reversal and involutivity are proved.
`integralOrderInvolution_apply` identifies its underlying value with
`σ(a)`. `integralOrderAction` composes the inclusion in the stabilizer
with its action on `basisLattice A`. The application formula is left
multiplication, `integralOrderAction_injective` proves faithfulness by
evaluation at `1`, and `integralOrder_mul_mem_basisLattice` states
preservation directly in `A`.

The basis choice makes this construction noncanonical. No compatibility
between different basis choices, maximality, discriminant calculation or
extension of the rational involution to a positive integral form is
asserted. The algebra and module types are universe-polymorphic.
