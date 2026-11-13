# Units `c` with every `c^m - 1` a unit

Module `Langlands.Geometry.Building.RegularUnitExistence`. This is an internal helper for
the uniqueness argument of `SplitIntegralFrameUniqueness`. That argument needs a torus
element `ν(c)` on whose root groups conjugation minus the identity is invertible, that is,
a unit `c` such that every `c^m - 1` is a unit.

## Declarations

Namespace `Langlands.Geometry.Building`, for a field `k` and a valuation
`v : Valuation k Γ` with values in a linearly ordered commutative group with zero:

* `valuation_eq_one_of_residue_ne_zero`: an element `a` of `v.valuationSubring` whose
  residue is nonzero satisfies `v a = 1`.
* `exists_unit_valuation_pow_sub_one_eq_one`: suppose the residue field of
  `v.valuationSubring` is infinite. For every finite set `N` of positive natural numbers
  there is `c : kˣ` with `v c = 1` and `v (c ^ m - 1) = 1` for all `m ∈ N`.
* `exists_unit_sq_ne_one`: under the same hypothesis, some unit `d` has `d ^ 2 ≠ 1`.

Namespace `Langlands.Geometry.Building.MaximalUnramified`, for a nonarchimedean local
field `F`:

* `infinite_residueField`: the residue field of `(valuation F).valuationSubring` is
  infinite. Here `valuation F` is the integer-valued valuation on the inertia fixed field.
* `exists_unit_valuation_pow_sub_one_eq_one` and `exists_unit_sq_ne_one`: the two
  statements above for `valuation F`.

## Implemented proof

*Valuation one.* A nonzero residue means `a` is outside the maximal ideal, hence a unit of
the valuation subring (`IsLocalRing.notMem_maximalIdeal`). Mathlib's
`ValuationSubring.valuation_eq_one_iff` turns this into valuation one for the valuation
of the subring. The equivalence `Valuation.isEquiv_valuation_valuationSubring` transfers
it to `v`.

*Regular units.* In the residue field `κ`, the finite set `bad` consists of `0` and the
roots of the nonzero polynomials `X ^ m - C 1` for `m ∈ N` (`X_pow_sub_C_ne_zero`). Since
`κ` is infinite, some `c₀` lies outside `bad` (`Infinite.exists_notMem_finset`). Then
`c₀ ≠ 0` and `c₀ ^ m - 1 ≠ 0` for all `m ∈ N`. Lift `c₀` to `a` in the valuation
subring. The residues of `a` and of `a ^ m - 1` are `c₀` and `c₀ ^ m - 1`, both nonzero, so
`a` and every `a ^ m - 1` have valuation one. In particular `a ≠ 0`, and
`c = Units.mk0 a _` works. For `exists_unit_sq_ne_one` take `N = {2}`: if `c ^ 2 = 1`,
then `c ^ 2 - 1 = 0` would have valuation zero, not one.

*Maximal unramified extension.* The published `fixedFieldResidueIsAlgClosure` makes the
residue field of `fixedFieldIntegers F` an algebraic closure of the residue field of `F`
(via the algebra `residueToFixedField F`). It is therefore algebraically closed, hence
infinite (Mathlib instance). The published `valuationSubring_eq` identifies
`(valuation F).valuationSubring` with `fixedFieldIntegers F`.

## Provenance and scope

Internal elementary lemmas, with no source assertion. They say nothing about groups or
buildings.
