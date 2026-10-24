# Normalized rational profinite-integer and finite-adele comparison

Author: Worker 212.

The theorem `Langlands.Global.rationalProfiniteIntegerAdeleComparison` proves
the published proposition `RationalProfiniteIntegerAdeleComparison` with no
parameters or hypotheses. It constructs a ring equivalence from the compatible
residue ring `ProfiniteIntegerRing` to `integralFiniteAdeles ℚ`, continuous in
both directions and normalized on integer residue families, together with a
compatible rational algebra equivalence
`ℚ ⊗[ℤ] ProfiniteIntegerRing ≃ₐ[ℚ] FiniteAdeles ℚ`.

## Integral comparison

The published theorem `profiniteIntegerPadicProductComparison` supplies an
equivalence `ep` from the residue ring to the product of `PadicInt p.val` over
`p : Nat.Primes`, its continuity in both directions, and its coordinatewise
integer normalization. The proof composes `ep` with the published
`rationalPadicProductIntegralEquiv`, obtaining the integral equivalence `e₀`.

The latter map uses the explicit correspondence
`Rat.HeightOneSpectrum.primesEquiv` between the actual rational finite places
and natural primes, and the local equivalences
`Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv`, before identifying
the product of completed integer rings with the integral finite-adele subring.
These constructions and their continuity laws are in
`Langlands.Global.IntegralFiniteAdelePadicProduct`. Thus the resulting
equivalence has the actual height-one-prime-indexed integral finite adeles as
its target, with their subspace topology from the restricted product.

Both continuity clauses follow by composing the corresponding published
continuity proofs. For an integer `z`, function extensionality turns the
coordinatewise normalization of `ep` into equality with the family
`p ↦ (z : PadicInt p.val)`. The theorem
`rationalPadicProductIntegralEquiv_intCast` then identifies its image in
`FiniteAdeles ℚ` with `algebraMap ℚ (FiniteAdeles ℚ) (z : ℚ)`.

## Rational comparison

The published theorem `integralFiniteAdeleRationalization` supplies a rational
algebra equivalence `E` from `ℚ ⊗[ℤ] integralFiniteAdeles ℚ` to the actual finite
adeles, satisfying
`E (q ⊗ a) = algebraMap ℚ (FiniteAdeles ℚ) q * (a : FiniteAdeles ℚ)`.

The integral ring equivalence `e₀` canonically gives an integer algebra
equivalence via `RingEquiv.toIntAlgEquiv`. Applying
`Algebra.TensorProduct.congr` to the identity rational algebra equivalence on
the first factor and this integer algebra equivalence on the second gives
the rational algebra equivalence from `ℚ ⊗[ℤ] ProfiniteIntegerRing` to
`ℚ ⊗[ℤ] integralFiniteAdeles ℚ`. Composing with `E` gives the required `e`.
Tensor congruence sends `q ⊗ a` to `q ⊗ e₀(a)`, so the pure-tensor formula for
`E` immediately proves
`e (q ⊗ a) = algebraMap ℚ (FiniteAdeles ℚ) q * (e₀ a : FiniteAdeles ℚ)`.
This is the compatibility required between the two constructed equivalences.

## Provenance and scope

This is an internal derived proof by composition of the published Library
comparisons and Mathlib's tensor congruence. The arithmetic and topological
inputs are imported by their Lean names from
`ProfiniteIntegerPadicProductComparisonProof`, `IntegralFiniteAdelePadicProduct`
and `IntegralFiniteAdeleRationalizationProof`; none is an assumed hypothesis.
The target statement and its source and target rings remain unchanged.

The rational tensor product carries the rational algebra structure from its
first factor. The proof makes no assertion about a topology on that tensor
product, rational Tate modules, or the prime-to-p comparison. It asserts no
new external-literature theorem beyond the internal statement it proves.
