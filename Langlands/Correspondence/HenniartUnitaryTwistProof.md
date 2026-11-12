# Supercuspidal classes as unramified twists of unitary classes

Author: Worker 4803. Module `Langlands.Correspondence.HenniartUnitaryTwistProof`,
namespace `Langlands.Henniart.Extension`. The field universe `uK` and the
supercuspidal carrier universe `uV` are independent.

This module proves `SupercuspidalUnitaryFiniteOrderTwistStatement.{uK, uV}` (stated
in `HenniartExtensionInputs`) with the standard axioms only. It has no new
statement. The theorem is used by `SupercuspidalCorrespondenceHenniartReducedStatement`
(module `HenniartCorrespondenceReduction`).

## Proofs

### `isOfFinOrder_of_isOpen_ker_of_uniformizer`

A homomorphism `ω : K^× → ℂ^×` with open kernel and `ω(ϖ) = 1`, for the chosen
uniformizer `ϖ = T.uniformizerUnit` of the canonical data `T`, has finite order.
The kernel `C` of the order map is the set of units of absolute value one. It is
compact by the published `isCompact_normalizedAbs_eq_one_units`, through
`ord_eq_zero_iff_normalizedAbs`. The subgroup `ker ω ∩ C` is open in `C`, so it has
finite index `m` (Mathlib's `Subgroup.quotient_finite_of_isOpen`). Every unit is
`a = (a ϖ^(-ord a)) ϖ^(ord a)` with the first factor in `C`. Hence
`ω(a)^m = ω((a ϖ^(-ord a))^m) = 1`, so `ω^m = 1`. This follows the published proof
of `norm_eq_one_of_normalizedAbs_eq_one`.

### `supercuspidalClassTwist_congr`

Twisting a supercuspidal class by equal characters gives equal classes, whatever
the openness and determinant certificates.

### `exists_unitaryFiniteOrderTwist`, `supercuspidalUnitaryFiniteOrderTwist`

Let `π = (n, [A])`.

1. The published `supercuspidalRepRealUnitarization` gives a real `t` such that
   `B = A ⊗ |det|^t` is unitarizable. The published
   `realPowerDeterminant_eq_unramifiedCharacter` identifies `|det|^t` with the
   determinant unramified character with value `z₁ = |ϖ|^t` at the uniformizer. So
   `(n, [B])` is the unitary class `π₁`, and
   `π₁ = unramifiedTwistBasisEquiv K z₁ π`.
2. The published `admissibleSchur_centralCharacter` gives a locally constant
   character `χc` of the centre by which the centre acts on `B`. Its composite
   `ω₁` with the scalar embedding (continuous by `GeneralLinear.scalarContinuous`)
   has open kernel. `ω₁` has modulus one everywhere: the invariant positive form of
   `B` and `norm_eq_one_of_invariantPositiveForm` (module
   `HenniartTwistBridge`) applied to a nonzero vector.
3. Write `u = ω₁(ϖ)`. Choose `w` with `w^n = u⁻¹` (Mathlib's
   `IsAlgClosed.exists_pow_nat_eq`). Then `‖w‖ = 1`. Lemma
   `unitaryCharacterTwist_fieldUnramified` (module `HenniartTwistBridge`) gives a unitary class `π₀` with
   `π₀ = unramifiedTwistBasisEquiv K w π₁`.
4. The central character of `π₀` is `ω₀ = (unramified character of w)^n · ω₁`
   (`supercuspidalCentralActsBy_iff` and `supercuspidalCentralActsBy_twist` of
   module `HenniartExtensionDeterminant`). Its kernel contains the intersection of
   two open kernels, and `ω₀(ϖ) = w^n u = 1`. By the first lemma `ω₀` has finite
   order, so `HasFiniteOrderCentralCharacter K π₀`.
5. With `z = (w z₁)⁻¹`, `unramifiedTwistBasisEquiv K z π₀ = π` by the published
   `unramifiedTwistBasisEquiv_mul` and `unramifiedTwistBasisEquiv_symm`.

`supercuspidalUnitaryFiniteOrderTwist` quantifies this over every prime and every
p-adic field.

## Literature

The theorem proved is the derived statement documented in
`HenniartExtensionInputs.md`: Henniart (1993), §4.3, second paragraph, printed
p. 349 (`henniart-1993-epsilon-pairs`), with the unitarity of supercuspidal
representations with unitary central character. The proof here does not follow
Renard's VI.2.1. It uses the published real unitarization of supercuspidal `GL_n`
representations instead.
