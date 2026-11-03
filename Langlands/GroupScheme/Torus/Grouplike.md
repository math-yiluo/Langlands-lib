# Grouplike elements of group algebras

This module works with the published algebra-level character machinery of `Torus.CharacterActionGrading`. That module provides the group algebra `algebra B = B[M]` of an `R`-algebra `B` and an additive commutative group `M`, together with `constant`, `universal`, `evaluate`, `coefficientMap` and `diagonalMap`. Here it is used to study grouplike elements, which describe endomorphisms of the diagonalizable group `D(M)` over `B`.

## Helper identities

- `evaluate_comp`: evaluation is natural in the target, `evaluate x t ≫ f = evaluate (x ≫ f) (mapCharacter f t)`.
- `mapCharacter_mul`, `mapCharacter_mapCharacter`: functoriality of changing the coefficients of a character.
- `hom_ext_single`: algebra maps out of `B[M]` agreeing on all monomials `single m b` are equal.
- `evaluate_apply`: `evaluate x t q = ∑ₙ x(qₙ) t(n)`.
- `evaluate_constant_universal`: evaluating with constant coefficients at the universal character is the identity of `B[M]`.

## Grouplike elements

`IsGrouplike u` for `u ∈ B[M]` says `Δ u = u ⊗ u` and `ε u = 1`. Here `Δ` is `diagonalMap` (`Xᵐ ↦ XᵐYᵐ` into the iterated group algebra `B[M][M]`), the two copies of `u` are `constant (algebra B) u` and `coefficientMap (constant B) u`, and `ε` is evaluation at the trivial character.

For grouplike `u`:

- `evaluate_mul` and `evaluate_one`: for every algebra map `x : B ⟶ D` and characters `t, t'`, `evaluate x (t * t') u = evaluate x t u * evaluate x t' u` and `evaluate x 1 u = 1`. The proof evaluates the defining identity in `B[M][M]` at the pair of characters `(t, t')`.
- `coeff_mul_coeff`, `isIdempotentElem_coeff`, `coeff_mul_coeff_of_ne` and `sum_coeff`: the coefficients `uₙ` are orthogonal idempotents with sum `1`. These follow by comparing coefficients of `XᵖY^q` in the defining identity.
- `mul`, `one` and `map`: grouplike elements are closed under products, and `1` is grouplike. Coefficientwise images under algebra maps are grouplike.
- `mul_inverse` and `isUnit`: `u` is a unit, with inverse obtained by substituting `Xᵐ ↦ X⁻ᵐ`.

## Construction and lifting

- `isGrouplike_sum_single`: if `(eᵢ)` is a finite complete family of orthogonal idempotents (Mathlib's `CompleteOrthogonalIdempotents`) and `a : ι → M` is arbitrary, then `∑ᵢ eᵢ X^{a i}` is grouplike.
- `exists_isGrouplike_lift`: let `π : C ⟶ D` be surjective with nilpotent kernel elements. Then every grouplike element of `D[M]` is the coefficientwise image of a grouplike element of `C[M]`. The coefficients over `D` form a complete family of orthogonal idempotents indexed by the support. Mathlib's `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker` lifts this family.
- `isGrouplike_lift_unique`: two grouplike elements of `C[M]` with the same image are equal. Their coefficients are idempotents differing by nilpotents, so they agree by Mathlib's `eq_of_isNilpotent_sub_of_isIdempotentElem`.

## Provenance

This is an internal construction toward task `0f453442`. Grouplike elements of group algebras over arbitrary rings, and their description by orthogonal idempotents, are standard: they are the characters `D(M) → 𝔾_m` over `Spec B`, locally constant on `Spec B`. The module formalizes the parts needed for rigidity of diagonalizable groups under square-zero deformations: lifting and uniqueness of grouplikes along nilpotent ideals. No literature result is formalized verbatim.
