# Normalized absolute value of the actual idele norm

For number fields `K` and `L`, in arbitrary possibly different universes, and a
specified `Algebra K L`, the definition
`AdelicFunctoriality.normAbsoluteValueCharacter K L` is the continuous positive
character on the original full idele group of `L` obtained by composing the
actual idele norm `ideleNorm` with `IdeleAbsoluteValue.full K`.
The theorem `full_ideleNorm` proves the exact normalized identity

```text
IdeleAbsoluteValue.full K (ideleNorm x) = IdeleAbsoluteValue.full L x.
```

Both finite and infinite components are retained. The absolute values are the
published product-formula normalizations: multiplicity one at real places and
two at complex places, together with the original finite-place norms.

This is an internal derivation from published results. In particular, it uses
`NormOneIdeleClass.exists_isCompact_fundamentalSet`, whose proof uses finiteness
of the ideal class group and Dirichlet's unit theorem. That result concerns
the multiplicative group alone and is independent of the general algebraic
group compactness theorem sought by the parent task.

The proof proceeds as follows.

1. `IdeleAbsoluteValue.apply_eq_one_of_full_eq_one` treats any continuous
   character `χ : Ideles F →ₜ* ℝ≥0ˣ` trivial on all principal ideles. Its real
   values are bounded above on the published compact fundamental set `C`.
   For a norm-one idele `y`, each positive integer power can be multiplied by
   a principal idele into `C`, leaving its character value unchanged. If
   `χ(y) > 1`, unboundedness of its positive powers contradicts this bound.
   Hence `χ(y) ≤ 1`; applying the same argument to the inverse proves equality.

2. `IdeleAbsoluteValue.eq_of_positiveRealIdeles` shows that such a character
   is determined by its values on `PositiveRealIdeles.full F`. Put
   `n = [F : ℚ]` and `s = PositiveRealIdeles.full F (full F x)`. The published
   positive scalar formula gives `full F s = (full F x)^n`, so
   `x^n * s⁻¹` has norm one. Step 1 and the assumed scalar identity imply
   `χ(x)^n = (full F x)^n`. The degree `n` is positive; injectivity of that
   power on nonnegative reals gives the result.

3. `infiniteRealEmbedding_ratCast` identifies rational real scalars at infinity
   with their actual principal coefficients.
   `infiniteAdeleNorm_infiniteRealEmbedding` compares two continuous functions
   of a real variable. On the dense rational subfield they agree by the
   published principal-adele norm formula and the algebraic identity
   `Algebra.norm K (algebraMap K L q) = q^[L:K]`. Rational density proves the
   equality for every real scalar.

4. `ideleNorm_positiveRealIdeles` combines step 3 with the finite part, where
   the scalar idele is one. Thus its actual idele norm is the positive scalar
   idele raised to `[L:K]`.

5. Apply step 2 over `L` to `normAbsoluteValueCharacter K L`. It kills
   principal ideles by the original principal-idele norm formula and the
   product formula over `K`. Step 4 and the tower identity
   `[L:ℚ] = [L:K][K:ℚ]` give the required scalar equality.

The module assumes no Galois or splitting condition. It does not classify
algebraic characters of Weil restrictions or assert a general norm-one
comparison or quotient compactness.
