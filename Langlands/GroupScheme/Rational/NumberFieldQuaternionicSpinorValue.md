# Line similitudes with a prescribed reduced norm class

`Langlands.GroupScheme.numberFieldQuaternionicSpinorValue` proves
`Langlands.GroupScheme.NumberFieldQuaternionicSpinorValueStatement` in every universe. The
statement is stated in `Rational/NumberFieldQuaternionicSpinKernelReduction`.

Let `F` be a number field and `D` a central quaternion division algebra with an orthogonal
involution `σ`. Let `q` be a nondegenerate `σ`-quadratic form on `D^n` with `n ≥ 3`, with polar
hermitian pairing `h = σ.sesqForm (σ.polar q)`. Let `a ∈ F^*` be a square at every real place
where `F_v ⊗ D` is a division ring or `h` is anisotropic. The statement asks for a row `x` with
`c = h(x, x) ≠ 0`, a quaternion `d` with `d c σ(d) = Nrd(d) c`, and `s ∈ F^*` with
`Nrd(d) = a s²`.

## Proof

Let `τ` be the canonical conjugation and `ℓ` the alternating unit, so that `σ(z) = ℓ⁻¹ τ(z) ℓ`.
Let `H = conjugationSkewGram q`, which is antihermitian for `τ` and invertible, with
`τ.sesqForm H x y = h(x, y) ℓ⁻¹` (`sesqForm_conjugationSkewGram`). The same holds in
coordinates over any field extension (`sum_conjugationSkewGram_baseChange`, via
`baseChange_quaternionConjugation`). So a local isotropic row for `h` is one for `H`.

1. At a real place where `a` is nonsquare, the square hypothesis forces `F_v ⊗ D` to have a
   nonzero nonunit and `h` to have a nonzero isotropic row.
2. `exists_elliptic_mul_conjugation` gives `d` and `s ≠ 0` with `d τ(d) = a s²`, so
   `Nrd(d) = a s²`. It also gives `w = d - τ(d)` with `w² = δ ∈ F` and `δ < 0` at every real
   place where `a` is a square.
3. If `w = 0`, then `d` is a scalar and commutes with every value. A row with nonzero value
   exists by `exists_polar_sesqForm_ne_zero`: apply step 2 to `1` to obtain a pure quaternion
   that is elliptic at every real place, or use `ℓ` when `F` has no real place, and then
   `exists_value_on_pureLine_of_real`.
4. If `w ≠ 0`, it is pure. At a real place where `δ` is a square, `a` is nonsquare, by the
   sign of `δ` in step 2. Step 1 then gives the local isotropic row needed by
   `exists_value_on_pureLine_of_real`, which yields `x` and `b ≠ 0` with
   `τ.sesqForm H x x = b w`.
5. `d` commutes with `w`, because `τ(d) = Trd(d) - d`. Hence `d` commutes with
   `W = τ.sesqForm H x x`. The value `h(x, x) = W ℓ` is nonzero, and
   `d (W ℓ) σ(d) = d W ℓ ℓ⁻¹ τ(d) ℓ = W d τ(d) ℓ = Nrd(d) · W ℓ`.

The nonzero scalar `s` from step 2 defines the unit in the conclusion.

This is the global existence of spinor norms on rank-one tori used for skew-hermitian forms
over quaternion division algebras. Compare M. Kneser, *Lectures on Galois Cohomology of
Classical Groups* (1969), §5.11, sequence (4), printed p. 101 (PDF p. 107), and the
representation results of T. A. Springer's appendix, Proposition 5.3.2, printed p. 109
(PDF p. 115).
