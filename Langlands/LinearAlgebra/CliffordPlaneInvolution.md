# Clifford lifts of the negation of a nondegenerate plane

Module `Langlands.LinearAlgebra.CliffordPlaneInvolution`, namespace
`Langlands.QuadraticForm.CliffordSpinLift`.

## The result

`unit_mul_unit_eq_neg_one_of_involution` concerns a field `F` with `2` invertible, a finite
dimensional `F`-vector space `V` and a quadratic form `Q` on `V` whose polar bilinear form is
nondegenerate. Let `s : CliffordSpinLift Q` be a spin lift (module
`LinearAlgebra/CliffordSpinLift`) whose vector action `ℓ = vectorAction Q s` satisfies:

* `ℓ (ℓ v) = v` for every `v` (an involution);
* `ℓ v ≠ v` for some `v` (not the identity);
* the range of `ℓ - id` has dimension at most `2`.

Then the Clifford unit `unit Q s` satisfies `unit Q s * unit Q s = -1` in the Clifford
algebra `CliffordAlgebra Q`.

Geometrically, `ℓ` is the negation of a nondegenerate plane `W` and the identity on `W^⊥`.
For an orthogonal basis `e₁, e₂` of `W`, a spin lift of `-1_W ⊕ 1_{W^⊥}` is a scalar
multiple of `e₁e₂`, whose square is `-Q(e₁)Q(e₂)`. The norm-one condition on the lift
sets the square of the scalar to `1 / (Q(e₁)Q(e₂))`.

## Proof

Write `W` for the range of `ℓ - id`.

1. `ℓ` preserves the polar form (`vectorAction_preserves`), and `ℓ w = -w` on `W` because
   `ℓ` is an involution. Every vector `u` fixed by `ℓ` is polar-orthogonal to `W`, because
   `polar(u, w) = polar(ℓu, ℓw) = -polar(u, w)` and `2 ≠ 0`.
2. Every `v` splits as `u + w` with `u = ½(v + ℓv)` fixed and `w = -½(ℓv - v) ∈ W`. With
   the orthogonality of step 1, the nondegeneracy of `Q` implies that the restriction of the
   polar form to `W` is nondegenerate. So `W` has an orthogonal basis
   `c` (`LinearMap.BilinForm.exists_orthogonal_basis`) of anisotropic vectors.
3. `W ≠ 0` because `ℓ ≠ id`, so `dim W` is `1` or `2`.
   * If `dim W = 1`, spanned by `w₁`, then `ℓ` agrees with the reflection in `w₁` on fixed
     vectors and on `W`, so `ℓ` is that reflection. Its determinant is `-1`
     (`det_reflection`), contradicting `det_vectorAction` (spin lifts act with
     determinant `1`), since `2 ≠ 0`.
   * If `dim W = 2`, with orthogonal basis `w₁, w₂`, then `ℓ` is the reflection word of the
     list `[w₁, w₂]` (reflect in `w₁`, then in `w₂`), checked on fixed vectors and on
     `a w₁ + b w₂`.
4. The Clifford reflection word `a = ι w₂ · ι w₁` (`cliffordReflectionWord`) induces the same
   vector action as `unit Q s` and both are even. By
   `exists_smul_of_even_clifford_conj_eq` there is a scalar `t` with `unit Q s = t • a`.
5. The reversion norm of the unit is `1` (`reverse_mul_unit`), and that of `a` is
   `Q(w₁)Q(w₂)` (`reverse_mul_cliffordReflectionWord`), so `t² Q(w₁) Q(w₂) = 1`. Since
   `w₁ ⊥ w₂`, the vectors anticommute in the Clifford algebra (`ι_mul_ι_comm`), and
   `a · a = -Q(w₁)Q(w₂)` (`ι_sq_scalar`). Hence
   `unit · unit = t² · a · a = -t² Q(w₁)Q(w₂) = -1`.

## Provenance

This is the standard computation of the square of a lift to the spin group of a rotation by
`π` in a nondegenerate plane. The Lean result is derived from the Library's Clifford spin
lift API (`CliffordSpinLift`, `vectorAction`, `unit`, `exists_smul_of_even_clifford_conj_eq`,
reflection words) as described above.
