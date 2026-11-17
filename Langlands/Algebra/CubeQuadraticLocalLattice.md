# Local lattices from positive functions satisfying the cube identity

Module `Langlands.Algebra.CubeQuadraticLocalLattice`.

## Content

For an abelian group `M` and a rational-valued function `q : M → ℚ`:

- `CubeIdentity q` is the vanishing of the third difference:
  `q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)` for all
  `x y z`.
- `polar q x y = q (x + y) - q x - q y` is the polar form.

Under `CubeIdentity q` the module proves:

- `map_zero_of_cubeIdentity`: `q 0 = 0`.
- `polar_add_left`: the polar form is additive in its first argument, and
  `polar_comm` gives symmetry. `polar_zsmul_left` and `polar_neg_left`
  follow, using the packaged additive map `polarLeft`.
- `polar_self`: `polar q x x = q x + q (-x)`.
- `polar_self_pos`: if `q` is positive at every nonzero element, then
  `polar q x x > 0` for `x ≠ 0`.
- `exists_int_polar` (no cube identity needed): if `N * q x` is an integer for
  every `x`, then so is `N * polar q x y`.

Main theorem `fg_comap_of_cubeIdentity`: let `q` satisfy the cube identity, let
`N > 0` be such that `N * q x ∈ ℤ` for all `x`, and let `q` be positive at every
nonzero element. Then for every finitely generated `ℚ`-submodule `V` of
`ℚ ⊗[ℤ] M`, the preimage of `V` (viewed as a `ℤ`-module) under
`TensorProduct.mk ℤ ℚ M 1 : m ↦ 1 ⊗ m` is a finitely generated `ℤ`-module.

The map `TensorProduct.mk ℤ ℚ M 1` is written exactly as in
`Langlands.Rationalization.ofHom`, which is what
`Langlands.AbelianScheme.homToHom0` is defined to be. The conclusion therefore
has the same shape as the conclusion of
`Langlands.AbelianScheme.HomLocalLatticeStatement`.

## Proof

Finite generation of the preimage `P` comes from a linear map
`Φ : M → ℤ^s` whose kernel meets `P` trivially:

1. Choose finitely many generators `s` of `V`. Since `ℚ ⊗[ℤ] M` is the
   localization of `M` at the nonzero integers
   (`IsLocalization.tensorProduct_isLocalizedModule`), each generator `w` is
   `ι (y w) / n_w` for some `y w ∈ M` and nonzero integer `n_w`. Let `Z` be the
   span of the `y w`.
2. By induction on the span, every `v ∈ V` has a nonzero integer multiple equal
   to `ι x` for some `x ∈ Z`.
3. Define `Φ m = (N * polar q m (y w))_w`. These entries are integers by
   `exists_int_polar`, and `Φ` is additive by `polar_add_left`.
4. If `m ∈ P` and `Φ m = 0`, then `polar q x m = 0` for all `x ∈ Z` by
   additivity. By step 2, `n • ι m = ι x` with `x ∈ Z` and `n ≠ 0`. The kernel
   of `ι` is torsion (`IsLocalizedModule.eq_zero_iff`), so `t n • m = t • x`
   for some nonzero integer `t`. Hence `(t n) * polar q m m = t * polar q x m = 0`,
   so `polar q m m = 0` and `m = 0` by `polar_self_pos`.
5. `ℤ^s` is Noetherian, so the image `Φ(P)` is finitely generated, and
   `P ∩ ker Φ = 0`. Then `Submodule.fg_of_fg_map_of_fg_inf_ker` shows that `P`
   is finitely generated.

No torsion-freeness of `M` is assumed: positivity forces it.

## Provenance

This is an elementary lattice argument in the style of the classical proof
that `Hom(A, B)` is finitely generated. See Milne, *Abelian Varieties*
(1986 article, author revision 2022), proof of Theorem 12.5. There, for a simple
`A` and a finitely generated subgroup `M` of `End(A)`, the degree polynomial
`P : ℚM → ℚ` is positive on nonzero endomorphisms, so `ℚM ∩ End(A)` is
discrete in `ℚM` and hence finitely generated. Here a positive function with
bounded denominators that satisfies the cube identity plays the role of the
degree. Its polar form gives an integral embedding instead of an analytic
discreteness argument. The `ℚ`-valued formulation is internal to this
project. It is the form in which the geometric input (a mixed Euler
coefficient of pullbacks of an ample line bundle) is available.
