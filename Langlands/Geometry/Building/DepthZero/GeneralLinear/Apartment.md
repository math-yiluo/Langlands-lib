# The apartment of the diagonal torus of `GL_N`

Module `Langlands.Geometry.Building.DepthZero.GeneralLinear.Apartment`, namespace
`Langlands.Geometry.Building.GeneralLinearParahoric`.

For apartment data `A : KPApartmentData (diagTorus F N) (localFieldOrder F)` over a
nonarchimedean local field `F`, with the root values `c_{kl}(x) = rootValue A x k l` of the
module `Langlands.Geometry.Building.DepthZero.GeneralLinear.Valuation`, this module describes the
apartment, its filtrations, its affine roots and its vertices.

## Coordinates

- `coordCharacter k`: the character `e_k` of the diagonal split torus;
  `rootCharacter_eq_sub`, `eval_rootCharacter`: `e_k − e_l` evaluates as the difference of the
  coordinates.
- `exists_eval_coordCharacter`: every family of real coordinates `z_k` is `e_k(w)` for some
  `w ∈ V(S)`.
- `rootOf hkl`: `e_k − e_l` as an element of the set of relative roots.
- `rootValue_vadd`, `rootValue_mk_vadd`: translating `x` by `v` adds `(e_k − e_l)(v)` to
  `c_{kl}` (from `KPApartmentData.val_mk_vadd` and `RootFunctionFamily.vadd_apply`).
- `eq_of_rootValue_eq`: a point of the apartment is determined by its root values; the
  difference of two points with equal root values lies in the annihilator of the roots, which is
  zero in `TranslationSpace`.

## Filtrations and affine roots

- `mem_filtration_iff`: `U_{kl,x,r}` consists of the transvections `1 + t E_{kl}` with `t = 0`
  or `r ≤ ord(t) + c_{kl}(x)` (`val_transvectionPoint`).
- `two_nsmul_rootCharacter_not_mem`, `doubleRootGroupPoints_rootCharacter`: `2(e_k − e_l)` is not
  a root, so the double root groups are trivial.
- `affineFunctional_apply_eq`: the affine functional of derivative `e_k − e_l` with value `r` at
  `x₀` is `y ↦ c_{kl}(y) − c_{kl}(x₀) + r`.
- `exists_affineRoot_eq`: for `k ≠ l` and `m ∈ ℤ`, `y ↦ c_{kl}(y) + m` is an affine root
  (`KPApartmentData.affineRoots`). The element `1 + ϖ^m E_{kl}` of `U_ψ` is not in
  `U_{ψ+} · U_{2a, 2ψ}`, since its value is exactly `ψ` and the double root group is trivial.
- `localFieldOrder_eq_intCast`: `ord` takes integer values.
- `affineRoot_apply_eq`: every affine root is `y ↦ c_{kl}(y) + m` for some `k ≠ l` and
  `m ∈ ℤ`. If the constant is not an integer, no element of `U_ψ` has value exactly `ψ`
  (values are `ord t + c_{kl}`), so `U_ψ = U_{ψ+}` and `ψ` is not an affine root.

## Vertices and chambers

- `forall_affineRoot_ne_zero_iff`: `x` lies on no root hyperplane exactly when no `c_{kl}(x)`
  with `k ≠ l` is an integer.
- `min_fract_le_abs_add_intCast`, `sign_add_eq_of_abs_lt`: elementary estimates on the distance
  to `ℤ` and on signs.
- `isVertex_iff`: **`x` is a vertex (`AffineRootSystem.IsVertex`) exactly when all `c_{kl}(x)`
  are integers.** If they are, a point of the facet of `x` has the same sign as `x` on each
  root `c_{kl} − c_{kl}(x)`, hence the same root values, hence equals `x`. If some `c_{k₀l₀}(x)`
  is not an integer, write `c_{kl}(x) = y_k − y_l` and let `C` be the indices `m` with
  `fract(y_m) = fract(y_{k₀})`; moving the coordinates in `C` by a small `δ/2` (smaller than
  the distance to `ℤ` of every `y_p − y_q` with `p ∈ C`, `q ∉ C`) does not change the sign of
  any affine root, so it gives a second point of the facet of `x`.

For `N ≥ 2` this is the affine root system of type `Ã_{N−1}` of `GL_N` (Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach*, Cambridge University Press, 2023, §15.1,
literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`). For `N ≤ 1` there are
no distinct indices, so the affine root set is empty. The calculation uses the valuation
computed in `Langlands.Geometry.Building.DepthZero.GeneralLinear.Valuation` and the
definitions of `KPApartmentData.affineRoots` and `AffineRootSystem.facet`.
