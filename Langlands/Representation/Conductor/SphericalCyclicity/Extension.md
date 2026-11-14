# Extension by zero from the big cell

Author: Worker 392.

This helper module of the proof of
`Langlands.Conductor.OrderedUnramifiedSphericalCyclicityStatement` (see
[`OrderedUnramifiedSphericalCyclicity`](../OrderedUnramifiedSphericalCyclicity.md))
constructs the linear map

```
extend hϖ hq z : PrincipalSeries hϖ n hq (tailParam z) →ₗ[ℂ] PrincipalSeries hϖ (n + 1) hq z
```

from the Library's normalized unramified principal series of rank `n + 1` to the one of
rank `n + 2`. Here `tailParam z i = z (i + 1)`. The construction is an internal
auxiliary one, with no literature source. All declarations are in
`Langlands.Conductor.SphericalCyclicity`. The notation is from [`Cells`](Cells.md)
and [`Parahoric`](Parahoric.md). `Borel m` is the Library's upper-triangular
subgroup of `GL_(m+1)`, `diagonalUnit`, `ord`, `halfModulusCharacter`,
`inducingCharacter`, `normalizedCharacter` and `sqrtResidueUnit` are the Library's,
and `s = sqrtResidueUnit hq` is the chosen square root of `q`.

## Borel elements

- `colT_borel` and `isUnit_det_low_borel`: an upper-triangular `b` has
  `colT b = 0` and an invertible lower-right block.
- `lowBorel b : Borel n` is `lowGL b`, which is again upper triangular.
  `lowBorel_val` and `lowBorel_coe` describe it. `diagonalUnit_lowBorel` says its
  `i`-th diagonal unit is the `(i+1)`-th diagonal unit of `b`.
- `ord_prod`: `ord` of a finite product of units is the sum of the `ord`s.
  `ordDet_borel`: `ordDet b = Σ_i ord (b_ii)`. `ord_headUnit_borel`:
  `ord (headUnit) = ord b₀₀`.

## Splitting the normalized character

- `modulus_exponent_split`: an integer identity for the modulus exponent
  `-Σ_i (n + 1 - 2i) o_i` of rank `n + 2`. It is
  `(-(n + 1) o_0 + Σ_j o_(j+1))` plus the rank-`n + 1` exponent of `j ↦ o_(j+1)`.
- `halfModulusCharacter_split`, `inducingCharacter_split` and
  `normalizedCharacter_split` follow from it. With `e = ord b₀₀`:

  ```
  χ_z(b) = z_0^e · s^(-(n+1) e + ordDet(lowBorel b)) · χ_(tailParam z)(lowBorel b).
  ```

- `value_borel_mul`: `f (b g) = χ(b) f(g)` for every principal-series function. This
  is the Library's covariance property, read through `value`.
- `exists_level`: every principal-series function is right invariant under
  `principalLevelSubgroup F m a` for some `a > 0`. This uses smoothness and the
  Library's `exists_pos_principalLevelOpenSubgroup_subset`. `level f` is a chosen
  such `a`, with `level_pos` and `level_spec`.

## Cell functions

For `x : GL (Fin (n + 2)) F`:

- `headOrd x = ordDet x - ordDet (lowGL x)`;
- `cellScalar hq z x = z_0^(headOrd x) · s^(-(n+1) headOrd x + ordDet (lowGL x))`;
- `IsSmall v` means that every coordinate of `v` has valuation `< 1`;
- `cellFun hq z P φ x` is `cellScalar x * φ (lowGL x)` when `det (low x)` is a unit
  and `P (cellVec x)` holds, and `0` otherwise. Here `P` is a predicate on vectors and
  `φ : GL_(n+1)(F) → ℂ`. `cellFun_of` and `cellFun_of_not` evaluate it.
  `cellFun_eq_of_iff` compares two cell functions from the equivalence of their
  conditions and their values where the conditions hold.

Transformation rules:

- `lowGL_congr`, `lowGL_mul_lowerUnip`, `isUnit_det_low_mul_lowerUnip`,
  `cellVec_mul_lowerUnip` (`cellVec (x L(y)) = cellVec x + y`),
  `ordDet_mul_lowerUnip`, `cellScalar_mul_lowerUnip` and `cellFun_mul_lowerUnip`:
  right multiplication by `L(y)` replaces `P` by `v ↦ P (v + y)`.
- `cellScalar_eq_of`: shifting `headOrd` by `o` and `ordDet (lowGL ·)` by `d`
  multiplies `cellScalar` by `z_0^o s^(-(n+1) o + d)`.
- `low_mul_blockDiag`, `colT_mul_blockDiag`, `isUnit_det_low_mul_blockDiag`,
  `cellVec_mul_blockDiag` (`cellVec (x diag(α,h)) = α • h⁻¹ cellVec x`),
  `lowGL_mul_blockDiag`, `ordDet_blockDiag` and `cellFun_mul_blockDiag`. The last
  gives right multiplication by `diag(α, h)`. It multiplies by
  `z_0^(ord α) s^(-(n+1) ord α + ordDet h)` and replaces `P` and `φ` by
  `v ↦ P (α • h⁻¹ v)` and `g ↦ φ (g h)`.
- `cellFun_borel_mul`: if `φ` is covariant for `χ_(tailParam z)`, then `cellFun` is
  covariant for `χ_z` under left multiplication by `b ∈ Borel (n + 1)`. The proof
  uses `lowGL (b x) = lowBorel b * lowGL x`, `cellScalar_eq_of` and
  `normalizedCharacter_split`.
- `isSmall_iff` and `cellFun_isSmall`: with `P = IsSmall`, the condition is exactly
  `InCell x`.
- `cellFun_mul_parahoric`: for `k` in the parahoric subgroup `J`,
  `cellFun IsSmall φ (x k)` is `cellScalar x * φ (lowGL x * lowGL (L(cellVec x) k))` on
  the cell and `0` off it. This follows from `cell_mul_parahoric`, and from the
  vanishing of `ordDet` on integral matrices, which leaves `cellScalar` unchanged.

## The extension

- `extFun ψ = cellFun hq z IsSmall (value ψ)`. By `extFun_apply`, its value at `x` is
  `cellScalar x * ψ (lowGL x)` for `InCell x`, and `0` otherwise.
- `extFun_covariance`: Borel covariance for `χ_z`, from `cellFun_borel_mul`.
- `extFun_mul_level`: if `ψ` is fixed by the level-`a` subgroup of `GL_(n+1)` with
  `a > 0`, then `extFun ψ` is right invariant under the level-`a` subgroup of
  `GL_(n+2)`. This uses `cellFun_mul_parahoric` and
  `lowGL_lowerUnip_mul_mem_principalLevel`.
- `value_add` and `value_smul` hold definitionally.
- `extend hq z` packages `extFun ψ` with the Library's `smoothFunctionOf` and the
  open subgroup `principalLevelOpenSubgroup F (n + 1) (level ψ)`. It is additive and
  `ℂ`-homogeneous by `extFun_apply` and case analysis on `InCell`.
  `extend_value` gives `value (extend ψ) x = extFun ψ x`.
