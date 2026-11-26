# Transverse and centralizer coordinates near the identity

The module `Langlands.Analysis.Local.WeylChartCoordinates` sets up linear coordinates near
the identity of the unit group `Rˣ` of a normed algebra `R` over a nontrivially normed field
`F`, adapted to a unit `γ`.

## Definitions

- `defect F γ`: the `F`-linear adjoint defect `X ↦ γ X γ⁻¹ − X` of `R` (`defect_apply`).
- `centralizerAlg F γ`: the centralizer subalgebra of `γ` in `R`.
- `Coord F γ`: the product of the image of `defect F γ` (the transverse directions) and
  `centralizerAlg F γ`, with the product (maximum) norm.
- `IsRegularPosition F γ`: the image of `defect F γ` and the centralizer are complementary
  subspaces. For a regular semisimple matrix this is the splitting of the matrix algebra into
  the image and kernel of `Ad γ − 1`.
- `coordEquiv`, `coordCLE`: the linear equivalence `(y, s) ↦ y + s` from `Coord F γ` to `R`
  given by the complement, and the same map as a continuous linear equivalence when `F` is
  complete and `R` is finite dimensional. `coordConst` is the operator norm of its inverse.
- `IsSmallRadius hγ r`: `0 < r`, `r < 1` and `coordConst * r < 1`.
- `unitBall hγ hr`: the units `u` with `‖coordCLE⁻¹ (u − 1)‖ ≤ r`, a subgroup of `Rˣ` for
  every small radius; `ringBall hγ r` is the corresponding set of ring elements.

The instance `prod_isUltrametricDist` says that the product of two ultrametric spaces, with
the maximum distance, is ultrametric.

## Results

With `R` ultrametric, `‖coordEquiv x‖ ≤ ‖x‖` (`norm_coordEquiv_le`), hence
`‖z‖ ≤ ‖coordCLE⁻¹ z‖` and the product estimate
`‖coordCLE⁻¹ (a b)‖ ≤ coordConst * ‖coordCLE⁻¹ a‖ * ‖coordCLE⁻¹ b‖`
(`norm_coordCLE_symm_mul_le`). The subgroup property of `unitBall` follows: with
`a = u − 1` and `b = v − 1`, `uv − 1 = a + b + ab`, and the ultrametric inequality with
`coordConst * r * r ≤ r` bounds it. For inverses, `b = u⁻¹ − 1` satisfies `b = −a − ab`. If
`‖coordCLE⁻¹ b‖ > r` then `‖coordCLE⁻¹ b‖ ≤ coordConst * r * ‖coordCLE⁻¹ b‖`, which
contradicts `coordConst * r < 1`.

Under the further hypotheses that `F` is complete, ultrametric and proper and that `R` is
complete: `ringBall` is the image of the closed ball of radius `r` under
`x ↦ 1 + coordCLE x` (`ringBall_eq_image`); its elements are units (`isUnit_of_mem_ringBall`,
since `‖a − 1‖ < 1`); `val '' unitBall = ringBall` (`image_val_unitBall`); and `ringBall`
and `unitBall` are compact and, for positive radius, open (`isCompact_ringBall`,
`isOpen_ringBall`, `isOpen_unitBall`, `isCompact_unitBall`). Openness uses that closed balls
of positive radius are open in an ultrametric space.

## Role

These coordinates are an internal device for the local change of variables of the ordinary
Weyl map at a regular point (Henniart–Lemaire, *Changement de base et induction automorphe
pour GLₙ en caractéristique non nulle*, Mém. SMF 124 (2011), II.2.10).
