# Local transfer of coboundary data to the block cocycle

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisLocalStep`.

`IsCoboundaryAt.block`: let `H = adjoinSkewLine H₁ c₀` be antihermitian and invertible,
`u ∈ suGroup τ H L`, and `c₁` the block crossed homomorphism with
`blockUnit (c₁ s) = u * c s * s(u)⁻¹`. If `c` has coboundary data at a field `K` and
`ProperWittAt τ K (m + 1)` holds, then `c₁` has coboundary data at `K`.

Proof: over `M`, `b' = u * b` is a primitive of the twisted cocycle; its last row `y` is
`Gal(M/K)`-fixed (because the twisted values fix the last row), so it descends to `K`, where
it has the value `c₀` of the last row. Proper Witt transitivity over `K` gives `w` over `K`
of reduced norm one with `lastRow * w = y`; then `b' w⁻¹` fixes the last row and is a block
unit `blockUnit b₁`, and `b₁` is the required primitive (`tensorIncl_matrixSesqBilin` and
`unitMap_fixes_base` handle the coefficient change from `K` to `M`).
