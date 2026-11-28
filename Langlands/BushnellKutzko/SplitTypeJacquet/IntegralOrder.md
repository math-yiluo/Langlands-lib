# Block-triangular integrality conditions and their unit groups

Module `Langlands.BushnellKutzko.SplitTypeJacquet.IntegralOrder`.

Let `F` be a field with a valuative relation and `blk : ι → ℕ` a block function on a finite index
type. `InOrd blk x` says that every entry of the matrix `x` is integral and that the entries
`x p q` with `blk q < blk p` (strictly below the block diagonal) lie in the maximal ideal;
`InRad blk x` asks the same for the entries with `blk q ≤ blk p`. These conditions are closed
under addition and negation, `InOrd` under multiplication, and products of `InOrd` with `InRad`
lie in `InRad`; all of this holds over any field with a valuative relation.

When `F` is a nonarchimedean local field, the matrices with `InOrd` and with `InRad` are, in
coordinates adapted to a lattice chain, the hereditary order of the chain and its Jacobson radical
(C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
§1.1, printed pp. 19–23): this is `toLin_coordBasis_mem_order_iff` and
`toLin_coordBasis_mem_endFiltration_one_iff` in the module `LayerCoordinates`. No such
interpretation is claimed for a general valuative relation. For a nondiscrete valuation, the
`InOrd` matrices need not form a finitely generated lattice.

`J0 F blk` is the subgroup of invertible matrices `g` with `InOrd g` and `InOrd g⁻¹`, and `J1 F
blk` the subgroup of `g ∈ J0 F blk` with `InRad (g - 1)`; over a nonarchimedean local field these
are the groups `U(𝔄)` and `U^1(𝔄)` in adapted coordinates (`stdToAut_mem_unitFiltration_zero_iff`,
`stdToAut_mem_unitFiltration_one_iff` in `LayerCoordinates`). `conj_mem_J1` shows that `J1` is
normal in `J0`.

The module also records the uniformizer lemmas `val_uniformizer_lt_one` and
`val_uniformizer_mul_lt_one`, valuation bounds for products of integral matrices
(`int_mul_le_one`, `int_mul_lt_one`, `lt_one_mul_int`), and `exists_intGL_of_sub_one`: a matrix
congruent to the identity modulo the maximal ideal is invertible with integral inverse, since its
determinant reduces to `1` in the residue field.
