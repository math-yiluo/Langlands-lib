# The standard principal order with equal block sizes

The matrix model for the level-zero data of BK93 (5.5.10)(b) uses indices
`Ix e f = Fin f × Fin e`, with the second coordinate indexing the block.
The coefficient conditions come from stabilizing the adapted lattice chain.
[Adapted basis](LevelZeroAdaptedBasis.md)

- `InOrd x` asks that every entry of `x` be integral and that entries with
  `p.2 < q.2` lie in the maximal ideal. This is the order that stabilizes the
  lattices `L_j` spanned by `ϖ e_p` for `p.2 < j` and `e_p` for `p.2 ≥ j`.
- `InRad x` asks that every entry be integral and that entries with
  `p.2 ≤ q.2` lie in the maximal ideal. This models the Jacobson radical
  of the order.
- `J0 F e f` consists of units `g` such that `InOrd` holds for `g` and `g⁻¹`.
  It models `U(𝔄)`.
- `J1 F e f` consists of elements of `J0 F e f` with `InRad (g - 1)`. It
  models `U^1(𝔄)`.

Entrywise uses of the ultrametric inequality give closure of the order,
the radical ideal properties, the subgroup laws for `J0` and `J1`, and the
normality of `J1` in `J0` by `conj_mem_J1`. The identification of these
subgroups with the lattice-chain definitions uses the adapted basis.
[Unit group comparison](LevelZeroTransport.md)
