# Reduction of integral invertible matrices to the residue field

Lean module: `Langlands.Group.GL.IntegralReduction`, namespace
`Langlands.GeneralLinear.IntegralReduction`.

Let `F` be a field and `O` a subring of `F` that is a local ring, with residue field
`IsLocalRing.ResidueField O`. The integral subgroup `Conductor.integralSubgroup O m` of
`GL_{m+1}(F)` is the image of `GL_{m+1}(O)` under entrywise inclusion.

## Declarations

- `integralEquiv O m : GL_{m+1}(O) ≃* Conductor.integralSubgroup O m`, from the injectivity of
  the inclusion (`Conductor.integral_map_injective`); `integralEquiv_apply_val` and
  `integralEquiv_symm_apply_val` compute entries.
- `reduction O m : Conductor.integralSubgroup O m →* GL_{m+1}(ResidueField O)`, entrywise
  reduction modulo the maximal ideal (`reduction_apply`).
- `residueSection O : ResidueField O → O`, a set-theoretic section of the residue map with
  `residueSection O 0 = 0` and `residueSection O 1 = 1`.
- `liftMatrix`, `liftUnit` and `lift O m γ`: the entrywise lift of a residue invertible matrix
  `γ`. Its determinant reduces to `det γ ≠ 0`, so it is a unit of the local ring `O`
  (`isUnit_det_liftMatrix`), and the lift is an invertible integral matrix.
  `lift_apply` gives its entries.
- `reduction_lift`: `reduction O m (lift O m γ) = γ`; hence `reduction_surjective`.
- `lift_mem_unipotentSubgroup`: if `γ` lies in the unipotent radical
  `B.unipotentSubgroup` of a standard block parabolic over the residue field, then its lift lies
  in the unipotent radical of the same block shape over `F`. The lift preserves the zero entries
  below the diagonal blocks and the identity diagonal blocks, because the section fixes `0` and
  `1`.

## Provenance

Derived, internal material: the standard reduction map `GL_N(𝔬) → GL_N(k)` and its surjectivity,
used for representations of level zero (Bushnell–Kutzko 1993,
`bushnell-kutzko-1993-admissible-dual`, Chapter 5).
