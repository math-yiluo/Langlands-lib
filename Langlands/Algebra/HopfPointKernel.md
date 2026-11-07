# Kernels of bounded Hopf points are determined modulo `m`

Author: Worker 1421.

Corollaries of `Langlands.Algebra.HopfPointRigidity` phrased with the kernel of
the scalar extension `scalarExt α : C ⊗[R] A → C[ℤ^r]`
(`Langlands.Algebra.HopfPointClosedLocus`). This kernel is the defining ideal
of the image torus of the corresponding homomorphism from the split torus.
These results are used for the descent datum of the torus in the chart
construction of task `45ac6e52-a4d8-4414-91f1-03c3be35223e`. Internal module.

- `scalarExt_comp_mapDomain`: precomposition of a point with `mapDomain T`
  corresponds to `mapDomain T` after the scalar extension.
- `ker_scalarExt_mapDomain_addEquiv`: for an automorphism `T` of the lattice,
  twisting by `T` does not change the kernel, since `mapDomain T` is injective.
- `ker_scalarExt_eq_of_red_eq`: let `α` and `α'` have generator values in
  `box r n` with generating supports, and reductions modulo
  `m ≥ rigidityBound r n` that differ by an automorphism `γ` of `(ℤ/m)^r`.
  Then their scalar extensions have the same kernel. This is
  `exists_addEquiv_of_red_eq` followed by the previous lemma.
- `eq_refl_of_mapDomain_comp_eq` (for nontrivial `C`): if `scalarExt β` is
  surjective and `mapDomain ε ∘ β = β` for an automorphism `ε` of `M`, then
  `ε` is the identity. Each `single χ 1` is in the range of `scalarExt β`, and
  `mapDomain ε` fixes that range. This gives freeness of the twisting action on
  the closed-immersion locus.
