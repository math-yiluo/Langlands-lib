# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The unipotent transform of a matrix Schwartz–Bruhat function**

For a Schwartz–Bruhat function `Φ` on `(n+1) × (n+1)` matrices over a canonical
`p`-adic field and the standard character `θ`, the transform
`J(M) = ∫_N Φ(u M) θ(u) du` is defined for every matrix `M`. It is left
`(N, θ⁻¹)`-equivariant, inherits every right invariance of `Φ`, vanishes on
`diag(d) k` unless the diagonal `d` is bounded and its entries after the first are
bounded below, and is uniformly locally constant in the first diagonal entry.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicLatticeGeometryProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixIwasawa`
- `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneIwasawa.lattice_mul` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.lattice_mono` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.mem_lattice_zero_iff` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.one_mem_lattice_zero` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.exists_mem_lattice` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.inv_mem_lattice_of_notMem` (theorem): An element outside a lattice has inverse in the opposite lattice.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.isOpen_lattice` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.isCompact_lattice` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.matLattice` (def): Matrices with all entries in one lattice.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.mem_matLattice` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.matLattice_mono` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.matLattice_mul` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.matLattice_mul_integral` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.integral_mul_matLattice` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.integralSubgroup_mem_matLattice` (theorem): Integral invertible matrices and their inverses have integral entries.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.isOpen_matLattice` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.exists_lattice_subset` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.matLattice_basis` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.exists_mem_matLattice` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.schwartz_support_bound` (theorem): A matrix Schwartz–Bruhat function is supported in one matrix lattice.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.schwartz_invariance` (theorem): A matrix Schwartz–Bruhat function is invariant under one matrix lattice.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.schwartzOfLattice` (def): A function on `F` invariant under one lattice and supported in another is
  Schwartz–Bruhat.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.schwartzOfLattice_apply` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.unipotentTransform` (def): The unipotent transform `J(M) = ∫_N Φ(u M) θ(u) du` of a matrix test function,
  for an arbitrary (possibly singular) matrix `M`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.unipotentTransform_mul_right` (theorem): Right invariances of the test function pass to the transform.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.exists_ne_zero_of_unipotentTransform_ne_zero` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.one_add_single_apply` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.elemUnipotent` (def): The elementary unipotent matrix `1 + t E_{i, i+1}`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.elemUnipotent_val` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.standardCharacter_elemUnipotent` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.unipotentTransform_eq_zero_of_shift` (theorem): If right translation by `1 + t E_{i,i+1}` with `ψ(t) ≠ 1` does not change the
  integrand, the transform vanishes.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.exists_lattice_nontrivial` (theorem): A nontrivial character is nontrivial on some lattice.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.unipotent_col_zero` (theorem): Entries of the first column of an upper unipotent matrix.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.unipotent_mul_single_zero` (theorem): An upper unipotent matrix fixes the corner matrix unit on the left.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.mem_matLattice_of_support` (theorem): If `Φ(A k) ≠ 0` with `k` integral, then `A` lies in the support lattice.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.ColBound` (def): Column `j` of every unipotent `u` with `Φ(u M) ≠ 0` lies in the lattice of level `B`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.colBound_zero` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.colBound_of_inv` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.inv_mem_of_colBound` (theorem): The inductive step of the lower bound: a bounded column forces the next
  diagonal entry away from zero when the transform does not vanish.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.unipotentTransform_diag_bounds` (theorem): **Support of the transform on `diag(d) k`.** There are levels `R` and `E` such that
  `J(diag(d) k) ≠ 0` for integral `k` forces every `dᵢ` into the lattice of level `R` and
  every inverse `dᵢ⁻¹` with `i ≥ 1` into the lattice of level `E`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.exists_cornerSchwartz` (theorem): **The corner transform is Schwartz.** For fixed `a` and integral `k`, the function
  `x ↦ J(diag(x, a) k)` on `F` (including `x = 0`) is Schwartz–Bruhat.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.mul_sub_one_mem` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.congruenceGroup` (def): The congruence subgroup of level `m`: `k - 1` and `k⁻¹ - 1` have entries in `πᵐ O`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.one_add_mem_lattice_zero` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.congruenceGroup_le_integral` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.conj_mem_congruenceGroup` (theorem): The congruence subgroups are normalized by the integral subgroup.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.isOpen_congruenceGroup` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.exists_congruenceGroup_le` (theorem): Every open subgroup contains a congruence subgroup.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.exists_schwartz_congruence` (theorem): Right invariance of a matrix Schwartz–Bruhat function under deep congruence subgroups.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.RankOneIwasawa.exists_filtration_bounds`, `Langlands.RankinSelberg.RankOneIwasawa.unipotentTransform_unipotent_mul`, `Langlands.RankinSelberg.RankOneIwasawa.castSucc_lt_succ'`, `Langlands.RankinSelberg.RankOneIwasawa.mem_congruenceGroup`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
