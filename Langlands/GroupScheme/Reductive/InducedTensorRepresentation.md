# Tensor products of Galois conjugates of a representation and their induced intertwiners

This internal module shows that the induced twisting matrices of
`Algebra/KroneckerInduction` intertwine the tensor product of the Galois
conjugates of a representation with its Galois twists. It does not claim
that this tensor product representation descends to the ground field: such
intertwiners need not satisfy a cocycle condition (for `G = SL₁(ℍ)` over
`ℝ`, the standard two-dimensional complex representation is isomorphic to
its complex conjugate but is not defined over `ℝ`). The descended object in
the transfer argument is the twisted-fixed central simple algebra of the
induced matrices (`titsObstructionValue_eq_classOf_corCSAOf` in
`Reductive/TitsTransferMatrix`), whose Brauer class can be nontrivial. This
module is the group side of this development's matrix proof of
the integral-weight transfer law for the Tits obstruction
(`Reductive/TitsTransfer`), a derived analogue of Tits, *Représentations
linéaires irréductibles d'un groupe réductif sur un corps quelconque*,
J. reine angew. Math. 247 (1971), Proposition 5.1, printed p. 207 / PDF
p. 12, which is stated for `β` on central characters. Tits proves that
proposition cohomologically, citing his reference [14] (printed p. 219 /
PDF p. 24), S. Lang, *Rapport sur la cohomologie des groupes* (1966),
Proposition 13, p. 57. The present construction is this development's own.

Throughout, `K/k` is a field extension, `G` is a group scheme over `k`, and
representations of `G_K` have universal matrices with entries in
`K ⊗[k] O(G)` (`MatrixRepresentation/GaloisCoefficients`).

## Declarations (`MatrixRepresentation`)

- `galoisTensor_mul_apply`: the maps `σ ⊗ id` of `K ⊗[k] R` compose like the
  automorphisms `σ` (`Algebra.TensorProduct.ext'`).
- `universalMatrix_piTensor`: the universal matrix of the tensor product
  `piTensor ρ` (`Reductive/PiTensorWeights`) is the Kronecker product of the
  universal matrices of the `ρ i`. This is `piTensor_affineMatrix` at the
  universal point.
- `intertwines_galoisTwist_piTensor`: let `k ⊆ E ⊆ K`, and let
  `I : InductionData k E K (Fin (m + 1))` be induction data from `Gal(K/E)` to
  `Gal(K/k)`. Suppose `Q h` intertwines `ρ` with its twist `ρ^h` for every
  `h ∈ Gal(K/E)`. Then for every `τ ∈ Gal(K/k)` the induced matrix
  `inducedMatrix I Q τ` intertwines `Π = piTensor (i ↦ ρ^{I.ext i})` with its
  twist `Π^τ`.

  Proof. By `intertwines_iff_universalMatrix`, intertwining is an identity
  between universal matrices. By `universalMatrix_galoisTwist`, the universal
  matrix of a twist is the original one with `σ ⊗ id` applied entrywise. So
  the universal matrix of `Π` is the Kronecker product of the conjugates
  `(σ ⊗ id)(U_ρ)` with `σ = I.ext i`. Apply the Galois induction identity
  `inducedMatrix_mul_piKronecker` with coefficient ring `K ⊗[k] O(G)`, action
  `σ ↦ σ ⊗ id` and the constant family `Z = U_ρ`. Its hypothesis is the
  universal-matrix form of the intertwining by `Q h`. Since the family is
  constant, the permuted Kronecker product in that identity is `U_Π` itself.

## Declarations (`GaloisPinningData`)

- `hasTopWeight_galoisTwist`: let `d` be Galois pinning data. If `ρ` has top
  weight `λ` (`SplitPinning.HasTopWeight`: multiplicity one, all weights
  below), then its twist `ρ^σ` has top weight `σ ⋆ λ`, the image of `λ` under
  the star action of `σ`. Write the star action as `w · (Galois action)` with
  `w` in the Weyl group (`exists_weyl_mul_galoisAction_eq_starAction`). The
  weight spaces of `ρ^σ` are the Galois-conjugate subspaces of those of `ρ` at
  the Galois-conjugate weights (`representationWeightSpace_galoisTwist_smul`).
  Weight multiplicities are Weyl invariant
  (`finrank_representationWeightSpace_weyl`), and the star automorphism
  preserves `Q⁺` (`smul_mem_positiveRootMonoid`). The argument is that of
  the published `isHighestWeight_galoisTwist`, which treats a fixed `λ`.
