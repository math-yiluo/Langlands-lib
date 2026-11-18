# Tensor decomposition for finite commuting compact and Lie families

This is an internal algebraic consequence of the published compact and Lie
Jacobson-density and multiplicity-evaluation results. It extracts a tensor
**equivalence**, with every local intertwining identity, by adapting the
recursion of `FiniteFamilyPairing.assembly`. It is not a statement quoted from
Cogdell, and it supplies only the algebraic tensor step needed toward the
Rankin–Selberg factorization task.

`Langlands.Archimedean.FiniteFamilyTensor.FiniteTensorDecompositionStatement`
asserts the following, and `finiteTensorDecomposition` proves it. Let `I` be
any finite index type. At each `i`, supply a group `K i` with a topology, a
complex Lie algebra `L i`, a complex vector space `A i`, a representation
`σ i` of `K i` on `A i`, and a Lie action `p i`. Assume the published
`GKModuleDensity.Hyp (σ i) (p i)` at each source. This is the actual density
hypothesis of the imported theory, not an assumption that the asserted tensor
equivalence exists.

Let `V` carry representations `κ i` and Lie actions `ψ i`. Require:

- `FamilyCommutes κ ψ`: operators at distinct indices commute, for compact
  with compact, compact with Lie, and Lie with Lie actions.
- `FamilyIrreducible κ ψ`: `V` is nonzero, and every submodule preserved by
  all these operators is zero or the whole space.
- At every `i`, there is a nonzero linear map `A i → V` intertwining both
  its compact and its Lie action, expressed using the published `gkHoms`.

Then there is a complex linear equivalence

`e : (⨂[ℂ] i, A i) ≃ₗ[ℂ] V`.

`IsTensorEquivalence` states its covariance on pure tensors. If two tuples
`a` and `b` agree away from `i` and `b i = σ i k (a i)`, then
`e (tprod b) = κ i k (e (tprod a))`. The same holds with `p i X` and
`ψ i X`. Using two tuples avoids a convention for transporting values in a
dependent function update. The assertion has five independent universe
parameters. The target universe is the maximum of the source-vector universe
and the auxiliary target universe, so taking multiplicities preserves it.

The auxiliary `TensorDecompositionStatement I` expresses the property for a
fixed index type, and `tensorDecomposition I` proves it under `[Finite I]`.
The exported proposition quantifies over all finite `I`; the empty family is
included. No pairing, compact twist or Lie twist is required.

The proof uses `Finite.induction_empty_option`.

1. A bijection of index types transports the commuting and irreducibility
   hypotheses and the nonzero source occurrences. `PiTensorProduct.reindex`
   transports the tensor equivalence back. Its pure tensor formula transports
   both covariance identities.
2. For an empty family, all submodules of `V` are invariant. Choose `v ≠ 0`
   and a linear functional `φ` with `φ v = 1`. Its kernel cannot be the whole
   space, so joint irreducibility makes its kernel zero. It is surjective
   because `φ (c • v) = c`. Composing the inverse equivalence `ℂ ≃ₗ[ℂ] V`
   with `PiTensorProduct.isEmptyEquiv` gives the result. Covariance is vacuous.
3. For `Option α`, remove the `none` factor. Set
   `M = gkHoms (σ none) (p none) (κ none) (ψ none)`. Its nonzero occurrence
   makes `M` nonzero. All other operators commute with the removed actions,
   and `GKTensorEvaluation.evaluationEquiv` gives
   `A none ⊗[ℂ] M ≃ₗ[ℂ] V` by evaluation.
4. Postcomposition puts all remaining compact and Lie actions on `M`.
   They still commute. `residual_irreducible` proves their joint
   irreducibility. `TensorContraction.exists_nonzero_contractedGKHom`
   preserves every remaining nonzero source occurrence. The induction
   hypothesis therefore identifies the remaining dependent tensor with `M`.
5. `optionEquiv` separates `A none` from the dependent option-indexed tensor,
   using reindexing to a sum, `tmulEquivDep`, the singleton tensor equivalence
   and tensor commutation. Its proved pure tensor formula identifies this
   equivalence with the expected separated pure tensor. Compose it with the
   tensor of the induction equivalence and then evaluation. At `none`,
   covariance follows from `evaluation_compact` and `evaluation_lie`; at a
   remaining index, it follows from the induction identities and the
   postcomposition evaluation identities.

The proof reuses the residual-action setup of the published
`FiniteFamilyPairing.assembly`, whose original output was a bilinear form;
this unit retains the equivalence instead. All imported mathematics is used by
Lean name. It neither constructs a simultaneous global Whittaker functional nor
proves its product formula, smooth extension, prescribed finite-vector
normalization, or archimedean integral nonvanishing. Those obligations, and the
unconditional `ArchimedeanFactorizationStatement`, remain open.
