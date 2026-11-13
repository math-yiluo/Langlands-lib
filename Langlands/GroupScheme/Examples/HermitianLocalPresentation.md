# Local Hermitian presentations identify the actual root model

Author: Worker 166.

This module connects the published general Hermitian presentation interface
(`HermitianMatrix.Form`, `HermitianMatrix.SchemeModel.Presentation`,
`Presentation.reindex` and `Presentation.rootIsometryIso`) with the published local
congruence theorem `HermitianRoot.local_exists_gram_congruence`. Here `K` is a
nonarchimedean local field (`IsNonarchimedeanLocalField` with its `ValuativeRel` and
topology), and `L/K` is a separable quadratic extension with involution
`SU3Root.fieldInvolution K L`. Any characteristic is allowed. The module is
infrastructure for Task 5973. It does not prove `LocalOuterTypeAHermitianModelStatement`
or `LocalAnisotropicTypeAInnerStatement`: nothing here produces a presentation of a
group scheme from its Tits index. A presentation is always a supplied hypothesis.

## Definitions

Let `J : Form (fieldInvolution K L) (HermitianRoot.Index (Fin m))` be a nonsingular
Hermitian form with `hm : 1 ≤ m`. Write `Pᴴ` for `adjoint (fieldInvolution K L) P`.

- `Form.localRootForm J hm` is a diagonal Hermitian form `H` on `Fin m`, chosen with
  `Classical.choose` from `Form.exists_local_root_congruence`. Its weights are nonzero
  (`localRootForm_weight_ne_zero`).
- `Form.localRootUnits J hm i` is the weight `(localRootForm J hm).weight i` as a unit
  of `L`, so `localRootUnits_val` holds by `rfl`.
- `Form.localRootMatrix J hm` is the chosen invertible matrix `Q` over `L` with
  `Qᴴ * gram (localRootForm J hm) * Q = J.gram` (`localRootMatrix_spec`).
- `Presentation.localRootIso e hm` takes a presentation `e : Presentation K L J G` of a
  group scheme `G` over `Spec K` and returns the isomorphism
  `G ≅ HermitianRoot.SchemeModel.groupScheme K L (localRootForm J hm)
  (localRootUnits J hm) (localRootUnits_val J hm)`. It is
  `e.rootIsometryIso` applied to the chosen form, units and matrix.

## Statements

- `Form.exists_local_root_congruence`: for `J` and `hm` as above, there are a diagonal
  form `H` on `Fin m` with nonzero weights and `Q : Matrix.GeneralLinearGroup
  (Index (Fin m)) L` with `Qᴴ * gram H * Q = J.gram`. This is the matrix equation
  required by `Presentation.rootIsometryIso`.
- `Presentation.exists_local_rootIso`: let `Idx` be a finite type with
  `Fintype.card Idx = m + 2` and `1 ≤ m`. Let `J` be a nonsingular Hermitian form on
  `Idx` and `e : Presentation K L J G`. Then there are a diagonal form `H` on `Fin m`,
  units `w : Fin m → Lˣ` with `(w i : L) = H.weight i`, and an isomorphism
  `G ≅ HermitianRoot.SchemeModel.groupScheme K L H w hw`.
- `Presentation.exists_local_rootIso_of_card_eq_succ`: the same conclusion on
  `Fin (n - 1)` when `Fintype.card Idx = n + 1` and `2 ≤ n`. This is the conclusion
  shape of `LocalOuterTypeAHermitianModelStatement` for a fixed `L`.

## Proofs

For `exists_local_root_congruence`, the Gram matrix of `J` is invertible, so its
determinant is nonzero (`Matrix.isUnit_iff_isUnit_det`). `J.hermitian` is the
hypothesis `conjugateTranspose (fieldInvolution K L) M = M` of
`local_exists_gram_congruence`, because `adjoint` and `conjugateTranspose` are both
the transpose of the entrywise conjugate. That theorem gives `H` and `P` with
`Pᴴ * J.gram * P = gram H`. Take `Q = P⁻¹`. Then `Qᴴ * (Pᴴ * J.gram * P) * Q` equals
`(P * Q)ᴴ * J.gram * (P * Q)` by `adjoint_mul` and associativity. Since `P * Q = 1`,
this is `J.gram`.

The definitions `localRootForm`, `localRootUnits` and `localRootMatrix` unpack this
existence statement, and `localRootIso` is a direct application of the published
`rootIsometryIso`.

For `exists_local_rootIso`, the index type `HermitianRoot.Index (Fin m)` is
`Unit ⊕ (Fin m ⊕ Unit)`, of cardinality `m + 2`. So `Fintype.equivOfCardEq` gives an
equivalence `r : Idx ≃ Index (Fin m)`. The published `Presentation.reindex` moves `e` to
a presentation by `J.reindex r`, and `localRootIso` applies to it.
`exists_local_rootIso_of_card_eq_succ` uses `m = n - 1`.

## Provenance

Internal. The module composes published Library results and adds only an elementary
matrix computation and a reindexing. No external statement is transcribed.
