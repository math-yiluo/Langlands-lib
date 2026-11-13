# The top standard Hecke operator

Author: Worker 5137.

This helper module belongs to the proof of
`Langlands.ClassField.Global.RelativeWeilGroup.AssociatedCentralCharacterStatement` (Task 5210).
It records the standard fact that the top standard Hecke operator of `GL_(r+1)` over a p-adic
field `F` is translation by the scalar matrix of the uniformizer, with Hecke scalar the
product of the Satake parameters.

Throughout, `F` is a p-adic field with its canonical topology (the local instances of
`PairedHeckeScalars`), `ϖ` is its canonical uniformizer, and
`K = sphericalOpenSubgroup F r = GL_(r+1)(𝒪_F)`.

## Declarations in `Langlands.Unramified`

- `standardDiagonal_last`: the standard diagonal with index `r + 1`,
  `diag(ϖ, …, ϖ)`, is the scalar matrix `Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) ϖ`.
  Proof: entrywise; the condition `j < r + 1` in `standardDiagonal_val` always holds.
- `standardDiagonal_last_commute`: this standard diagonal commutes with every
  `g : GL_(r+1)(F)`, since scalar matrices are central (`Matrix.scalar_comm`).
- `cosetIndex_last_subsingleton` (instance) and `cosetIndexLast`: the index set
  `CosetIndex Λ m m` of the labelled left cosets in the top double coset has exactly one
  element. A subset of `Fin m` with `m` elements is `Finset.univ`, and the labelling
  function is then defined on an empty set of positions.
- `standardHecke_cornerAction_last`: for a smooth representation `ρ` on `V` and a
  `K`-fixed vector `a`,
  `corner F ρ hρ (standardHeckeElement F r (Fin.last (r + 1))) a = ρ(standardDiagonal F r (Fin.last (r + 1))) a`.
  Proof: by `standardHecke_cornerAction_eq_sum` the operator is the sum of `ρ(x_α) a` over the
  labelled coset representatives `x_α`. The index set has one element, so the sum is a single
  term (`Fintype.sum_subsingleton`). That representative lies in `k₁ t k₂` with
  `k₁, k₂ ∈ K` and `t` the standard diagonal (`labelledRep_mem_doubleCoset`,
  `standardDiagonal_eq_subsetTorus`). Since `t` is central and `a` is `K`-fixed,
  `ρ(k₁ t k₂) a = ρ(t) ρ(k₁) a = ρ(t) a`.
- `standardHeckeScalar_last`: for `s : Eigenvalues (r + 1)`,
  `standardHeckeScalar F s (Fin.last (r + 1)) = elementaryCoefficient s (r + 1)`. The
  normalizing factor `(√q) ^ (i (r + 1 - i))` is `1` for `i = r + 1`.
