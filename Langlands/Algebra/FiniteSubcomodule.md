# Finitely generated subcomodules of flat coalgebras over noetherian rings

Author: Worker 1421.

This module proves Serre's local finiteness theorem for the right regular
comodule of a flat coalgebra over a noetherian ring, and the resulting
finitely generated subcomodule that generates a bialgebra. It is an internal
helper for the construction of charts of the closed torus subgroup functor
(task `45ac6e52-a4d8-4414-91f1-03c3be35223e`). The statement is from J.-P.
Serre, *Groupes de Grothendieck des schémas en groupes réductifs déployés*,
Publ. Math. IHÉS 34 (1968), §1.5, Proposition 2. Only the case of the
comodule `C` itself is formalized here.

Throughout, `R` is a commutative ring and `C` an `R`-coalgebra (Mathlib's
`Coalgebra R C`) with comultiplication `comul`.

## Definitions

- `IsRightSubcomodule N`, for a submodule `N` of `C`: every `x ∈ N` has
  `comul x` in the image of `N ⊗ C → C ⊗ C`. That map is
  `N.subtype.rTensor C`.
- `core N`: the preimage under `comul` of that image. `mem_core` unfolds it.

## Results

- `core_le`: `core N ≤ N`. Apply `counit` in the second factor:
  `(id ⊗ ε)(comul y) = y ⊗ 1` (Mathlib's `lTensor_counit_comul`). For `y` in
  the core, the same element is the image of an element of `N ⊗ R`, so `y ∈ N`
  after `TensorProduct.rid`.
- `core_eq_ker`: `core N` is the kernel of `comul` followed by reduction
  modulo `N` in the first factor. This is right exactness of `- ⊗ C`
  (Mathlib's `rTensor_exact`). Flatness is not used here.
- `rTensor_mkQ_assoc_symm_lTensor_comul`: for `z ∈ N ⊗ C`, applying
  `comul` to the second factor, reassociating, and reducing the first factor
  modulo `N` gives `0`. Proof: induction on `z` and on `comul c`.
- `isRightSubcomodule_core` (needs `Module.Flat R C`): `core N` is a right
  subcomodule. For `y ∈ core N`, coassociativity (`coassoc_symm_apply`) and the
  previous lemma show that `comul y` is killed by `φ.rTensor C`, where `φ` is the
  map of `core_eq_ker`. Flatness makes `ker φ ⊗ C → ker (φ.rTensor C)`
  surjective (`Module.Flat.rTensor_exact`), so `comul y` comes from
  `core N ⊗ C`.
- `IsRightSubcomodule.sup`: sums of right subcomodules are right subcomodules.
- `exists_fg_isRightSubcomodule` (needs `IsNoetherianRing R` and
  `Module.Flat R C`): every `x ∈ C` lies in a finitely generated right
  subcomodule. Choose a finitely generated `N` with `comul x` in the image of
  `N ⊗ C` (`TensorProduct.exists_finite_submodule_left_of_setFinite`). Then
  `x ∈ core N`, and `core N ≤ N` is finitely generated because `N` is a
  noetherian module.
- `exists_fg_isRightSubcomodule_adjoin_eq_top`: a flat bialgebra `A` over a
  noetherian ring that is of finite type as an algebra has a finitely
  generated right subcomodule `V` with `Algebra.adjoin R V = ⊤`. Take the sum
  of subcomodules containing a finite set of algebra generators.
