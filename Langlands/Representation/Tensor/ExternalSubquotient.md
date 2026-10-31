# Irreducible subquotients of external tensor products

Module `Langlands.Representation.Tensor.ExternalSubquotient`, namespace
`Langlands.FiniteTensor`.

## Purpose and provenance

This is an internal algebraic helper for the tensor-route proof of
`Langlands.GLCuspidalInductionJacquetConstituentStatement`. It is used in
`Langlands.Representation.Exponents.CuspidalInductionJacquetConstituentConditional`.
No literature result is formalized here. The two main results are standard
facts of linear algebra over a field. The module proves:

* an irreducible actual subquotient of `M ⊗ J`, where the group acts trivially on
  `M`, is an actual subquotient of `J`;
* if an external tensor product of irreducible representations `⊗ ρ_i` is an
  actual subquotient of an external tensor product `⊗ J_i`, then each `ρ_k` is an
  actual subquotient of `J_k`.

"Actual subquotient" is `Langlands.WeylBranchPieces.IsSubquotient A Y`: there
is a subrepresentation `U` of `A` and a surjective intertwining map from `U`
onto `Y`. All spaces are complex vector spaces of arbitrary dimension. No
finiteness, smoothness or admissibility is assumed. The group, carrier and index
universes are independent.

## Declarations

### A trivially acted tensor factor (section `Slot`)

Here `G` is a group and `M`, `W`, `X` are complex vector spaces. Also
`τ : Representation ℂ G M` with `hτ : ∀ g, τ g = 1`, and
`J : Representation ℂ G W`. The tensor product representation is Mathlib's
`Representation.tprod τ J` on `M ⊗[ℂ] W`.

* `trivialContraction τ hτ J φ` (for `φ : Module.Dual ℂ M`): the intertwining map
  `Representation.tprod τ J → J` given by `m ⊗ w ↦ φ m • w`. It is
  `TensorProduct.lid` composed with `φ.rTensor W`. It intertwines because `τ`
  acts trivially. `trivialContraction_tmul` records the formula on pure tensors.
* `trivialContraction_surjective`: if `φ m = 1` for some `m`, the contraction is
  surjective, since `m ⊗ w ↦ w`.
* `leftSlice τ hτ J N` (for a subspace `N` of `M`): the subrepresentation of
  `Representation.tprod τ J` whose underlying subspace is the range of
  `N.subtype.rTensor W : N ⊗ W → M ⊗ W`. These are the tensors whose left
  factors lie in `N`. It is invariant because `g` acts by `id ⊗ J g`, which maps
  `N ⊗ W` into itself (`lTensor`). This is checked by tensor induction.
* `mem_range_of_trivialContraction_eq_zero`: let `m ∈ N` with `φ m = 1`, and let
  `y : N ⊗ W` be a tensor whose image in `M ⊗ W` is killed by the contraction.
  Then that image lies in the range of `(N ⊓ ker φ) ⊗ W`. Proof: the map
  `s : N → N ⊓ ker φ`, `n ↦ n - φ n • m`, gives an identity of linear maps
  `N ⊗ W → M ⊗ W`: the inclusion equals `(incl ∘ (s ⊗ id)) + (m ⊗ –) ∘ contraction ∘ incl`.
  This is checked on pure tensors with `TensorProduct.ext'`. Evaluating at `y`
  and using that the contraction vanishes gives the claim.
* `isSubquotient_of_tprod_trivial` (needs `hτ`; instance `[Y.IsIrreducible]` for
  `Y : Representation ℂ G X`): `IsSubquotient (Representation.tprod τ J) Y`
  implies `IsSubquotient J Y`.

  Proof. Let `U` be the subrepresentation and `f : U ↠ Y`. Since `Y` is
  irreducible its carrier is nonzero (`IsSimpleModule.nontrivial`). Consider the
  finite-dimensional subspaces `N ⊆ M` for which some `x ∈ U` lying in the range
  of `N ⊗ W` has `f x ≠ 0`. Such an `N` exists:
  `TensorProduct.exists_finite_submodule_left_of_setFinite` gives a
  finite-dimensional `N` containing the left factors of a preimage of a nonzero
  vector. Choose `N` of minimal `finrank` (`Nat.find`). Then `N ≠ ⊥`, because
  otherwise `x = 0`. Choose a nonzero `m ∈ N` and a functional `φ` with `φ m = 1`
  (`Module.Projective.exists_dual_eq_one`). The subspace `N ⊓ ker φ` is strictly
  smaller than `N`, so has smaller `finrank`. By minimality, `f` vanishes on every
  vector of `U` in the range of `(N ⊓ ker φ) ⊗ W`.

  Put `UN = U ⊓ leftSlice N` and let `c : UN → J` be the restricted contraction,
  with image the subrepresentation `R = c.range` of `J`. Let `c' : UN ↠ R` be its
  corestriction. If `c v = 0` for `v ∈ UN`, then
  `mem_range_of_trivialContraction_eq_zero` places `v` in the range of
  `(N ⊓ ker φ) ⊗ W`, so `f v = 0`. Thus `ker c' ≤ ker (f|UN)`, and
  `WeylBranchPieces.exists_descend` gives an intertwining map `d : R → Y` with
  `d ∘ c' = f|UN`. Then `d ≠ 0` because `x ∈ UN` and `f x ≠ 0`. Since `Y` is
  irreducible, `d` is surjective (`Representation.IsIrreducible.surjective_or_eq_zero`).
  So `(R, d)` exhibits `Y` as an actual subquotient of `J`.

### External tensor products (section `External`)

Here `ι` is a finite index type with decidable equality, `H i` are groups, and
`V i`, `W i` are complex vector spaces. `FiniteTensor.external ρ` is the published
external tensor product. It is a representation of `∀ i, H i` on
`PiTensorProduct ℂ V`, given by `FiniteTensor.action` of the coordinate pull-backs.

* `nontrivial_piTensorProduct`: a finite indexed tensor product of nonzero
  complex vector spaces is nonzero. A tensor product of bases
  (`Basis.piTensorProduct`) has a nonzero basis vector.
* `slotRestriction ρ k i`: the representation `(ρ i).comp (eval i ∘ mulSingle k)`
  of `H k` on `V i`. On `V k` it is `ρ k` (`slotRestriction_self`). For `i ≠ k`
  it is trivial. Hence, by `action_slotRestriction_compl`, the action of `H k` on
  the tensor product over the complement `{k}ᶜ` is the identity:
  `action (fun i : ({k}ᶜ : Set ι) => slotRestriction ρ k i) g = 1`. The proof uses
  `Pi.mulSingle_eq_of_ne` and `PiTensorProduct.map_id`.
* `isSubquotient_factor_of_external J ρ hρ h k`: let
  `J : ∀ i, Representation ℂ (H i) (W i)` and `ρ : ∀ i, Representation ℂ (H i) (V i)`,
  with every `ρ i` irreducible. If
  `h : IsSubquotient (external J) (external ρ)`, then
  `IsSubquotient (J k) (ρ k)` for every `k`.

  Proof. Pull `h` back along `MonoidHom.mulSingle H k`
  (`IsSubquotient.comp`). The pull-back of `external J` is definitionally
  `action (slotRestriction J k)`, and likewise for `ρ`. The published
  `FiniteTensor.slotEquiv` splits slot `k`:
  `action ψ ≃ tprod (action over {k}ᶜ) (ψ k)`. Apply it on both sides
  (`IsSubquotient.of_equiv_left`, `of_equiv_right`). The complementary carrier
  for `ρ` is nonzero by `nontrivial_piTensorProduct`, since irreducible
  representations have nonzero carriers. Choose a functional equal to `1` on a
  nonzero vector of it. Its `trivialContraction` maps the `ρ` side onto
  `slotRestriction ρ k k` (`trivialContraction_surjective`), using
  `action_slotRestriction_compl` for `ρ`. Composing with `IsSubquotient.trans`
  gives `IsSubquotient (tprod (action over {k}ᶜ of J) (slotRestriction J k k))
  (slotRestriction ρ k k)`. The complementary action for `J` is trivial
  (`action_slotRestriction_compl` for `J`), and `slotRestriction ρ k k = ρ k` is
  irreducible. So `isSubquotient_of_tprod_trivial` gives
  `IsSubquotient (slotRestriction J k k) (slotRestriction ρ k k)`. Rewrite with
  `slotRestriction_self` to finish.

## Dependencies

`Langlands.Representation.Exponents.WeylBranchPiecesSubquotient`
(`IsSubquotient` API, `exists_descend`, `subtypeMap`) and
`Langlands.Representation.Tensor.FiniteFiltration` (`FiniteTensor.action`,
`external`, `slotEquiv`). From Mathlib it uses
`TensorProduct.exists_finite_submodule_left_of_setFinite`,
`Module.Projective.exists_dual_eq_one`, `Basis.piTensorProduct`,
`Submodule.finrank_lt_finrank_of_lt`.
