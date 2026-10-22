# Proof that associated supercuspidal tensors have equal multisets of factors

Author: Worker 219.

`Langlands.CuspidalSupport.glCuspidalTensorAssociation` proves the published
proposition `Langlands.CuspidalSupport.GLCuspidalTensorAssociationStatement` in
`Langlands.Representation.CuspidalSupport.CuspidalTensorStatement`. The
theorem's type is exactly `GLCuspidalTensorAssociationStatement.{uV, uF}`, with
the carrier universe `uV` and the field universe `uF` kept independent. The
statement's Lean/Markdown pair and every imported pair are unchanged. The proof
adds no hypotheses, assumes no finite-dimensionality, and uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

The statement is the forward direction of Bernstein–Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), Example 2.7. If the
external tensor products of two families of supercuspidal block factors are
associated, the two families agree up to permutation. The source states this
without a detailed argument. The Lean proof below is self-contained. It reads
off a block bijection from the conjugating permutation matrix, compares
corresponding factors through the action of one block at a time, and then
counts.

Beyond the target statement, the module imports
`Langlands.Representation.Geometric.WeylUniquenessProof`, for
`Geometric.exists_index_of_blockIndex_eq`, and three Mathlib modules on bases of
tensor products. `Geometric.blockIndex_index` comes from the already imported
`WeylDefinitions`.

## Factor equivalence (section `FactorEquivalence`)

These lemmas hold for any field `K` and any groups. They are applied with
`K = ℂ`.

- `isIrreducible_comp_of_surjective`: if `ρ` is irreducible and `f : G →* H` is
  surjective, then `ρ.comp f` is irreducible. Both representations have the
  same invariant submodules (surjectivity gives one inclusion), so their
  subrepresentation lattices are order-isomorphic. The simple-order property
  then transfers.
- `nontrivial_of_isIrreducible`: an irreducible representation has a
  nontrivial carrier, since otherwise `⊥ = ⊤` among its subrepresentations.
- `equivComp`: an equivalence `ρ ≃ σ` of representations of `H` gives an
  equivalence `ρ.comp f ≃ σ.comp f` with the same linear equivalence.
- `exists_tprod_ne_zero`: if every factor `V i` is nontrivial, some pure tensor
  `tprod v` is nonzero. A pure tensor of basis vectors is a member of the
  product basis `Basis.piTensorProduct`.
- `exists_factor_contraction`: take a nonzero `x` in `⨂ j, W j` and an index
  `j₀`. Then there is a linear map `c : (⨂ j, W j) → W j₀` with `c x ≠ 0` such
  that, for every linear endomorphism `f` of `W j₀`, applying `f` to the
  `j₀`-th entry of a pure tensor before `c` is the same as applying `f` after
  `c`. To build `c`, split off the factor `j₀` with
  `PiTensorProduct.equivPiTensorComplSingletonTensor`, which gives
  `(⨂ j ≠ j₀, W j) ⊗ W j₀`. Next choose a basis of the left factor and identify
  this tensor product with finitely supported functions into `W j₀`
  (`TensorProduct.equivFinsuppOfBasisLeft`). Finally evaluate at a basis index
  where the image of `x` is nonzero.
- `external_mulSingle_tprod`: the external tensor action
  `FiniteTensor.external π` of `Pi.mulSingle i₀ g` on a pure tensor changes
  only the `i₀`-th entry, applying `π i₀ g` to it.
- `nonempty_equiv_of_factor_actions`: let a group `G` act on `⨂ i, V i` by
  `πV` and on `⨂ j, W j` by `πW`, with every `V i` nontrivial. On pure tensors,
  `πV g` changes only the entry `i₀`, through an irreducible `ρ`, and `πW g`
  changes only the entry `j₀`, through an irreducible `σ`. Then an
  equivalence `πV ≃ πW` gives an equivalence `ρ ≃ σ`. Proof: choose a nonzero
  pure tensor `tprod v` and let `e : V i₀ → ⨂ i, V i` send `u` to
  `tprod (update v i₀ u)`. This map intertwines `ρ` with `πV`. Since
  `E (tprod v) ≠ 0`, the previous lemma gives a contraction `c` onto `W j₀`
  with `c (E (tprod v)) ≠ 0`. Checking on pure tensors
  (`PiTensorProduct.ext`) shows that `c` intertwines `πW` with `σ`. So
  `c ∘ E ∘ e` is an intertwiner `ρ → σ`, and it is nonzero at `v i₀`. Schur's
  lemma `Representation.IsIrreducible.bijective_or_eq_zero` makes it
  bijective, hence an equivalence (`IntertwiningMap.ofBijective`).

## Blocks of a conjugating permutation (section `Blocks`)

Here `B` and `C` are block shapes of `n`, and `hw : ConjugatesLevi B C w` for a
permutation `w` of `Fin n`. The block structure is derived only from matrix
entries of embedded Levi elements.

- `leviEmbedding_eq_zero_of_blockIndex_ne`: an embedded Levi element has zero
  entries between coordinates in different blocks.
- `exists_leviEmbedding_ne_zero`: for two coordinates in one block, some Levi
  element has a nonzero entry at that position. Take the permutation matrix of
  the transposition of the two positions in that block, and the identity in
  the other blocks.
- `leviConjugation_symm_entry`: the entry `(a, b)` of
  `(leviConjugation B C w hw).symm m` embedded in `GL_n` equals the entry
  `(w a, w b)` of `m` embedded in `GL_n`. This follows from the Library's
  `leviConjugation_symm_embedding` and the entry formulas for products with
  permutation matrices.
- `blockIndex_eq_iff`: `w a` and `w b` lie in one block of `C` if and only if
  `a` and `b` lie in one block of `B`. Each direction combines the previous
  three lemmas. A nonzero entry on one side would face a forced zero entry on
  the other.
- `blockMap B C w i` is the `C`-block that contains the image under `w` of
  the first coordinate of block `i`. By `blockIndex_image`, it contains the
  image of every coordinate of block `i`. `blockImage_bijective` follows:
  injectivity from `blockIndex_eq_iff`, and surjectivity by applying `w⁻¹` to
  the first coordinate of a target block.
- `blockPosition hw i x` is the position of `w (B.index i x)` inside the block
  `blockMap B C w i` (`index_blockPosition`).
  `blockPosition_bijective` and `blockPositionEquiv` show that it is a
  bijection between the positions of block `i` and those of its image block.
  No order-preservation is claimed.
- `leviConjugation_symm_apply_entry`: the component of
  `(leviConjugation B C w hw).symm m` at block `i` has entry `(x, y)` equal to
  the entry `(blockPosition x, blockPosition y)` of the component of `m` at
  `blockMap B C w i`.
- `leviConjugation_symm_mulSingle_ne`: the inverse conjugation of an element
  supported in the block `blockMap B C w i` is trivial at every block other
  than `i`.
- `factorHom hw i : GL (C.size (blockMap B C w i)) →* GL (B.size i)` is the
  component at `i` of `(leviConjugation B C w hw).symm ∘ Pi.mulSingle`. Its
  entries are `factorHom hw i g x y = g (blockPosition x) (blockPosition y)`
  (`factorHom_apply_entry`). It is surjective (`factorHom_surjective`): the
  preimage of `h` is `reindex (blockPositionEquiv hw i) h`.
- `external_leviConjugation_symm_mulSingle`: under the transported external
  action, `Pi.mulSingle (blockMap B C w i) g` acts on a pure tensor by
  changing only the `i`-th entry, through `π i (factorHom hw i g)`.

## Equality of cuspidal data (section `Datum`)

- `nonempty_iso_of_equiv_comp_permuted`: let `A₁` and `A₂` be supercuspidal
  objects of `GL_r`, and let `φ : GL_r →* GL_r` satisfy
  `φ g x y = g (β x) (β y)` for a permutation `β`. Then an equivalence
  `A₁ ∘ φ ≃ A₂` gives an isomorphism `A₁ ≅ A₂`. The entry formula says that
  `φ g = P g P⁻¹` for the permutation matrix `P = permutation r F β⁻¹`
  (`permutation_conjugate_entry`). Therefore the composite `E ∘ A₁(P)` is an
  intertwiner `A₁ → A₂`. It is bijective because `A₁(P)` is invertible.
  `SmoothRep.mkIso` and `ObjectProperty.isoMk` turn it into an isomorphism of
  supercuspidal objects.
- `cuspidalDatum_eq_of_equiv`: let `A₁` and `A₂` be actual representatives of
  two cuspidal data. Suppose there are a bijection
  `β : Fin ρ₁.rank ≃ Fin ρ₂.rank`, a homomorphism `φ` with the entry formula
  above, and an equivalence `A₁ ∘ φ ≃ A₂`. Then the two data are equal. The
  bijection forces equal ranks (`Fin.equiv_iff_eq`). The previous lemma and
  `SupercuspidalRep.isoClass_eq_iff` then equate the two classes.

## Closing argument

Fix the prime, the p-adic field `F`, its topological data `T` (whose topology
is installed as the local instance), `n`, the two families `ρ : Fin k → _` and
`ρ' : Fin l → _` with their representatives `A` and `A'`, and the association.
The association provides `w`, `hw : ConjugatesLevi B C w` for the block shapes
`B = T.cuspidalShape ρ h` and `C = T.cuspidalShape ρ' h'`, and an equivalence
`E` from the transport of the external tensor of the `A i` to the external
tensor of the `A' j`. Every `(A i).obj` is irreducible, so its carrier is
nontrivial.

For each `i`, let `j = blockMap B C w i`. Restrict `E` along
`Pi.mulSingle j` (`equivComp`). On the source side, by
`external_leviConjugation_symm_mulSingle`, the restricted action changes only
factor `i`, through `(A i).obj.representation.comp (factorHom hw i)`. This is
irreducible by `isIrreducible_comp_of_surjective` and `factorHom_surjective`.
On the target side, by `external_mulSingle_tprod`, it changes only factor `j`,
through the irreducible `(A' j).obj.representation`.
`nonempty_equiv_of_factor_actions` gives an equivalence between these two
factor representations. Then `cuspidalDatum_eq_of_equiv`, with
`β = blockPositionEquiv hw i` and `φ = factorHom hw i`, gives
`ρ i = ρ' (blockMap B C w i)`. The irreducibility instances are passed
explicitly to `nonempty_equiv_of_factor_actions`, because instance search does
not identify `GL (C.size j)` with `GL (ρ' j).rank` through the definition of
`cuspidalShape`.

Finally, let `τ : Fin k ≃ Fin l` be the bijection `blockMap B C w`. Then
`ρ = ρ' ∘ τ`. Writing `List.ofFn ρ` as a multiset is
`Finset.univ.val.map ρ` (`Fin.univ_val_map`). `Multiset.map_map` and
`Multiset.map_univ_val_equiv` then show that the two multisets are equal. This
is equality in `Multiset CuspidalDatum`, so ranks, isomorphism classes and
multiplicities are all retained.

The block-label map is imported from the shared `BlockMap` module. Its
definition is unchanged from this proof's original `blockImage`.
