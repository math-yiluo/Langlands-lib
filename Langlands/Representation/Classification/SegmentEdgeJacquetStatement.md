# Uniform Jacquet modules of an induction with one merged adjacent slot

Author: Worker 890.

`Langlands.Classification.SegmentEdgeJacquetFiltration.{uF,uV,uW} F T` is a
proposition definition. **This contribution does not prove it.** It states a
special case of the geometric lemma of Bernstein–Zelevinsky (Zelevinsky 1980,
1.2–1.3, quoting BZ77 Lemma 2.12). The special case is induction from a block
shape `γ` obtained by merging two adjacent blocks of `β = (r, …, r)`, followed
by the Jacquet functor along `β`. The pieces that vanish under two explicit
hypotheses on the factors are deleted. The file adds no helper definitions and
assumes no theorem as data. Provenance is *derived*; see the last section.

## The statement

Fix a prime `p`, a p-adic field `F : PadicField.{uF} p` and topological data
`T : F.TopologicalData`. Everything is read under `letI := T.topology`. The
universes `uF` (field), `uV` (factors `σ_i`) and `uW` (factors `Y_j`) are
independent.

The statement quantifies over:

- natural numbers `m`, `r` with `hr : 0 < r`, and `k` with
  `hk : k + 1 < m` (written as `k + 1 < (BlockShape.uniform m r hr).length`,
  which is `m` by definition);
- a family `σ i : SmoothRep.{0,uF,uV} ℂ (GL_r(F))` for `i : Fin m` (the size
  of every block of the uniform shape is `r`);
- a family `Y j : SmoothRep.{0,uF,uW} ℂ (GL_{γ.size j}(F))` for
  `j : Fin (m - 1)`, one factor for each block of `γ`.

Notation, all from `Langlands.Group.GL.AdjacentMergeShape`:

- `β = BlockShape.uniform m r hr`, the shape `(r, …, r)` of `GL_{mr}`;
- `γ = β.adjacentMerge k hk`, the shape `(r, …, r, 2r, r, …, r)` with `m - 1`
  blocks, in which blocks `k` and `k + 1` of `β` form the single block `k`;
- `S = β.adjacentRefinement k hk`, the refinement of `γ` splitting each block
  `j` of `γ` into the blocks of `β` it contains: `S k = (r, r)` and
  `S j = (r)` (one block) for `j ≠ k`;
- `β.adjacentBlockEquiv k hk : (Σ j, Fin (S j).length) ≃ Fin m`, the
  lexicographic bijection between pairs (block `j` of `γ`, inner block `t`) and
  blocks of `β`.

**Hypotheses.**

- (H1) For every block `j` of `γ` and every block shape `D` of `γ.size j` with
  at least two blocks and `D ≠ S j`, the normalized Jacquet module
  `(T.normalizedJacquetFunctor D).obj (Y j)` is a subsingleton (zero).
- (H2) For every block `j` of `γ`, the normalized Jacquet module of `Y j` along
  `S j` is equivalent (`Representation.Equiv`) to the external tensor product
  `⊠_t σ (β.adjacentBlockEquiv k hk ⟨j, t⟩)` of the factors of the blocks of `β`
  inside block `j`.

For `j ≠ k` the shape `S j` has one block, so (H1) says that `Y j` has no
nonzero proper Jacquet module (it is quasicuspidal) and (H2) says that `Y j`
is equivalent to `σ` of the corresponding block of `β`. For `j = k`, (H1)
says that the only possibly nonzero proper Jacquet module of `Y k` is the one
along `(r, r)`, and (H2) says that it is `σ_k ⊠ σ_(k+1)`. Neither hypothesis
requires any factor to be nonzero: zero families `σ` and `Y` satisfy both, and
then every successive quotient below is zero.

**Conclusion.** Let `Π = (T.normalizedProductInductionFunctor γ).obj Y`, the
normalized parabolic induction `i_γ(Y_0 ⊗ ⋯ ⊗ Y_(m-2))` from the standard upper
block parabolic of `γ`. There exist

- a natural number `N`;
- a bijection `e` from `Fin N` onto the set of
  `v : MinimalConjugatingPermutations β β` such that
  `IsMinimalRepresentative γ β v`;
- a finite filtration `s : ObjectRepFiltration` of length `N` of the normalized
  Jacquet module `(T.normalizedJacquetFunctor β).obj Π`,

such that, for each `i : Fin N`, the `i`th successive quotient
`s.gradedRepresentation i` (the `(i+1)`st step modulo the `i`th) is equivalent to
`transport β β v hv (⊠_i σ_i)` with `v = e i`. Here
`FiniteTensor.externalSmoothObject σ` is the external tensor product of the
`σ_i`, a representation of `β.Levi F = ∏_i GL_r(F)`.

### The objects used

- `MinimalConjugatingPermutations β β` (`CuspidalSupport/LeviDefinitions`):
  permutations `w` of `{0, …, mr - 1}` that are minimal for `(β, β)`
  (`IsMinimalRepresentative β β w`: increasing on each block of `β`, and `w⁻¹`
  increasing on each block of `β`) and conjugate the Levi of `β` onto itself
  (`ConjugatesLevi`). Such a `w` permutes the `m` blocks of `β` as wholes,
  keeping the order inside each block.
- `IsMinimalRepresentative γ β w` (`Geometric/WeylDefinitions`): `w` is
  increasing on each block of `γ` and `w⁻¹` is increasing on each block of `β`.
  For `w` as above this adds one condition: `w` keeps the order of the two
  `β`-blocks `k` and `k + 1` (it is increasing on the merged block). Exactly
  half of the `m!` block permutations satisfy it.
- `transport β β w hw ρ` (`CuspidalSupport/LeviDefinitions`): the Weyl
  transport of a representation of `β.Levi F`, acting through the inverse of
  conjugation by `w` (BZ77 1.7). For a block permutation this permutes the
  tensor factors.
- `ObjectRepFiltration` (`Filtration/ObjectDefinitions`): a chain of invariant
  subspaces from `⊥` to `⊤`, with `gradedRepresentation i` the actual quotient of
  step `i + 1` by step `i`.

The statement does not specify the order of the pieces in the filtration; only
the multiset of successive quotients, indexed through `e`, is asserted.

## Intended use

This is the input (E) for the proof of
`Langlands.Classification.SegmentFullJacquetFormula` (Ze80 3.1 and 9.1(*)),
task `b331611c-526d-4925-87fe-ea67ed6e6fed`. There `Y_k` is a two-block
subrepresentation or quotient of `i(ρ_k, ρ_(k+1))` given by Ze80 1.11 or 2.9 and
the other `Y_j` are the cuspidal factors. The two cases differ:

- If `Y_k` is a subrepresentation of `i(σ_k, σ_(k+1))` with `(r, r)` Jacquet
  module `σ_k ⊠ σ_(k+1)`, then `i_γ(Y)` is a subrepresentation of `i_β(σ)`
  (exactness and transitivity of induction), and (E) applies to `σ` itself.
- If `Y_k` is a quotient of `i(σ_k, σ_(k+1))` whose `(r, r)` Jacquet module is
  `σ_(k+1) ⊠ σ_k`, then `i_γ(Y)` is a quotient (not in general a
  subrepresentation) of `i_β(σ)`, and (E) is applied to the family
  `σ ∘ swap(k, k + 1)`, for which (H2) holds. For example, with `m = 2`, `r = 1`
  and `σ = (1, ν)`, Ze80 1.11(b) shows that the quotient of `1 × ν` does not
  embed in `1 × ν`. Applying (E) to the swapped family computes the Jacquet
  module of `i_γ(Y)`; it does not by itself give any embedding of `i_γ(Y)`
  into an induction.

The statement (E) itself asserts only the filtration of the Jacquet module of
`i_γ(Y)`; it makes no claim about how `i_γ(Y)` sits inside `i_β(σ)`.

## Provenance (derived)

Zelevinsky 1980 (`zelevinsky-1980-induced-ii`), 1.2 (printed p.170, PDF page 7),
states: "the functor `F = r_{γ,(n)} ∘ i_{(n),β} : Alg G_β → Alg G_γ` is glued
together from the `F_w`, where `w ∈ W^{β,γ}`". Here `F_w = i_{γ,γ'} ∘ w ∘ r_{β',β}`
with `β' = β ∩ w⁻¹(γ)` and `γ' = w(β) ∩ γ`, and "this is a particular case of
Lemma 2.12 from [1]" (BZ77, `bernstein-zelevinsky-1977-induced-i`). Ze80 1.3
(PDF page 8) makes "glued" precise: for an ordering `w_1, …, w_k` of
`W^{β,γ}`, `F(ρ)` has a filtration `0 = τ_0 ⊂ ⋯ ⊂ τ_k = F(ρ)` with
`τ_i / τ_(i-1) ≅ F_{w_i}(ρ)`. Ze80 1.5(a) splits the Jacquet functor of an
external tensor product into the tensor product of the Jacquet functors of the
factors.

The statement is that theorem with Zelevinsky's `β` and `γ` played by our `γ`
(induction) and `β` (Jacquet module). Under (H1) and (H2) it is derived as follows.

1. For `w` minimal for `(γ, β)`, the shape `γ' = γ ∩ w⁻¹(β)` restricts on block
   `j` of `γ` to a shape `γ'_j`. By Ze80 1.5(a), the Jacquet module of
   `Y_0 ⊗ ⋯ ⊗ Y_(m-2)` along `γ'` is the tensor product of the Jacquet modules
   of the `Y_j` along `γ'_j`.
2. If some `γ'_j` has at least two blocks and differs from `S j`, (H1) makes
   the piece `F_w` zero.
3. The merged block `k` of `γ` has `2r` indices. Their images under `w` are
   spread over blocks of `β` of size `r`, so `γ'_k` has at least two blocks
   and must equal `S k = (r, r)`. Every other `γ'_j` with `j ≠ k` must equal
   `S j`, since it is the one-block shape or would vanish by step 2. So `γ'`
   is the shape `β`. Hence `w` maps each block of `β` onto a whole block of `β`
   in increasing order, `w(β) ∩ β = β`, and the outer induction in `F_w` is the
   identity.
4. Such `w` are exactly the `v` in `MinimalConjugatingPermutations β β` with
   `IsMinimalRepresentative γ β v`. For them, (H2) and Ze80 1.5(a) give
   `F_w(Y) ≅ w(σ_0 ⊗ ⋯ ⊗ σ_(m-1))`, the transport of `⊠ σ`.
5. Deleting from the filtration of Ze80 1.3 the pieces `F_w` with `w` outside
   the retained set (those made zero by (H1) in step 2) leaves a filtration
   indexed by the retained `w`, with the stated successive quotients. The
   retained pieces are kept even when they are zero (for instance when some
   `σ_i` is zero), so the index set is exactly the retained permutations.

Normalization. Ze80 1.1 uses the functors of BZ77 2.3 (printed p.446, PDF
page 7), `i_{G,M} = i_{U,1}` and `r_{M,G} = r_{U,1}`. These are normalized by
`mod_U^{1/2}` (BZ77 1.8, PDF page 5), as are the Library's
`T.normalizedProductInductionFunctor` and `T.normalizedJacquetFunctor`. BZ77 6.4
(printed pp.468–469) proves the geometric lemma for these normalized functors and
shows that the comparison character `ε` is trivial, so no modulus twist appears
in `F_w`. The geometric lemma itself is BZ77 2.12 (printed p.448, PDF page 9).
