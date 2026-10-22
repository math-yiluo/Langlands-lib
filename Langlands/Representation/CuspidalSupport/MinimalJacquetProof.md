# Proof of nonzero quasicuspidal Jacquet descent

Authors: Worker 203 and Worker 276.

`Langlands.CuspidalSupport.minimalNonzeroJacquet` proves the published
proposition `Langlands.CuspidalSupport.MinimalNonzeroJacquetTheorem` in
`Langlands.Representation.CuspidalSupport.MinimalJacquetStatement`. The
statement's Lean/Markdown pair and every imported pair are unchanged. The
theorem's type is exactly `MinimalNonzeroJacquetTheorem.{uF, uV}`, with the
field universe `uF` and the representation carrier universe `uV` kept
independent. The proof covers every prime, every actual p-adic field, every
compatible `T : F.TopologicalData`, every rank `n` (including `n = 0`) and
every nonzero smooth input. It adds no hypotheses: no irreducibility,
admissibility, finite length or finite generation. It uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

The module imports the statement module, the published
`Langlands.Representation.Parabolic.RefinementComposition` (the subgroups
`leviPreimage` and `composedUnipotent`) and `Langlands.Group.GL.SingleBlock`
(`singleBlock_parabolic_eq_top`). It does not use the transitivity statement
`NormalizedRefinementJacquetTransitivityClause`, cuspidal-induction finite
length, or association results. All coordinate, whole-group and descent
steps are proved here.

## Route

The source picks a standard Levi that is minimal among those with nonzero
Jacquet module, and then uses the transitivity isomorphism. The Lean proof
uses a different route with less machinery. Among all block shapes `B` of
`n` with a nonzero Jacquet module, it takes one with the largest number of
blocks. The block count is bounded by `n`. If some proper refinement `S` of
`B` had nonzero inner coinvariants, then the *flattened* shape `B.flatten S`
would have strictly more blocks. A surjection would then make its Jacquet
module nonzero too, which contradicts maximality. Only this surjection is
needed, not a full transitivity isomorphism.

## Ordering lemmas (namespace `Langlands.GeneralLinear.BlockShape`)

- `finSigmaFinEquiv_lt_of` and `finSigmaFinEquiv_lt_iff`: Mathlib's
  consecutive numbering `finSigmaFinEquiv` of `(i : Fin m) × Fin (L i)`
  increases exactly in lexicographic order: first by `i`, then by the inner
  index. The forward direction compares the offset sums
  `∑_{k < i} L k + a`. The backward direction follows by trichotomy.
- `index_lt_iff`: for a block shape `B`, the coordinate `B.index i a` lies
  before `B.index j b` exactly when `i < j`, or when `i = j` and `a < b`.
  This holds because `B.indexEquiv` is `finSigmaFinEquiv` followed by a
  cast.
- `length_le`: `B.length ≤ n`, because each block has positive size and the
  sizes sum to `n`.

## The flattened shape

For `S : BlockRefinement B` (a block shape `S i` of each block size
`B.size i`), `flatten B S` is the block shape of `n` with
`∑ i, (S i).length` blocks. Its block number `finSigmaFinEquiv ⟨i, j⟩` has
size `(S i).size j`. So it lists the blocks of `S 0`, then those of `S 1`,
and so on. Its sizes sum to `n` by `Fintype.sum_sigma'` and the sum
conditions of `S i` and `B`. The block numbering `flattenBlockEquiv` is
`finSigmaFinEquiv`. `flattenBlockEquiv_lt_iff` restates its lexicographic
order, and `flatten_size_flattenBlockEquiv` gives its sizes.

Coordinate identification:

- `index_index_lt`: the composite coordinates
  `B.index i ((S i).index j c)` increase lexicographically in `(i, j, c)`.
  This follows from `index_lt_iff` for `B` and for `S i`.
- `flatten_index`: the coordinate `c` of flattened block `k` is
  `B.index i ((S i).index j c)` with `⟨i, j⟩ = flattenBlockEquiv.symm k`.
  Both sides are numberings of the same index type. The composite numbering
  `φ` preserves the strict order of the flattened numbering `f`, so
  `φ ∘ f.symm` is a strictly monotone self-map of `Fin n`. Such a map is the
  identity, by `StrictMono.apply_le` and `StrictMono.le_apply`.
- `index_index_eq_flatten`: the same identity, read from a pair `⟨i, j⟩`,
  with the evident cast of the inner coordinate.

Counting blocks:

- `one_le_refinement_length`: every `S i` has at least one block, since the
  block size `B.size i` is positive.
- `length_lt_flatten`: if `refinedParabolic R B S ≠ ⊤`, then
  `B.length < (B.flatten S).length`. Suppose instead every `S i` had exactly
  one block. Then `singleBlock_parabolic_eq_top` would make every
  `(S i).parabolic R` the whole group, and `Subgroup.pi_top` would make the
  refined parabolic `⊤`. So some `S i` has at least two blocks, and the sum
  of the lengths is strictly larger.

Radical inclusion:

- `flatten_unipotentSubgroup_le`: `(B.flatten S).unipotentSubgroup R` lies
  in `Parabolic.composedUnipotent R B S`, which is the preimage under the
  `B`-Levi projection of `refinedUnipotent R B S`. Take `g` in the
  flattened radical. An entry whose row lies in outer block `i` and whose
  column lies in an earlier outer block `i' < i` lies strictly below the
  flattened block diagonal (`index_index_eq_flatten` and
  `flattenBlockEquiv_lt_iff`), so it vanishes. Hence `g ∈ B.parabolic R`. The `i`-th diagonal block of `g`
  (`leviProjection_apply`) has zero entries below the `S i` block diagonal,
  for the same reason. On each `S i` diagonal block it agrees with the
  identity, because the flattened diagonal blocks of `g` are identities. So
  each component lies in `(S i).unipotentSubgroup R`.

## Shapes with at most one block

- `exists_length_le_one`: every rank has a shape with at most one block. At
  rank zero this is the empty shape; at positive rank it is the single
  block of size `n`.
- `unipotentRadical_val_eq_one`: if `B.length ≤ 1`, every element of the
  unipotent radical is the identity matrix. All coordinates lie in the same
  block, and the radical is the identity on diagonal blocks. At rank zero
  this holds trivially.
- `jacquetMk_injective_of_length_le_one`: so the Jacquet relations
  `ρ u v - v` all vanish (`Jacquet.relations_eq_span`), and the quotient map
  `B.jacquetMk ρ` has zero kernel (`Jacquet.ker_mk`).
- `nontrivial_jacquetModule_of_length_le_one`: for nonzero `V`, the Jacquet
  module of such a shape is therefore nonzero.

This proves the whole-group identification needed at the start of the
descent, including the empty shape at rank zero.

## The surjection (namespace `Langlands.CuspidalSupport.MinimalJacquet`)

Fix `T`, `B`, `S` and `ρ`.

- `mk_jacquetMk_composedUnipotent`: for `g ∈ composedUnipotent F B S` and
  `v`, the inner-coinvariant class of `B.jacquetMk ρ (ρ g v)` equals that of
  `B.jacquetMk ρ v`. Write `g = u · leviEmbedding m` with `u` in the radical
  of `B` (`unipotentPart`) and `m` its Levi projection, which lies in
  `refinedUnipotent F B S`. The factor `u` acts trivially on the outer
  Jacquet module (`Jacquet.mk_apply_subgroup`). By
  `normalizedJacquet_mk_eq_inv_halfModulus`, the normalized action of `m` is
  `leviHalfModulus B m⁻¹` times the action of `leviEmbedding m`. The
  published `leviHalfModulus_refinedUnipotent` makes this scalar `1`. So
  `ρ (leviEmbedding m)` acts as the normalized action of an element of the
  inner radical. Such an element acts trivially on the inner coinvariants
  (`Jacquet.mk_apply_subgroup` again).
- `flattenJacquetMap`: by `flatten_unipotentSubgroup_le`, this gives a
  linear map (`Jacquet.lift`) from `(B.flatten S).JacquetModule ρ` to
  `Jacquet.Coinvariants (T.normalizedJacquet B ρ) (refinedUnipotent F B S)`.
  It sends the class of `v` to the inner class of the outer class of `v`.
- `flattenJacquetMap_surjective`: it is surjective, because both quotient
  maps `Jacquet.mk_surjective` and `B.jacquetMk_surjective` are.
- `nontrivial_flatten`: so nonzero inner coinvariants give a nonzero
  flattened Jacquet module (`Function.Surjective.nontrivial`).

## Closing argument

Install `T.topology` and `T.generalLinearTopology n`, and let
`ρ = A.representation`. Let `P k` say that some shape of length `k` has a
nonzero Jacquet module of `ρ`. By `exists_length_le_one` and
`nontrivial_jacquetModule_of_length_le_one`, `P` holds at some length, and
all lengths are at most `n` (`length_le`). `Nat.findGreatest_spec` gives a
shape `B` with nonzero Jacquet module of length `Nat.findGreatest P n`. The
carrier of `(T.normalizedJacquetFunctor B).obj A` is
`B.JacquetModule A.representation`, and its representation is
`T.normalizedJacquet B ρ`. So the first conjunct holds. For quasicuspidality,
let `S` be a refinement with proper refined parabolic, and suppose its inner
coinvariants were not a subsingleton, hence nontrivial. Then
`nontrivial_flatten` makes `(B.flatten S).JacquetModule ρ` nonzero, and
`length_lt_flatten` makes its length larger than `Nat.findGreatest P n`. Its
length is at most `n`. This contradicts `Nat.findGreatest_is_greatest`.

## Relation to the source

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups. I*, Ann. Sci. ENS (4) 10 (1977), 441–472 (registered source
`bernstein-zelevinsky-1977-induced-i`). Section 2.14(1), printed p.449 / PDF
p.10, asserts for a connected reductive group `G` that every nonzero
`π₀ ∈ Alg G` has a standard `L < G` with `r_{L,G}(π₀)` quasicuspidal and
nonzero, citing the transitivity 2.3(c) (printed p.446 / PDF p.7). The
Jacquet functor `r` is normalized by `mod_U^{-1/2}` (1.8(b), printed p.444 /
PDF p.5). Quasicuspidality is the vanishing of all proper standard Jacquet
modules (2.4). For `GL_n`, standard Levis are given by ordered partitions of
`n` (2.2).

For positive rank, the theorem specializes this source claim to `GL_n` over
the Library's p-adic fields, with block shapes as ordered partitions. The
source does not treat `GL_0`. The rank-zero case is a derived extension
under the Library's conventions. There the empty shape has length `0`, its
radical is trivial, so its Jacquet module is nonzero, and `n` bounds the
block count. The Lean proof does not treat this case separately: the
same descent argument applies, with `n = 0` bounding the block count. The
implemented proof replaces the source's
minimal-Levi choice and transitivity isomorphism by a maximal block count
and the one-directional surjection above.
