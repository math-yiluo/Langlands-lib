# The factor hypotheses of the merged-slot Jacquet filtration

Author: Worker 890.

The published statement
`Langlands.Classification.SegmentEdgeJacquetFiltration.{uF,uV,uW} F T`
(module `SegmentEdgeJacquetStatement`) has two hypotheses on the factors `Y j`
of the merged shape `γ = β.adjacentMerge k hk`, where
`β = BlockShape.uniform m r hr`, `S = β.adjacentRefinement k hk` and
`e = β.adjacentBlockEquiv k hk`:

- (H1) for every `j` and every shape `D` of rank `γ.size j` with
  `1 < D.length` and `D ≠ S j`, the normalized Jacquet module of `Y j` along `D`
  is zero (`Subsingleton`);
- (H2) for every `j`, the normalized Jacquet module of `Y j` along `S j` is
  equivalent to the external tensor product of `t ↦ σ (e ⟨j, t⟩)`.

This module proves these hypotheses for the factors used in the proof of
Zelevinsky 1980, 3.1 and 9.1(*): the slot products
`Y₀ j = i_{S j}(σ (e ⟨j, 0⟩), …)` and, at the merged slot, an invariant subspace
of `Y₀` or the quotient by it. **It does not prove the geometric lemma**: all
(H1) results take `GeometricLemmaTheorem` or `PadicGeometricLemmaTheorem` as an
explicit hypothesis. The merged-slot results take the published statements
`TwoSupercuspidalAdjacentProductComposition` and
`TwoSupercuspidalAdjacentProductJacquet` (Ze80 Proposition 1.11(b), module
`TwoSupercuspidalProductStructureStatement`) as explicit hypotheses and transport
them from the standard shape `(r, r)` to the merged slot.

All declarations live in the namespace `Langlands.Classification.SegmentEdge`.
Provenance is internal. The vanishing argument is a derived consequence of the
geometric lemma (BZ77 2.12, printed p.448; Ze80 1.2–1.3, printed pp.170–171):
the Jacquet module along `C` of a representation induced from cuspidal data on
the Levi of `B` is glued from pieces, and each piece is zero unless its source
refinement is trivial, which needs a refinement of `C` whose Levi is conjugate to
the Levi of `B`. The combinatorial fact that such a refinement forces `C = B`
for a shape `B` with equal block sizes and `B.length ≤ C.length` is proved
here. The shape transport and the one-block identification have no counterpart
in the sources; they are bookkeeping in this formalization.

## Section `Vanishing`

- `refinedLevi_map_eq_flatten_leviSubgroup`: the image of `refinedLevi K D S`
  in `GL_n` is the Levi subgroup of the flattened shape `D.flatten S`. It uses
  the published `flattenedLeviEquiv_embedding` and its inverse form.
- `eq_of_conjugatesLevi_flatten`: if all blocks of `B` have the same size,
  `B.length ≤ D.length` and `ConjugatesLevi B (D.flatten S) w`, then `D = B`.
  Proof: `TotalConjugatingCount.length_eq` gives
  `B.length = ∑ i, (S i).length`. Each summand is at least `1`, so
  `D.length = B.length` and every `S i` has one block. Each block of the
  flattening has a size of `B` (`blockMap_surjective`, `size_blockMap`), and the
  one block of `S i` has size `D.size i`. So all sizes agree and
  `TotalConjugatingCount.shape_ext` gives `D = B`.
- `no_associated_refinement_of_size_eq`: the same hypotheses on `B`, and
  `D ≠ B`, exclude every refinement `S` of `D` and permutation `w` with
  `w (Levi B) w⁻¹ = (refinedLevi D S).map D.leviEmbedding`.
- `jacquet_induction_subsingleton_of_geometricLemma`: given
  `GeometricLemmaTheorem T B C` and a representation `ρ` of the Levi of `B`
  satisfying `IsLeviQuasicuspidal`, if no refinement of `C` has a Levi conjugate
  to the Levi of `B`, then the normalized Jacquet module along `C` of the
  normalized induction from `B` of `ρ` is zero. Evaluating the geometric-lemma
  filtration at `ρ` (`objectFiltrationAt`) gives graded quotients isomorphic to
  geometric pieces. Every piece is zero by the published
  `geometricPieceFunctor_subsingleton_of_proper_source`, whose properness
  hypothesis comes from `source_refinement_proper_of_no_associated_refinement`.
  Then `objectRepFiltrationSubsingleton` gives the conclusion.
- `induced_jacquet_subsingleton`: for `0 < n`, a shape `B` whose blocks all have
  the same size, the geometric lemma for `(B, D)` for every `D`, and
  supercuspidal factors `A i`, the normalized Jacquet module of
  `i_B(A)` along every `D` with `B.length ≤ D.length` and `D ≠ B` is zero. The
  external tensor product of the `A i` is quasicuspidal by the published
  `glCuspidalTensor`.
- `subquotient_jacquet_subsingleton`: the same vanishing for every subquotient
  `Z` of `i_B(A)`, since the normalized Jacquet module of a subquotient is a
  subquotient (`normalizedJacquetSubquotient`, `subsingleton_of_isSubquotient`).

## Section `OneBlock`

- `singleBlockInducedJacquetEquiv`: for a shape `B` with one block and a family
  `τ` on that block, the normalized Jacquet module along `B` of
  `i_B(τ)` is equivalent to the external tensor product of `τ`. It composes the
  inverse of `T.singleBlockNormalizedJacquetEquiv` with
  `T.singleBlockNormalizedInducedEquiv` pulled back along `B.leviEmbedding`.
  The intertwining condition is corrected with
  `(B.singleBlockLeviEquiv hB).symm_apply_apply`.

## Section `Transport`

- `shape_family_transport`: a property `Q n C τ υ` of a rank, a shape and two
  factor families on it passes from `(a, B, τ, υ)` to `(b, B', τ', υ')` when
  `a = b` and `B`, `B'`, the `τ` and the `υ` are heterogeneously equal (`HEq`).
  The proof substitutes the equalities.
- `heq_rankCast`: a shape is heterogeneously equal to its `rankCast`.

## Section `Slots`

Fix `hr : 0 < r` and `hk : k + 1 < β.length`, and let `kk` be the merged index
`β.adjacentMergeIndex k hk`.

- `slotProduct T hr k hk σ j` (abbreviation): the normalized product induction
  over `S j` of `t ↦ σ (e ⟨j, t⟩)`, a representation of `GL_{γ.size j}(F)` in
  universe `max uF uV`. No rank cast is used.
- `swappedFactors T hr k hk σ` (abbreviation): the family `σ'` with
  `σ' i = σ (swap ⟨k, _⟩ ⟨k + 1, hk⟩ i)`, that is, blocks `k` and `k + 1`
  exchanged.
- `slot_length_le`: every slot refinement `S j` has at most two blocks, so
  `(S j).length ≤ D.length` whenever `1 < D.length`.
- (H1) `slot_subquotient_jacquet_subsingleton`, `slot_jacquet_subsingleton`,
  `slot_subrepresentation_jacquet_subsingleton` and
  `slot_quotient_jacquet_subsingleton`: given
  `hgeo : PadicGeometricLemmaTheorem.{uF, uV}` and
  `hσ : ∀ i, (σ i).IsIrreducible ∧ IsSupercuspidal (σ i).representation`, for
  every slot `j`, every `D` with `1 < D.length` and `D ≠ S j`, the normalized
  Jacquet module along `D` is zero for, respectively, every subquotient of
  `slotProduct T hr k hk σ j`, the slot product itself,
  `SmoothRep.subrepresentation (slotProduct …) W` and
  `SmoothRep.quotient (slotProduct …) W` for every invariant subspace `W`. These
  apply `subquotient_jacquet_subsingleton` and `induced_jacquet_subsingleton` to
  `S j`, whose blocks all have size `r` (by `rfl`).
- (H2) away from the merged slot, `slot_jacquet_equiv_of_ne` (for
  `j.val ≠ k`): the normalized Jacquet module of the slot product along `S j` is
  equivalent to the external tensor product of `t ↦ σ (e ⟨j, t⟩)`, by
  `singleBlockInducedJacquetEquiv` and
  `adjacentRefinement_length_of_ne`. `swappedFactors_slot_of_ne` shows that the
  exchanged factors agree with `σ` on such a slot (its only block is neither `k`
  nor `k + 1`), and `slot_jacquet_equiv_swapped_of_ne` is the same (H2) against
  `σ'`.
- `merged_size` (`r + r = γ.size kk`), `merged_refinement_heq`
  (`Shahidi.twoBlocks r r hr hr` is heterogeneously equal to `S kk`; both have
  sizes `![r, r]`), `merged_blockEquiv_val` (`(e ⟨kk, t⟩).val = k + t.val`),
  `merged_factors_heq` and `merged_swappedFactors_heq`: if `σ ⟨k, _⟩ = ρ` and
  `σ ⟨k + 1, hk⟩ = ρ'`, then `twoBlockFactors hr hr ρ ρ'` is heterogeneously
  equal to the merged-slot factors `t ↦ σ (e ⟨kk, t⟩)`, and
  `twoBlockFactors hr hr ρ' ρ` to the exchanged ones `t ↦ σ' (e ⟨kk, t⟩)`.
- `merged_composition`: given `TwoSupercuspidalAdjacentProductComposition F T`,
  supercuspidal `ρ ρ' : SupercuspidalRep (n := r)` with `σ ⟨k, _⟩ = ρ.obj`,
  `σ ⟨k + 1, hk⟩ = ρ'.obj` and
  `ρ'.isoClass = T.supercuspidalClassRealPowerTwist r 1 ρ.isoClass ∨
  ρ.isoClass = T.supercuspidalClassRealPowerTwist r 1 ρ'.isoClass` (Ze80's
  `ρ' ≅ νρ` or `ρ ≅ νρ'`), the merged slot product `P = slotProduct … kk` has
  composition length two, exactly one invariant subspace other than `⊥` and
  `⊤`, and for every such subspace `W` both `SmoothRep.subrepresentation P W`
  and `SmoothRep.quotient P W` are irreducible. This is the composition clause
  of Ze80 1.11(b) for `ρ × ρ'`, transported by `shape_family_transport`.
- `merged_jacquet_equiv`: given `TwoSupercuspidalAdjacentProductJacquet F T` and
  the same `ρ`, `ρ'`, for every invariant subspace `W` of `P` other than `⊥` and
  `⊤`, the normalized Jacquet module along `S kk` of
  `SmoothRep.subrepresentation P W` is equivalent to the external tensor product
  of `t ↦ σ (e ⟨kk, t⟩)`, and that of `SmoothRep.quotient P W` to the external
  tensor product of `t ↦ σ' (e ⟨kk, t⟩)`. This is the Jacquet clause of Ze80
  1.11(b) (`r(ω) = ρ ⊗ ρ'`, `r(ω') = ρ' ⊗ ρ`), transported to the merged slot.

So, for the factors `Y j = slotProduct … j` for `j ≠ kk` and `Y kk` a
subrepresentation (respectively quotient) of `slotProduct … kk` by such a `W`,
(H1) holds for all slots, and (H2) holds against `σ` (respectively against
`σ'`). The hypotheses of `SegmentEdgeJacquetFiltration` are then met with
`uW = max uF uV`.

## Technical options

The module sets `backward.isDefEq.respectTransparency.types false`, as do the
published `SegmentEdgeJacquetReduction` and
`AssociatedGeometricPiecesEquivalenceProof`.

## Sources

- Zelevinsky 1980 (`zelevinsky-1980-induced-ii`), 1.2–1.3 (printed pp.170–171,
  PDF pages 7–8) and Proposition 1.11 (printed p.175, PDF page 12).
- Bernstein–Zelevinsky 1977 (`bernstein-zelevinsky-1977-induced-i`), Lemma
  2.12 (printed p.448, PDF page 9).
