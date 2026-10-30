# The factor hypotheses for a slot family with one updated merged slot

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
  equivalent to the external tensor product of `t ↦ σ' (e ⟨j, t⟩)` for given
  block factors `σ'`.

This module names (H1) and (H2) as two propositions, `FamilyJacquetVanishing`
and `FamilyJacquetEquiv`. The published module `SegmentEdgeFactorHypotheses`
proves these hypotheses slot by slot for the slot products
`Y₀ = slotProduct T hr k hk σ` and for subrepresentations and quotients of the
merged slot `kk = β.adjacentMergeIndex k hk`. This module combines those
results into the two propositions for the two families used in the proof of
Zelevinsky 1980, 3.1 and 9.1(*):

- `Y_L = Function.update Y₀ kk (SmoothRep.quotient (Y₀ kk) W)`, with
  `σ' = swappedFactors T hr k hk σ` (blocks `k` and `k + 1` of `σ` exchanged);
- `Y_W = Function.update Y₀ kk (SmoothRep.subrepresentation (Y₀ kk) W)`, with
  `σ' = σ`.

Here `W` is an invariant subspace of `Y₀ kk`. For (H2) it must be other than
`⊥` and `⊤`. Finally, for the factors `σ = T.segmentFactors A.obj m hr` of a
segment of a supercuspidal `A`, the module produces such a `W` and both
hypotheses for both families.

**Nothing here proves the geometric lemma, Ze80 1.11, or
`SegmentEdgeJacquetFiltration`.** Every result takes the ones it uses as explicit
hypotheses:

- `hgeo : PadicGeometricLemmaTheorem.{uF, uV}` for (H1);
- `hjac : TwoSupercuspidalAdjacentProductJacquet.{uF, uV} F T` (Ze80
  Proposition 1.11(b), Jacquet clause, module
  `TwoSupercuspidalProductStructureStatement`) for (H2);
- `hcomp : TwoSupercuspidalAdjacentProductComposition.{uF, uV} F T` (Ze80
  Proposition 1.11(b), composition clause, same module) for the existence of `W`
  in the segment case;
- `hE : SegmentEdgeJacquetFiltration.{uF, uV, uW} F T` in
  `jacquet_filtration_of_family`.

For general `σ`, the factor hypotheses are those of `SegmentEdgeFactorHypotheses`:

- `hσ`: every `σ i` is irreducible and supercuspidal;
- `ρ ρ' : SupercuspidalRep` with `hρ : σ ⟨k, _⟩ = ρ.obj` and
  `hρ' : σ ⟨k + 1, _⟩ = ρ'.obj`;
- `hadj`: `ρ' ≅ νρ` or `ρ ≅ νρ'` on isomorphism classes
  (`T.supercuspidalClassRealPowerTwist r 1`).

All declarations live in the namespace `Langlands.Classification.SegmentEdge`.
Provenance is internal. The case split by slot is bookkeeping. The mathematical
content is in the published `SegmentEdgeFactorHypotheses` and in the
hypotheses: the vanishing of the other Jacquet modules comes from the geometric
lemma, and the Jacquet modules of the two constituents of `ρ × ρ'` come from
Ze80 1.11(b).

## Definitions

- `FamilyJacquetVanishing T hr k hk Y`, for
  `Y : ∀ j : Fin γ.length, SmoothRep.{0, uF, uW} ℂ (GL (γ.size j))`: for every
  `j` and every `D : BlockShape (γ.size j)` with `1 < D.length` and `D ≠ S j`,
  `(T.normalizedJacquetFunctor D).obj (Y j)` is a subsingleton. This is the
  premise (H1) of `SegmentEdgeJacquetFiltration`, copied verbatim.
- `FamilyJacquetEquiv T hr k hk σ Y`, for
  `σ : ∀ i : Fin β.length, SmoothRep.{0, uF, uV} ℂ (GL (β.size i))` and `Y` as
  above: for every `j`, the representation of
  `(T.normalizedJacquetFunctor (S j)).obj (Y j)` has a `Representation.Equiv`
  to that of `FiniteTensor.externalSmoothObject (fun t => σ (e ⟨j, t⟩))`. This
  is the premise (H2) of `SegmentEdgeJacquetFiltration`, copied verbatim.

Both are `Prop`-valued definitions. Each unfolds definitionally to the
corresponding premise, so they can be passed to the statement directly.

## Declarations

### The statement applied to a family

- `jacquet_filtration_of_family hE σ Y h₁ h₂`: given
  `h₁ : FamilyJacquetVanishing T hr k hk Y` and
  `h₂ : FamilyJacquetEquiv T hr k hk σ Y`, the normalized Jacquet module along
  `β` of `i_γ(Y)` has a filtration indexed (through an equivalence `Fin N ≃ …`)
  by the minimal permutations conjugating the Levi of `β` to itself that are
  minimal representatives for `(γ, β)`. Its graded pieces are equivalent to the
  Weyl transports of the external tensor product of `σ`. The conclusion is the
  conclusion of `SegmentEdgeJacquetFiltration`, written out. Proof: `hE` applied
  to `m r hr k hk σ Y h₁ h₂`.

### The updated families

- `ne_adjacentMergeIndex_iff`: a slot `j` of `γ` differs from the merged slot
  `kk` if and only if `j.val ≠ k`. Proof: `Fin.ext_iff` and
  `BlockShape.adjacentMergeIndex_val`.
- `updateQuotient_jacquet_subsingleton`: `FamilyJacquetVanishing` for `Y_L`.
  It holds for any subrepresentation `W` (no `⊥`/`⊤` condition) and needs only
  `hgeo` and `hσ`. Proof: if `j = kk`, substitute, rewrite with
  `Function.update_self` and use `slot_quotient_jacquet_subsingleton`.
  Otherwise rewrite with `Function.update_of_ne` and use
  `slot_jacquet_subsingleton`.
- `updateSubrepresentation_jacquet_subsingleton`: `FamilyJacquetVanishing` for
  `Y_W`. The proof is the same, with
  `slot_subrepresentation_jacquet_subsingleton` at `kk`.
- `updateQuotient_jacquet_equiv`: `FamilyJacquetEquiv` for `Y_L` against
  `swappedFactors T hr k hk σ`. Needs `hjac`, `ρ`, `ρ'`, `hρ`, `hρ'`, `hadj`
  and `W ≠ ⊥`, `W ≠ ⊤`. At `kk` it is the second component of
  `merged_jacquet_equiv`, the Jacquet clause of Ze80 1.11(b) for the quotient.
  Elsewhere it is `slot_jacquet_equiv_swapped_of_ne`, with `j.val ≠ k` from
  `ne_adjacentMergeIndex_iff`.
- `updateSubrepresentation_jacquet_equiv`: `FamilyJacquetEquiv` for `Y_W`
  against `σ`. It is the first component of `merged_jacquet_equiv` at `kk` and
  `slot_jacquet_equiv_of_ne` elsewhere.

### The factors of a segment

Here `σ = T.segmentFactors A.obj m hr = (A, νA, …, ν^(m-1) A)`, where `A` is a
supercuspidal object of `GL_r` and `ν^s A` is `T.segmentFactor A.obj s`, the
twist of `A` by `|det|^s`. The published `segmentSupercuspidalFactor F T A s`
(module `SegmentTensorStabilizerProof`) packages `ν^s A` as a supercuspidal
object. The facts used are that a twist of an irreducible supercuspidal
representation by a character of the determinant is again irreducible and
supercuspidal (`SupercuspidalRep.twist`), and that
`|det|^1 · |det|^k = |det|^(k+1)` (`supercuspidalClassRealPowerTwist_add`).

- `segmentFactors_irreducible_supercuspidal T hr A`: every block factor of the
  segment is irreducible and supercuspidal. This is the property field of
  `segmentSupercuspidalFactor F T A i`, whose underlying object is
  `T.segmentFactors A.obj m hr i` by definition. It supplies `hσ`.
- `segmentFactors_eq_left T hr k hk A`:
  `T.segmentFactors A.obj m hr ⟨k, _⟩ = (segmentSupercuspidalFactor F T A k).obj`
  (`rfl`). It supplies `hρ` with `ρ = ν^k A`.
- `segmentFactors_eq_right T hr k hk A`:
  `T.segmentFactors A.obj m hr ⟨k + 1, hk⟩ =
  (segmentSupercuspidalFactor F T A (k + 1)).obj` (`rfl`). It supplies `hρ'`
  with `ρ' = ν^(k+1) A`.
- `segmentSupercuspidalFactor_isoClass T A s`: the class of `ν^s A` is
  `T.supercuspidalClassRealPowerTwist r s A.isoClass` (`rfl`).
- `segmentSupercuspidalFactor_succ_isoClass T A k`: the class of `ν^(k+1) A` is
  `T.supercuspidalClassRealPowerTwist r 1` of the class of `ν^k A`. Proof:
  rewrite both classes with the previous lemma, combine the two twists with
  `supercuspidalClassRealPowerTwist_add`, and check `(k + 1 : ℝ) = 1 + k`. With
  `Or.inl`, it supplies `hadj`.
- `segment_exists_proper_subrepresentation T hr k hk hcomp A`: the merged slot
  product `ν^k A × ν^(k+1) A` (that is, `slotProduct … kk` for the segment
  factors) has an invariant subspace `W` with `W ≠ ⊥` and `W ≠ ⊤`. Proof: the
  existence part of the unique-existence clause of `merged_composition` (Ze80
  1.11(b), composition clause, through `hcomp`), with the factor data above.
- `segment_updateQuotient_hypotheses T hr k hk hgeo hcomp hjac A`: there is an
  invariant subspace `W` of the merged slot product such that `Y_L` satisfies
  `FamilyJacquetVanishing` and, against
  `swappedFactors T hr k hk (T.segmentFactors A.obj m hr)`,
  `FamilyJacquetEquiv`. Proof: take `W` from the previous lemma and apply
  `updateQuotient_jacquet_subsingleton` and `updateQuotient_jacquet_equiv` with
  the segment factor data.
- `segment_updateSubrepresentation_hypotheses T hr k hk hgeo hcomp hjac A`: the
  same for `Y_W`, against `T.segmentFactors A.obj m hr`, through
  `updateSubrepresentation_jacquet_subsingleton` and
  `updateSubrepresentation_jacquet_equiv`.

The two segment results give a `W` that may differ between them. By the
uniqueness clause of `merged_composition` there is only one such `W`, but these
results do not state that.

## Universes

`σ` and `ρ`, `ρ'` live in carrier universe `uV`. The slot products and the
families `Y_L`, `Y_W` live in `max uF uV`. The two definitions and
`jacquet_filtration_of_family` allow any universe `uW` for `Y`. For `Y_L` and
`Y_W`, use `jacquet_filtration_of_family` with
`hE : SegmentEdgeJacquetFiltration.{uF, uV, max uF uV} F T`.

## Sources

- Zelevinsky 1980 (`zelevinsky-1980-induced-ii`), Proposition 1.11 (printed
  p.175, PDF page 12), through the published statements
  `TwoSupercuspidalAdjacentProductJacquet` and
  `TwoSupercuspidalAdjacentProductComposition`, and 1.2–1.3 (printed
  pp.170–171, PDF pages 7–8) for the geometric lemma.
- Bernstein–Zelevinsky 1977 (`bernstein-zelevinsky-1977-induced-i`),
  Lemma 2.12 (printed p.448, PDF page 9), the geometric lemma.
