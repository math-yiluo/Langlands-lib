# Smooth contragredients of cuspidal product-Levi representations

Author: Worker 918.

The closing theorem

```text
theorem Langlands.CuspidalSupport.leviCuspidalContragredient
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) :
    LeviCuspidalContragredientTheorem.{uF, uV} F T B
```

has the existing proposition
`Langlands.CuspidalSupport.LeviCuspidalContragredientTheorem` from
[`QuasicuspidalStructureStatement`](QuasicuspidalStructureStatement.md) as its
type. It covers every prime, every actual p-adic field, every supplied
topological realization `T`, every natural rank `n` (zero included) and every
ordered block shape `B`. The field and representation universes `uF` and `uV`
are independent. The topology is exactly `T.topology` with the published
instance `T.leviTopologicalGroup B`, as in the statement. For every smooth
representation `A` of the actual product Levi `B.Levi F.Carrier`, the proof
shows that `IsLeviCuspidal B A.representation` implies
`IsLeviCuspidal B (smoothContragredient A.representation)`. Irreducibility is
not assumed. The theorem has no extra hypotheses, chosen pairings or duality
witnesses. Inspection reports only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The statement module and the modules it imports are unchanged.

## Notation

For a block refinement `S` of `B`, `S i` is a block shape of the size of
outer block `i`. `refinedUnipotent F.Carrier B S` is the product over `i` of
the upper radicals `(S i).unipotentSubgroup`, and
`refinedOppositeUnipotent F.Carrier B S` is the product of the lower radicals
`(S i).oppositeUnipotentSubgroup`. Both are subgroups of the product Levi.

## Geometric helpers

These declarations are elementary consequences of the published
block-reversal results in [`ReverseBlocks`](../../Group/GL/ReverseBlocks.md).
They hold over every commutative ring `R`.

- `ProductLeviDualOpposite.reverseRefinement B S` is the refinement whose block `i` is
  `(S i).reverse`. It keeps the outer block order and reverses the order of
  the inner blocks of every outer block.
- `ProductLeviDualOpposite.reverseWeyl B S R : B.Levi R` is the product Levi element whose block `i`
  is the permutation matrix `(S i).reverseMatrix R`.
- `innerReverseRefinement_refinedUnipotent_map_conj`: the image of
  `refinedUnipotent R B (ProductLeviDualOpposite.reverseRefinement B S)` under conjugation by
  `ProductLeviDualOpposite.reverseWeyl B S R` is `refinedOppositeUnipotent R B S`. Conjugation in
  the product group acts blockwise, so the proof reduces to the published
  `BlockShape.reverse_unipotentSubgroup_map_conj` in each block.
- `refinedParabolic_eq_top_iff`: `refinedParabolic R B S` is the whole product
  Levi exactly when every block parabolic `(S i).parabolic R` is the whole
  block group. For the forward direction, put an arbitrary block element `g`
  in position `i` and `1` elsewhere (`Pi.mulSingle`) and read off component
  `i`.
- `innerReverseRefinement_refinedParabolic_ne_top_iff`: the reversed
  refinement gives a proper refined parabolic exactly when `S` does. By the
  previous item this reduces to the published
  `BlockShape.reverse_parabolic_eq_top_iff` in each block. The equivalence
  holds for all refinements, including those with one-block or rank-zero
  blocks.

## Duality step

`refinedJacquet_smoothContragredient_subsingleton_of_opposite` states the
following. Let `ρ` be an admissible representation of `B.Levi F.Carrier`
whose coinvariants by `refinedOppositeUnipotent F.Carrier B S` are
subsingleton. Then the coinvariants of `smoothContragredient ρ` by
`refinedUnipotent F.Carrier B S` are subsingleton.

The proof applies the published
`Langlands.Parabolic.refinedNaturalJacquetDuality` (module
[`NaturalJacquetDualityProof`](../Parabolic/NaturalJacquetDualityProof.md))
to `Rep.of ρ` and the admissibility proof. It gives an actual equivalence of
representations from `T.normalizedRefinedJacquet B S (smoothContragredient ρ)`
to `smoothContragredient (T.normalizedRefinedOppositeJacquet B S ρ)`. The
carrier of the first is the upper coinvariant module of the smooth dual;
normalization changes only the action, not the carrier. The carrier of the
second is the smooth dual of the opposite coinvariant module, which is
subsingleton because that module is. The equivalence is injective, so its
source is subsingleton. Only the existence of the equivalence is used; its
naturality clause is discarded.

## Proof of the closing theorem

Install `T.topology` and `T.leviTopologicalGroup B`, and take `A` with
`IsLeviCuspidal B A.representation`, that is, admissibility `hadm` and the
vanishing `hvan` of the upper coinvariants for every proper refinement.

1. **Admissibility.** For an open subgroup `K` of the product Levi, the
   published choice `T.leviCompactOpen B` gives a compact open subgroup inside
   `K`. With this cofinality, the published
   `isAdmissible_smoothContragredient_of_compact_cofinal` makes
   `smoothContragredient A.representation` admissible.
2. **Quasicuspidality.** Fix a refinement `S` with
   `refinedParabolic F.Carrier B S ≠ ⊤`. The refinement
   `ProductLeviDualOpposite.reverseRefinement B S` is also proper, so `hvan` gives vanishing
   coinvariants by its upper radical. The published
   `Langlands.Jacquet.coinvariants_conj_subsingleton_iff` (module
   [`SupercuspidalContragredientAux`](../Classification/SupercuspidalContragredientAux.md))
   transports this vanishing to the image of that radical under conjugation by
   `ProductLeviDualOpposite.reverseWeyl B S F.Carrier`. This image is
   `refinedOppositeUnipotent F.Carrier B S`. The duality step then gives
   vanishing of the coinvariants of the smooth dual by
   `refinedUnipotent F.Carrier B S`.

The proof follows the same pattern as the published GL proof
`Langlands.GeneralLinear.isSupercuspidal_smoothContragredient`, with
product refinements in place of GL block shapes. It does not prove or restate
that GL theorem.

## Dependencies

The module imports the statement module, `NaturalJacquetDualityProof`,
`SupercuspidalContragredientAux`, `Group.GL.ReverseBlocks` and
`Group.GL.CompactOpen`. Its transitive Library imports include no module on
positive-root discrete-series support, joint support, regular Langlands
heads or exhaustion, tempered exhaustion, square-integrable Langlands
classification or ordered-segment classification. It does not use Silberger
1978 Lemma 5.3.

## Provenance

The target statement records its source: Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), section 2.4(c),
printed pages 446-447 (source ID `bernstein-zelevinsky-1977-induced-i`).
BZ77 refers to its reference [1], chapter II, for the GL proof. The present
proof does not follow that cited argument. It is an internal derivation from
published Library constructions: the refined natural Jacquet duality, the
block-reversal matrices and the conjugation invariance of coinvariant
vanishing. The helper declarations are elementary consequences of these
constructions and have no separate literature source.

The two reversal constructions are the existing declarations imported from [RefinementReversal](../Parabolic/RefinementReversal.md). This shared module imports no classification or cone theorem.
