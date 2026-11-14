# Pulling the chosen separable valuation ring back along an embedding: proof

This module proves the published closed target
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_comap_embeddingStatement`
([target](ComapEmbeddingStatement.md), NYLL source unit M265.012) by the theorem

```lean
theorem localSeparableValuationSubring_comap_embedding :
    localSeparableValuationSubring_comap_embeddingStatement
```

in namespace `Langlands.NYLL.LocalClassFieldTheory`, the adapted source name.
Its type is the target; neither has a level parameter. The theorem says: let
`K : Type` be a nonarchimedean local field and `L : Type` a finite separable
extension whose valuation extends that of `K`. Then for every `K`-embedding
`i : L →ₐ[K] SeparableClosure K`, the preimage under `i` of the chosen
valuation ring `localSeparableValuationSubring K` is the valuation ring of `L`.

## Proof

The proof does not follow the source route. The source proof (lines 167–200)
identifies both rings with the valuation ring of one chosen complete-DVF
extension, using the uniqueness theorem
`target_valuationSubring_eq_of_finite_separable` (M196.039). That theorem is not
in the Library. This proof replaces it by a short argument with valuation
overrings.

The module first installs the published M249.001/M249.002 instances
`Langlands.NYLL.PortInternal.M249.d001` and `d002` (the algebra structure of
`AlgebraicClosure K` over `SeparableClosure K` and its scalar tower over `K`)
with `attribute [local instance]`, as the source file does, because the
published `localSeparableValuationSubring K` is the preimage of
`Langlands.NYLL.PortInternal.M249.d003 K` along that algebra map.

After `intro` of `K`, `L`, their instance binders, `i` and the separability
instance, write `base` for the published canonical complete DVF
`Langlands.NYLL.LocalFieldTheory.localCompleteDVF K` and `𝒪` for
`base.valuation.valuationSubring`.

1. **An integral-closure valuation ring.** The published theorem
   `exists_integralClosure_standard_completeDVF K L base` (M245.017) gives a
   complete DVF `target` on `L` and the fact `hmem`: for every `z : L`,
   `z ∈ target.valuation.valuationSubring` if and only if `z` lies in the
   integral closure of `𝒪` in `L`. Write `T` for
   `target.valuation.valuationSubring`. Its ring-equivalence conjunct is not
   used.
2. **Key claim.** Let `D` be any valuation subring of `L` such that, for every
   `x : K`, `algebraMap K L x ∈ D` if and only if `x ∈ 𝒪`. Then `T = D`:
   - *`T ≤ D`.* Let `z ∈ T`. By `hmem`, `z` is integral over `𝒪`. The map
     `φ : 𝒪 →+* D`, `a ↦ algebraMap K L a`, is well defined by the hypothesis
     on `D`, and composing it with the inclusion `D → L` gives the algebra map
     `𝒪 → L` (checked by `rfl`). Mathlib's `RingHom.IsIntegralElem.of_comp`
     then makes `z` integral over `D`. A valuation subring is integrally
     closed (Mathlib instance `instIsIntegrallyClosedSubtypeMemValuationSubring`)
     with fraction field `L`, so `IsIntegrallyClosed.isIntegral_iff` puts
     `z` in `D`.
   - *`D ≠ ⊤`.* If `D = ⊤`, then every `x : K` lies in `𝒪` by the hypothesis
     on `D`, so `𝒪 = ⊤`. Mathlib's `Valuation.valuationSubring_eq_top_iff`
     then says that `base.valuation` is trivial. This contradicts the instance
     `Valuation.IsRankOneDiscrete.instIsNontrivial`, available because the
     valuation of a complete DVF is rank-one discrete.
   - *Conclusion.* `T` is the valuation ring of a rank-one discrete valuation,
     hence a discrete valuation ring (Mathlib's
     `Valuation.valuationSubring_isDiscreteValuationRing`) and of Krull
     dimension at most one (instance
     `instKrullDimLEOfNatNatOfIsDiscreteValuationRing`). Mathlib's
     `ValuationSubring.eq_of_le_of_ne_top` says that such a ring equals every
     proper valuation overring, so `T = D`.
3. **The chosen separable ring pulls back to `𝒪` (source M249.007).** The `have`
   `hpull` states: for every `x : K`,
   `algebraMap K (SeparableClosure K) x ∈ localSeparableValuationSubring K`
   if and only if `x ∈ 𝒪`. Its proof is the source proof of M249.007
   (`localSeparableValuationSubring_pullback`, lines 94–104 of
   `LocalResidueDatum.lean`) with the private source lemma M249.004
   (lines 66–76) inlined as the inner `have habsolute`: the third conjunct of
   `Classical.choose_spec` of the published Chevalley theorem
   `exists_extension_valuationSubring (L := AlgebraicClosure K) base.valuation`
   (whose chosen witness is `d003 K`) says that `algebraMap K (AlgebraicClosure K) y ∈ d003 K`
   if and only if `y ∈ 𝒪`. A `change` rewrites membership in the preimage as
   membership of the image in `AlgebraicClosure K`, and
   `IsScalarTower.algebraMap_apply` folds the two algebra maps into one.
   The same theorem is the target of a separate proof task; it is reproved
   here so that this proof does not import that unpublished proof module.
4. **The pulled-back ring lies over `𝒪`.** For `x : K`, membership of
   `algebraMap K L x` in `(localSeparableValuationSubring K).comap i.toRingHom`
   unfolds by `change` to `i (algebraMap K L x) ∈ localSeparableValuationSubring K`.
   Rewriting with `i.commutes` gives
   `algebraMap K (SeparableClosure K) x ∈ localSeparableValuationSubring K`,
   which is equivalent to `x ∈ 𝒪` by `hpull x`. This is the body of the
   source step `hBext` (lines 173–177).
5. **The valuation ring of `L` lies over `𝒪`.** For `x : K`, `change` turns the
   membership into `ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
   base.valuation x ≤ 1`. Mathlib's `Valuation.HasExtension.val_map_le_one_iff`
   rewrites the left side to `ValuativeRel.valuation K x ≤ 1`, and the remaining
   equivalence holds by `rfl`, as in the body of the source step `hCext` (lines 181–186).
6. Steps 2, 4 and 5 give `T` equal to both rings, so they are equal.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compiled the module
with no errors or warnings, first for Worker 3 against Library commit
`c257f7ccf7972d2aea55b65301d4db306861161e` (diagnostic
`83c838ad-e81e-4aa7-8905-24e2511a8d25`) and again for Worker 400 against Library
commit `c40a01345b2f4172fa41e07ff31644b40e695003` (diagnostic
`6e8985de-c725-4a9a-8fe4-25d42b0ebe42`). Inspection of the theorem reported kind
`theorem`, no level parameters, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. Worker 3 read the Mathlib instance names in
step 2 from a private probe that printed the elaborated instance terms with
`pp.explicit`; a further private `#check` probe (diagnostic
`d7a0b5df-56d0-4a3a-a205-e9270bf09356`) confirmed that
`Valuation.IsRankOneDiscrete.instIsNontrivial`,
`instIsIntegrallyClosedSubtypeMemValuationSubring`,
`instKrullDimLEOfNatNatOfIsDiscreteValuationRing` and
`Valuation.valuationSubring_isDiscreteValuationRing` exist with the types used
above.

## Imports

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedComparison.ComapEmbeddingStatement`,
  the published [target](ComapEmbeddingStatement.md), which brings in the
  published M249 definitions module
  [`LocalResidueDatum.U006.Definitions`](../LocalResidueDatum/U006/Definitions.md)
  (`localSeparableValuationSubring`, `d001`–`d003`) and, through it,
  `localCompleteDVF` and the Chevalley theorem
  `exists_extension_valuationSubring`.
- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.StandardCompleteDVFProof`,
  the published [M245.017 proof](../../../../../ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure/StandardCompleteDVFProof.md)
  `exists_integralClosure_standard_completeDVF`.

The Mathlib results above come through these imports. The published target and
the imported declarations are used by name; none of them is modified.

## Source correspondence and changes

The original theorem is
`LocalClassFieldTheory.localSeparableValuationSubring_comap_embedding` at lines
154–200 of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedComparison.lean#L154-L200)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`48110dffb73b0584773bf23cb7cde4ebbb32c51804442311758ebfcc934460b2`). Its
statement is the published target.

Worker 3 made these changes on 13 November 2026:

- the theorem proves the closed target, so the proof begins with `intro` of the
  section variables, `i` and the separability instance;
- the source theorem `localSeparableValuationSubring_pullback` (M249.007), which
  the source proof cites, is reproved inline as `hpull` by its source proof
  (step 3), instead of being imported;
- the source's two membership computations (`hBext`, lines 170–177, and
  `hCext`, lines 178–186) are kept, but as
  membership equivalences over `𝒪` rather than as `Valuation.HasExtension`
  instances; the source's application of
  `hasExtension_valuation_of_valuationSubring_pullback` is therefore not needed;
- the source's identification of both rings with the chosen target through
  `exists_integralClosure_standard_fundamental_identity`,
  `valuationSubring_isScalarTower_of_hasExtension` and
  `target_valuationSubring_eq_of_finite_separable` (lines 187–200) is replaced
  by step 2 above, which uses the published M245.017 theorem and Mathlib's
  overring theorem for valuation rings of Krull dimension at most one;
- the source's `omit` and `open … in` clauses are dropped.

The Lean file is Worker 3's shared draft for this proof task (draft revision 1),
submitted unchanged by Worker 400 with Worker 3 as coauthor; Worker 400 rechecked
it against the current Library and updated only the Checks section and this
paragraph of the Markdown.

## Provenance and license

The readable original is in registration
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The Lean
file keeps the original copyright and author header verbatim and records the
modifications. The Apache-2.0
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are unchanged in the
Library.
