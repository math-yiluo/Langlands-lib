# Relative cosets give every embedding of a finite fixed field: proof

This module proves the published closed proposition
`Langlands.NYLL.PortInternal.M276.d004Statement` (NYLL source unit M276.004,
the private theorem `abstractFixedFieldCosetToAlgHom_surjective`) by the
theorem `Langlands.NYLL.PortInternal.M276.d004`. Its only import is the
statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U004.Statements`,
which imports the definition module `FixedFieldRelativeNorm.U002.Definitions`
of `abstractFixedFieldCosetToAlgHom` (M276.002). The statement pair and
everything it imports are unchanged.

## Exact target

The theorem's type is exactly `d004Statement`. Unfolded, it says:

```lean
∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsSepClosed Ω]
  (K L : ClosedSubgroup (Gal(Ω/k)))
  (hLK : L.toSubgroup ≤ K.toSubgroup)
  [FiniteDimensional
    (Langlands.NYLL.LocalClassFieldTheory.abstractFixedField k Ω K)
    (Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField
      k Ω hLK)],
  Function.Surjective
    (Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom
      k Ω K L hLK)
```

In words: write `Ω^K ⊆ Ω^L` for the fixed fields of `L ≤ K` in a separably
closed Galois extension `Ω / k`. If `Ω^L` is finite over `Ω^K`, every
`Ω^K`-embedding `f : Ω^L → Ω` is `x ↦ σ x` for some `σ ∈ K`, i.e. it is the
image of the left coset of `σ`.

## Proof

The proof introduces the binders (`k`, `Ω`, the five instances, `K`, `L`,
`hLK`, the finite-dimensionality instance and the embedding `f`) and then
runs the original tactic proof:

1. `Ω^L` is separable over `Ω^K` and `Ω` is separable over `Ω^L`, by
   Mathlib's `Algebra.isSeparable_tower_bot_of_isSeparable` and
   `Algebra.isSeparable_tower_top_of_isSeparable` applied to the tower
   `Ω^K ⊆ Ω^L ⊆ Ω` (`Ω` is separable over `Ω^K` because `Ω / k` is Galois).
2. Because `Ω` is separably closed, Mathlib's
   `IsSepClosed.surjective_domRestrict_of_isSeparable` extends `f` to an
   `Ω^K`-algebra endomorphism `φ : Ω → Ω` whose restriction to `Ω^L` is `f`.
3. `Ω` is normal over `Ω^K`, so `φ` is bijective
   (`Normal.toIsAlgebraic.algHom_bijective₂`) and `AlgEquiv.ofBijective`
   makes it an element `σReal` of `Gal(Ω/Ω^K)`.
4. The published equivalence `abstractSubgroupEquivGaloisGroup k Ω K`
   (M099.007) identifies `K` with `Gal(Ω/Ω^K)`; its inverse gives `σ ∈ K`
   acting as `σReal`.
5. The coset of `σ` maps to `x ↦ σ x = φ x = f x`, checked pointwise by
   `AlgHom.ext` and definitional unfolding (`change`).

The proof has the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Original correspondence

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldRelativeNorm.lean`
(SHA-256
`ab3ee25eed6dbccd721f18245bc5f17aea6fbe8e7631a11f41e9eb88032c1e4c`),
private theorem `abstractFixedFieldCosetToAlgHom_surjective`: signature
lines 90–96, proof lines 97–126.

Adaptation changes:

- The private theorem is named `d004` in `Langlands.NYLL.PortInternal.M276`
  after its source row, and proves the published closed proposition
  instead of carrying the binders in its signature. The proof therefore
  starts with one `intro` of the binders and the embedding `f`; the source
  proof starts with `intro f`.
- After that, the tactic proof is the original one, line for line, with
  `Langlands.NYLL.LocalClassFieldTheory` opened so that the published names
  `abstractFixedField`, `abstractRelativeFixedField` and
  `abstractSubgroupEquivGaloisGroup` resolve as in the source.
- The single import replaces the original imports. The original
  `noncomputable section`, other namespace openings and all other
  declarations of the module are omitted. The adapted docstring describes
  the theorem, which has no source docstring.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
authorship line and Apache-2.0 notice, followed by a dated modification
record by Worker 56. The retained
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged.

No instance or simp attribute is installed. The development check reports
no errors or warnings.
