# Distinct relative cosets give distinct embeddings: proof

This module proves the published closed proposition
`Langlands.NYLL.PortInternal.M276.d005Statement` (NYLL source unit M276.005,
the private theorem `abstractFixedFieldCosetToAlgHom_injective`) by the
theorem `Langlands.NYLL.PortInternal.M276.d005`. Its only import is the
statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U004.Statements`,
which imports the definition module `FixedFieldRelativeNorm.U002.Definitions`
of `abstractFixedFieldCosetToAlgHom` (M276.002). The statement pair and
everything it imports are unchanged.

## Exact target

The theorem's type is exactly `d005Statement`. Unfolded, it says:

```lean
∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω]
  (K L : ClosedSubgroup (Gal(Ω/k)))
  (hLK : L.toSubgroup ≤ K.toSubgroup),
  Function.Injective
    (Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom
      k Ω K L hLK)
```

In words: for closed subgroups `L ≤ K` of `Gal(Ω/k)` with `Ω / k` Galois,
if two elements `σ, τ` of `K` agree on the fixed field `Ω^L`, then
`σ⁻¹ τ ∈ L`, so they lie in the same left coset of `L`.

## Proof

The proof introduces the binders and two cosets `q`, `r` with equal images
`hqr`, and then runs the original tactic proof:

1. Both cosets are rewritten as classes of chosen representatives
   `Quotient.out q`, `Quotient.out r`; by `Quotient.sound'` and
   `QuotientGroup.leftRel_apply` it suffices that
   `(Quotient.out q)⁻¹ * Quotient.out r` lies in
   `extensionSubgroup K L hLK = L.toSubgroup.subgroupOf K.toSubgroup`, and by
   Mathlib's `Subgroup.mem_subgroupOf` that its underlying Galois element
   lies in `L`.
2. That element fixes every `x ∈ Ω^L`: evaluating `hqr` at `x` gives
   `(out q) x = (out r) x`, so `(out q)⁻¹ ((out r) x) = x` (closed by
   `simp`). Hence it lies in the fixing subgroup of `Ω^L`
   (`IntermediateField.mem_fixingSubgroup_iff`).
3. Since `L` is closed, Mathlib's infinite Galois correspondence
   `InfiniteGalois.fixingSubgroup_fixedField L` says the fixing subgroup of
   `Ω^L` is `L`, which finishes the proof.

The proof has the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Original correspondence

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldRelativeNorm.lean`
(SHA-256
`ab3ee25eed6dbccd721f18245bc5f17aea6fbe8e7631a11f41e9eb88032c1e4c`),
private theorem `abstractFixedFieldCosetToAlgHom_injective`: `omit` line
128, signature lines 129–133, proof lines 134–155.

Adaptation changes:

- The private theorem is named `d005` in `Langlands.NYLL.PortInternal.M276`
  after its source row, and proves the published closed proposition
  instead of carrying the binders in its signature. The proof therefore
  starts with one `intro` of the binders and of `q r hqr`; the source proof
  starts with `intro q r hqr`.
- The source step
  `apply (mem_extensionSubgroup_iff K L hLK ((Quotient.out q)⁻¹ * Quotient.out r)).2`
  uses the NYLL lemma `KummerTheory.mem_extensionSubgroup_iff` (source unit
  M022.001), which is not in the Library. It is replaced by
  `apply Subgroup.mem_subgroupOf.2`. Since the published
  `extensionSubgroup K L hLK` is the reducible abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`, Mathlib's `Subgroup.mem_subgroupOf`
  gives the same criterion (`x ∈ H.subgroupOf K ↔ (x : G) ∈ H`), and the
  following steps are unchanged. Other Library ports make the same
  replacement (see the M040 `FiniteGaloisSubextension` module).
- Otherwise the tactic proof is the original one, with
  `Langlands.NYLL.LocalClassFieldTheory` opened so that the published names
  resolve as in the source.
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
