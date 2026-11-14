# The coset action on a fixed unit is evaluation of an embedding: proof

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_abstractFixedFieldUnit_valStatement`
(NYLL source unit M276.007) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_abstractFixedFieldUnit_val`.
Its only import is the statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U004.Statements`.
The statement pair and everything it imports are unchanged.

## Exact target

The theorem's type is exactly
`relativeCosetAction_abstractFixedFieldUnit_valStatement`. Unfolded, it
says (unqualified names are in `Langlands.NYLL.LocalClassFieldTheory`):

```lean
∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω]
  (K L : ClosedSubgroup (Gal(Ω/k)))
  (hLK : L.toSubgroup ≤ K.toSubgroup)
  (x : (abstractRelativeFixedField k Ω hLK)ˣ)
  (q : K.toSubgroup ⧸
    Langlands.NYLL.CyclicCohomology.extensionSubgroup K L hLK),
  ((Additive.toMul
    (Langlands.NYLL.ClassFormation.relativeCosetAction
      (galoisAmbientUnitsRep k Ω)
      K L hLK
      (abstractRelativeFixedFieldUnitsEquivGaloisFixed
        k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω) =
    abstractFixedFieldCosetToAlgHom k Ω K L hLK q
      (x : abstractRelativeFixedField k Ω hLK)
```

In words: for a unit `x` of the fixed field `Ω^L` and the left coset `q` of
`σ ∈ K`, letting `σ` act on `x` through the Galois representation on `Ωˣ`
gives the element `σ x` of `Ω`, which is the value at `x` of the embedding
attached to `q` by `abstractFixedFieldCosetToAlgHom` (M276.002).

## Proof

After introducing the binders, `Quotient.inductionOn' q` reduces to a coset
`q = ⟦σ⟧` of a representative `σ : K.toSubgroup`. For such a coset both
sides are, by definition, `σ.1 (x : Ω)`:

- `relativeCosetAction` is `Quotient.liftOn'` of `σ ↦ A.ρ σ.1 a.1`; for
  `A = galoisAmbientUnitsRep k Ω` the action of `σ.1` on the fixed unit
  coming from `x` (via `abstractRelativeFixedFieldUnitsEquivGaloisFixed`,
  which keeps the underlying unit) is `Units.map σ.1`, whose value is
  `σ.1 x`;
- `abstractFixedFieldCosetToAlgHom` is `Quotient.liftOn'` of
  `σ ↦ (abstractSubgroupEquivGaloisGroup k Ω K σ).toAlgHom.comp (inclusion)`,
  whose value at `x` is again `σ.1 x`.

So the goal closes by `rfl`, as in the source.

The proof has the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Original correspondence

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldRelativeNorm.lean`
(SHA-256
`ab3ee25eed6dbccd721f18245bc5f17aea6fbe8e7631a11f41e9eb88032c1e4c`),
theorem `relativeCosetAction_abstractFixedFieldUnit_val`: `omit` line 171,
docstring line 172, signature lines 173–184, proof lines 185–187.

Adaptation changes:

- The theorem gets the `Langlands.NYLL` namespace prefix and proves the
  published closed proposition instead of carrying the binders in its
  signature. The proof therefore starts with `intro`.
- After the `intro`, the tactic proof is the original
  `refine Quotient.inductionOn' q ?_; intro σ; rfl`.
- The single import replaces the original imports. The original
  `noncomputable section`, the namespace openings (not needed here) and all
  other declarations of the module are omitted. The source docstring is
  kept.

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

## Shared draft reuse

Worker 605 reused Worker 56's complete shared draft for Task 6334,
revision 1, on 14 November 2026. The draft's proof, import and original
attribution are retained. Worker 605 checked the target and the
representative computation against the published definitions at Library
base `9d71020c4b80abb41dbf8102ded7d93202edf495`, compared the proof with
lines 171–187 of the pinned original, and added this reuse record and the
corresponding Lean modification note. Worker 56 is credited as a
coauthor of the contribution.

No instance or simp attribute is installed.

The project Lean service built this module on 14 November 2026 with no
errors or warnings. Declaration inspection reports precisely the standard
axioms listed above; independent review and exact-target validation are
performed for the submitted candidate.
