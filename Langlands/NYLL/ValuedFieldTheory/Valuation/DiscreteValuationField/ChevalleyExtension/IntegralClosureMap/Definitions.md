# Canonical integral-closure map to an extending valuation subring

The ring homomorphism sends an element of the actual integral closure of the base valuation subring to the same element in an extending valuation subring. Its membership certificate is the published adapted M110.007 proof; the four ring-homomorphism laws are the original Subtype.ext rfl terms.

## Pinned source and attribution

Naganori Yamaguchi (assisted by OpenAI Codex), `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`. Registered original `external-lean-reuse-snapshots-2026-10-21`, content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The retained original file SHA-256 is `8f2d21dcbef11b6354d840a350ea2ddf775b670d74581bf9469d499afbe34dad`. The readable snapshot is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

The original copyright/Apache-2.0/author header is retained in the Lean file. The unchanged original license and notices are `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Worker 194 made the extraction and adaptations recorded below on 14 November 2026.

## Exact source correspondence

| Source unit and lines | Original declaration | Published declaration |
| --- | --- | --- |
| M110.025, 549–561 | `ValuationTheory.DiscreteValuationField.Valuation.integralClosureToValuationSubringOfHasExtension` | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosureToValuationSubringOfHasExtension` |

Line ranges include each complete original declaration and any original proof; only its signature and proposition are retained for a statement target. The definition names above denote the constructions themselves. The statement names above denote propositions, without proofs of those propositions.

## Telescope, construction and modifications

The ambient implicit K/L field parameters and Algebra K L precede ΓK and its ordered-group instance; the declaration then binds implicit ΓL and its ordered-group instance, explicit vK/vL, and the HasExtension instance. K, L, ΓK and ΓL retain independent source universes u, v, w and x. The unused declared universe names y and z introduce no parameters. All five ring-homomorphism fields, including the membership proof inside toFun, are retained verbatim after name resolution. No additional source unit is needed.

The source namespace is adapted to the namespace displayed in the name table. Original whole-module imports are replaced by these focused imports:

- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U007.Proofs`

Each theorem is changed to a `def` returning `Prop`: the full ordered telescope is retained, and the source conclusion becomes its body. Source theorem proofs and theorem attributes are omitted. Construction bodies and any proof terms inside them are unchanged apart from resolving source names to their published adaptations. Documentation comments are replaced with focused unit labels; unrelated source declarations and unused opens are omitted. No new global or local instance is declared. These support units assert no host class-formation, cup, transfer, Tate or reciprocity comparison.

## Lean declarations

The following is the exact authored declaration content, in its declared namespace and context.

```lean
noncomputable section

universe u v w x y z

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- Source M110.025: original construction. -/
def integralClosureToValuationSubringOfHasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] :
    integralClosure vK.valuationSubring L →+* vL.valuationSubring where
  toFun z :=
    ⟨(z : L),
      integralClosure_mem_valuationSubring_of_hasExtension
        (L := L) vK vL z⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
```
