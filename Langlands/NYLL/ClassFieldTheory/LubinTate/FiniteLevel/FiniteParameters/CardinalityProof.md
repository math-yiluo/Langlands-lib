# Cardinality of the finite unit parameter quotient (M358.008 proof)

The module proves NYLL M358.008 as the exact published target
`Langlands.NYLL.LubinTate.standardLubinTateUnitParameter_natCardStatement`.
The public theorem is
`Langlands.NYLL.LubinTate.standardLubinTateUnitParameter_natCard`, with
universe parameters `u, v`, implicit `{K : Type u} [Field K]` and explicit
`(F : LocalField.{u, v} K) (n : ℕ)`. Its type is
`standardLubinTateUnitParameter_natCardStatement F n`, that is,

`Nat.card (standardLubinTateUnitParameter F n) =
  (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n`,

where `standardLubinTateUnitParameter F n` is the published quotient
`F.valuationSubringˣ ⧸ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)`
(`FiniteParameters.Definitions`). There is no additional hypothesis. The
entry module is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters.CardinalityProof`.
The published target pair `FiniteParameters.CardinalityStatements` and
everything it imports are used unchanged.

## Notation

Write `O := F.valuationSubring`, the valuation subring of the stored complete
discrete valuation (`F.toHenselianDVF.valuation.valuationSubring`), and
`m := F.maximalIdeal`, which unfolds to `IsLocalRing.maximalIdeal O`.
`F.residueField` unfolds to `IsLocalRing.ResidueField O`, which is
definitionally `O ⧸ m`. Write `q := Nat.card F.residueField`. The published
subgroup `higherPrincipalUnitGroup F.toCompleteDVF k` has carrier
`{x : Oˣ | (x : O) - 1 ∈ m ^ k}` (`PrincipalUnits.Filtration.Definitions`,
line 31).

Instances found by instance search (confirmed in a private check with
`#synth` in the approved environment):

- `IsLocalRing O`: Mathlib's `ValuationSubring.isLocalRing`;
- `IsDiscreteValuationRing O`: Mathlib's
  `Valuation.valuationSubring_isDiscreteValuationRing`
  (`Mathlib/RingTheory/Valuation/Discrete/Basic.lean`, line 449), using the
  published instance `Valuation.IsCompleteDiscrete.isRankOneDiscrete` of the
  stored valuation (`Complete.Definitions`);
- `IsDedekindDomain O`: Mathlib's `IsPrincipalIdealRing.isDedekindDomain`;
- `Finite F.residueField`: the stored field `F.residueFinite` of the
  published `LocalField` structure.

## Implemented proof

Let `I := m ^ (n + 1)` and let `J := m.map (Ideal.Quotient.mk I)` be the image
of `m` in `R := O ⧸ I`. Since `n + 1 ≠ 0`, `I ≤ m` (`Ideal.pow_le_self`).

1. Membership in `J`. For `a : O`, the class of `a` lies in `J` iff `a ∈ m`
   (Mathlib `Ideal.mem_quotient_iff_mem`,
   `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, line 191, using
   `I ≤ m`).
2. Units of `R`. For `a : O`, the class of `a` is a unit of `R` iff `a ∉ m`.
   If the class is a unit and `a ∈ m`, then `J` contains a unit, so `J = ⊤`
   (`Ideal.eq_top_of_isUnit_mem`); then the class of `1` lies in `J`, so
   `1 ∈ m` by step 1, contradicting `m ≠ ⊤`. Conversely, if `a ∉ m` then `a`
   is a unit of the local ring `O` (`IsLocalRing.notMem_maximalIdeal`), and
   its image is a unit.
3. The unit map. Let `φ : Oˣ →* Rˣ` be `Units.map` of the quotient map.
   - Its kernel is exactly `higherPrincipalUnitGroup F.toCompleteDVF (n + 1)`:
     `φ x = 1` iff `mk I x = mk I 1` iff `(x : O) - 1 ∈ I`
     (`Ideal.Quotient.eq`), which is the defining condition of the subgroup.
   - It is surjective: lift a unit `r` of `R` to some `a : O`
     (`Ideal.Quotient.mk_surjective`); by step 2, `a ∉ m`, so `a` is a unit of
     `O`, and its unit maps to `r`.
   Hence `standardLubinTateUnitParameter F n ≃* Rˣ` by
   `QuotientGroup.quotientKerEquivOfSurjective`
   (`Mathlib/GroupTheory/QuotientGroup/Basic.lean`, line 159).
4. Cardinality of `R`. Since `O` is a discrete valuation ring it is not a
   field, so `m ≠ ⊥` (`IsDiscreteValuationRing.not_a_field`). As `O` is a
   Dedekind domain and `m` is prime, Mathlib's `cardQuot_pow_of_prime`
   (`Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean`, line 155) gives
   `Nat.card (O ⧸ m ^ (n + 1)) = Nat.card (O ⧸ m) ^ (n + 1)`, i.e.
   `Nat.card R = q ^ (n + 1)` after unfolding `Submodule.cardQuot_apply`.
   As `q > 0` (`Nat.card_pos`, from the finite nonempty residue field), `R` is
   finite (`Nat.finite_of_card_ne_zero`).
5. Cardinality of `J`. The third isomorphism theorem
   `DoubleQuot.quotQuotEquivQuotOfLE` (`I ≤ m`;
   `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, line 944) identifies
   `R ⧸ J` with `O ⧸ m`, so the index of `J` as an additive subgroup is `q`.
   Lagrange's theorem `AddSubgroup.card_mul_index`
   (`Mathlib/GroupTheory/Index.lean`, line 290) gives
   `Nat.card J * q = q ^ (n + 1) = q ^ n * q`, hence `Nat.card J = q ^ n`.
6. Cardinality of `Rˣ`. By steps 1 and 2 (every element of `R` is a class
   `mk I a`), the range of `Units.val : Rˣ → R` is the complement of `J`.
   Since `Units.val` is injective (`Nat.card_range_of_injective`), and
   `Set.ncard_add_ncard_compl` (`Mathlib/Data/Set/Card.lean`, line 1144)
   gives `Nat.card J + #(Jᶜ) = Nat.card R`, we get
   `Nat.card Rˣ = q ^ (n + 1) - q ^ n` (by `omega`).
7. Conclusion. By step 3,
   `Nat.card (standardLubinTateUnitParameter F n) = Nat.card Rˣ
    = q ^ (n + 1) - q ^ n = (q - 1) * q ^ n`, using `Nat.sub_mul`, `one_mul`,
   `pow_succ` and `mul_comm`.

Inspection of the theorem in the approved environment reports kind
`theorem`, universe parameters `u, v`, and only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Source correspondence and adaptations

The source is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/FiniteParameters.lean`:
docstring lines 114–115, signature lines 116–121 and proof lines 121–167 of
theorem `standardLubinTateUnitParameter_natCard`. The adapted theorem has the
same name with the `Langlands.NYLL` prefix, the same arguments and the same
conclusion, stated through the published target constant.

The proof route differs from the source. The source splits the quotient by
the image `H` of `U^1`: it identifies the outer quotient with `Oˣ ⧸ U^1`
(M120.083) and then with the residue-field units (M228.002), counted by
`Nat.card_units`; it identifies `H` with `U^1 ⧸ U^(n+1)` (M120.051), counted
by `q ^ n` through a chosen uniformizer (M231.064); and it concludes with
`Subgroup.card_eq_card_quotient_mul_card_subgroup`. None of these
prerequisites is in the Library. The implemented proof instead identifies the
quotient with the units of the finite ring `O ⧸ m ^ (n + 1)` and counts them
directly with Mathlib, as described above. It uses no uniformizer, no
principal-unit subquotient and no NYLL declaration besides the published
target and its imports.

Modifications: the `Langlands.NYLL` namespace prefix; the conclusion stated
as the published target constant; the source imports replaced by the
published target module and the Mathlib modules
`Mathlib.RingTheory.Ideal.Norm.AbsNorm` (`cardQuot_pow_of_prime`) and
`Mathlib.RingTheory.Valuation.Discrete.Basic` (the discrete valuation ring
instance of `O`); and the source proof replaced by the direct proof above.

## Imports and scope

The direct imports are the published
`FiniteParameters.CardinalityStatements` (the target, importing the published
`FiniteParameters.Definitions`) and the two Mathlib modules named above. The
only public addition is the theorem. There is no helper declaration, global
instance, axiom, finiteness hypothesis or chosen uniformizer.

## Attribution and source records

The registered source `external-lean-reuse-snapshots-2026-10-21` has
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The verified SHA256 of `FiniteParameters.lean` is
`c1254bd8cbffb7941e723d32b6a47ccc353bb2265211c86c99565dc47c2cd92d`.
The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Its author verification record `files/.github/verification/publication.json`
lists the same SHA256 for `FiniteParameters.lean` (line 2119), and its
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_*` attribution files have no
entry for this file. No applicable erratum was found.

The original copyright and author header is retained verbatim: copyright 2026
Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI Codex),
under Apache-2.0. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany this adaptation.
Worker 441 made the modifications listed above on 14 November 2026 and wrote
this Markdown; no other worker's Lean content was reused. The approved
environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
