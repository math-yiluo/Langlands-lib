# NYLL M096.004: relative coset action on intermediate-field units

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_valStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val`.
The theorem's type is exactly that proposition applied to its source
parameters, `relativeCosetAction_intermediateFieldUnit_valStatement K Ω E x q`.

Its direct imports are
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Statements`
and the published proof module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.U002.Proofs`,
which supplies the theorem `relativeCosetAction_mk` used by the proof. Those
published Lean/Markdown pairs and their complete imported chains remain
unchanged.

## Target and parameters

The theorem is stated in the source's section telescope, with the source's
`omit [FiniteDimensional K E] in`. Its parameters are, in this order,
explicit `K Ω : Type`, the instances
`[Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]`, an explicit intermediate
field `E : IntermediateField K Ω`, the instance `[IsGalois K E]`, an explicit
unit `x : Eˣ` and an explicit coset

```lean
q : (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
  extensionSubgroup (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
```

exactly as in the published proposition. No finite-dimensionality hypothesis
is used.

Unfolding the published proposition gives

```lean
((Additive.toMul
    (relativeCosetAction (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
      (intermediateFieldUnitsEquivGaloisFixed K Ω E (Additive.ofMul x)) q) :
    Ωˣ) : Ω) =
  E.val ((baseFixingExtensionQuotientEquivGaloisGroup K Ω E q) (x : E))
```

The left side is the published abstract relative coset action
(`Langlands.NYLL.ClassFormation.relativeCosetAction`): the value at the coset
`q` of the fixed coefficient attached to `x` by the published fixed-unit
equivalence, computed through `galoisAmbientUnitsRep K Ω`, the Galois action
on `Ωˣ`. The right side applies to `x` the automorphism of `E/K` that the
published equivalence `baseFixingExtensionQuotientEquivGaloisGroup K Ω E`
attaches to `q`, and includes the result into `Ω`. The statement says that the
abstract coset action on `Eˣ` is the ordinary Galois action of `Gal(E/K)`.

## Implemented proof

The complete proof body is

```lean
  unfold relativeCosetAction_intermediateFieldUnit_valStatement
  refine Quotient.inductionOn' q ?_
  intro σ
  rw [relativeCosetAction_mk (hLK := fixingSubgroupLeBase K Ω E)]
  change σ.1 (E.val (x : E)) =
    E.val ((baseFixingExtensionQuotientEquivGaloisGroup K Ω E
      (QuotientGroup.mk' _ σ)) (x : E))
  have hq :
      baseFixingExtensionQuotientEquivAmbient K Ω E
          (QuotientGroup.mk' _ σ) =
        QuotientGroup.mk' (closedFixingSubgroup K Ω E).toSubgroup σ.1 := by
    rfl
  have hn := InfiniteGalois.normalAutEquivQuotient_apply
    (closedFixingSubgroup K Ω E) σ.1
  change InfiniteGalois.normalAutEquivQuotient (closedFixingSubgroup K Ω E)
      (QuotientGroup.mk' _ σ.1) = _ at hn
  rw [baseFixingExtensionQuotientEquivGaloisGroup, MulEquiv.trans_apply, hq,
    MulEquiv.trans_apply, hn, AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, IntermediateField.equivOfEq_symm,
    IntermediateField.equivOfEq_apply]
  change σ.1 (E.val (x : E)) =
    (((AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) σ.1)
      ⟨E.val (x : E), _⟩ : IntermediateField.fixedField
        (closedFixingSubgroup K Ω E).toSubgroup) : Ω)
  rw [AlgEquiv.restrictNormalHom_apply]
```

Step by step:

1. `unfold` replaces the published proposition by the equation displayed
   above, so that the later rewrites can see its terms.
2. `Quotient.inductionOn'` reduces the claim to cosets of a representative
   `σ` of the closed fixing subgroup of `⊥`, which is a subgroup of
   `Gal(Ω/K)`; `intro σ` introduces it.
3. The published `relativeCosetAction_mk`
   (`Langlands.NYLL.ClassFormation.relativeCosetAction_mk`, M024.002),
   whose statement unfolds to
   `relativeCosetAction A K L hLK a (QuotientGroup.mk k) = A.ρ k.1 a.1`,
   rewrites the left side to the Galois action of `σ.1` on the fixed
   coefficient of `x`. The first `change` records that this is
   `σ.1 (E.val x)` definitionally (the coefficient is the inclusion of `x`
   into `Ωˣ`, and `galoisAmbientUnitsRep` acts by applying the automorphism),
   and writes the coset as `QuotientGroup.mk' _ σ`.
4. `hq`, proved by `rfl`, says that the published quotient equivalence
   `baseFixingExtensionQuotientEquivAmbient K Ω E` sends this coset to the
   coset of `σ.1` in `Gal(Ω/K) ⧸ Gal(Ω/E)`.
5. `hn` is Mathlib's `InfiniteGalois.normalAutEquivQuotient_apply` for the
   normal closed subgroup `closedFixingSubgroup K Ω E`: the canonical
   isomorphism `Gal(Ω/K) ⧸ H ≃* Gal(fixedField H / K)` sends the coset of
   `σ.1` to `AlgEquiv.restrictNormalHom (fixedField H) σ.1`. The `change ...
   at hn` writes its left side with `QuotientGroup.mk'`.
6. Unfolding `baseFixingExtensionQuotientEquivGaloisGroup`, which is the
   composite of `baseFixingExtensionQuotientEquivAmbient`,
   `InfiniteGalois.normalAutEquivQuotient` and `AlgEquiv.autCongr` of
   `IntermediateField.equivOfEq (InfiniteGalois.fixedField_fixingSubgroup E)`,
   the rewrites with `MulEquiv.trans_apply`, `hq`, `hn` and
   `AlgEquiv.autCongr_apply` turn the right side into the conjugate of the
   restriction of `σ.1` by that `equivOfEq`.
7. `simp only` with `AlgEquiv.trans_apply`,
   `IntermediateField.equivOfEq_symm` and `IntermediateField.equivOfEq_apply`
   evaluates the conjugation: transporting `x` to the fixed field of
   `Gal(Ω/E)` and back does not change its value in `Ω`. The second `change`
   displays the right side as the value in `Ω` of
   `AlgEquiv.restrictNormalHom (fixedField (closedFixingSubgroup K Ω E)) σ.1`
   at the element `⟨E.val x, _⟩`.
8. Mathlib's `AlgEquiv.restrictNormalHom_apply`, which states
   `restrictNormalHom L σ x = σ x` (as elements of the ambient field), turns
   the right side into `σ.1 (E.val x)` and closes the goal.

Steps 2 and 4–8 are the original proof verbatim. There are two adaptations,
both forced by the Library's presentation of published source declarations
through `...Statement` propositions. The initial `unfold` exposes the stated
equation, which the source theorem has directly. In step 3 the source writes
`rw [relativeCosetAction_mk]`; in the Library the argument
`fixingSubgroupLeBase K Ω E` of `relativeCosetAction` in the goal is a
theorem whose type is the published `fixingSubgroupLeBaseStatement K Ω E`,
which matches the hypothesis type `L.toSubgroup ≤ K.toSubgroup` of
`relativeCosetAction_mk` only after unfolding that proposition, so the
rewrite's pattern search does not unify it with a metavariable. Supplying it
as the named argument `hLK := fixingSubgroupLeBase K Ω E` makes the pattern
contain the same term as the goal; the rewrite and everything after it then
proceed as in the source. No auxiliary declaration, extra hypothesis,
instance or `simp` registration is introduced. The development check reports
no warnings and only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_valStatement`
  in SeparableUnitsNorm.BaseUnits.Statements.
- The published theorem `Langlands.NYLL.ClassFormation.relativeCosetAction_mk`
  in AbstractClassFieldTheory.Degree.Norm.U002.Proofs, with its proposition
  `relativeCosetAction_mkStatement` and the definition
  `relativeCosetAction` (AbstractClassFieldTheory.Degree.Norm.Statements and
  Definitions).
- The published definitions `baseFixingExtensionQuotientEquivGaloisGroup` and
  `baseFixingExtensionQuotientEquivAmbient`
  (GaloisExtensionQuotient.Quotient.Definitions), unfolded in the proof, with
  `baseFixingToAmbientQuotient` and the instance
  `closedFixingSubgroup_normal` (GaloisExtensionQuotient.Initial.Definitions)
  that they use, and the published theorem `fixingSubgroupLeBase`
  (GaloisExtensionQuotient.Initial.U002.Proofs).
- The published `intermediateFieldUnitsEquivGaloisFixed`
  (AbsoluteUnitsFixedField.FixedUnitsEquiv.Definitions),
  `intermediateFieldUnitsToGaloisAmbient` and `galoisAmbientUnitsRep`
  (AbsoluteUnitsFixedField.Initial.Definitions),
  `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` and
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup`, unfolded
  definitionally in the first `change`.
- Mathlib's `Quotient.inductionOn'`, `QuotientGroup.mk'`,
  `MulEquiv.trans_apply`, `InfiniteGalois.normalAutEquivQuotient` and
  `InfiniteGalois.normalAutEquivQuotient_apply`
  (`Mathlib/FieldTheory/Galois/Infinite.lean`), `AlgEquiv.autCongr_apply` and
  `AlgEquiv.trans_apply` (`Mathlib/Algebra/Algebra/Equiv.lean`),
  `IntermediateField.equivOfEq_symm` and `IntermediateField.equivOfEq_apply`
  (`Mathlib/FieldTheory/IntermediateField/Basic.lean`) and
  `AlgEquiv.restrictNormalHom_apply` (`Mathlib/FieldTheory/Normal/Defs.lean`).

No other proof and no host class-formation or reciprocity theorem is used.
The coercion law M088.007 is not cited; its definitional content is used
inside the first `change`.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:75–117`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean#L75-L117).
Line 75 is the retained `omit [FiniteDimensional K E] in`, 76 the source
docstring, 77–91 the signature and 92–117 the proof; the
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m096)
places this proof at M096.004 (source unit lines 77–120, ending before the
next unit M096.005 at line 121) after M096.003.END. The section variables are
`(K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]` at
lines 36–37 and, in section `FiniteGaloisIntermediate` (line 60),
`(E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]` at
line 62. The whole-file SHA-256 is
`b725f9b453be02ebc61de24d8c9a3f32b87f438471b2423357c1edf54a76fcaa`,
recomputed by Worker 96 on 15 November 2026 UTC from the retained snapshot.

| Original | Adapted |
| --- | --- |
| Asserted type of `LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val` (M096.004) | Published `Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_valStatement` in SeparableUnitsNorm.BaseUnits.Statements |
| Proof `LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val` | This theorem `Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_val` in SeparableUnitsNorm.BaseUnits.U004.Proofs |
| `ClassFormation.relativeCosetAction_mk` (M024.002) | Published `Langlands.NYLL.ClassFormation.relativeCosetAction_mk` |
| `LocalClassFieldTheory.baseFixingExtensionQuotientEquivGaloisGroup`, `baseFixingExtensionQuotientEquivAmbient` | Published declarations of the same names under `Langlands.NYLL.LocalClassFieldTheory` |
| `LocalClassFieldTheory.fixingSubgroupLeBase` | Published theorem of the same name, typed by `fixingSubgroupLeBaseStatement` |
| Instance `baseFixingExtensionQuotient_finite` (M096.003) | Not used |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the published Statements module and the published proof
module of `relativeCosetAction_mk`, opens only `RamificationTheory`,
`ClassFormation` and `CyclicCohomology` (the source also opens
`KummerTheory`, `LocalFieldTheory`, `BigOperators` and a
`noncomputable section`, unused here), keeps the source section variables and
`omit` clause, states the theorem's type as the published proposition applied
to `K Ω E x q`, and makes the two proof adaptations described above.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 96's dated modification
record. Worker 96 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors.

The unchanged inherited
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M096.004. The finiteness instance M096.003, the
relative-norm comparisons M096.005 onward, the coercion law M088.007, the
value law M096.002 and any host class-formation, cup, transfer, Tate or
reciprocity target are separate work.
