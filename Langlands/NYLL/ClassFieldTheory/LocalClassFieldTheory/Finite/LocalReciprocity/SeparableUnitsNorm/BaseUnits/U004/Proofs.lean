/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 96, 15 November 2026 UTC:
Extract only the proof of M096.004 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published SeparableUnitsNorm.BaseUnits
Statements module and the published proof module of relativeCosetAction_mk,
keep the source section variables and omit clause, open only the namespaces
the proof uses, and state the theorem as the published Statement applied to
the source parameters. The proof is the source proof line by line with two
adaptations: a first `unfold` of the published Statement, and the explicit
argument `hLK := fixingSubgroupLeBase K Ω E` in the rewrite with
relativeCosetAction_mk, needed because the Library types
fixingSubgroupLeBase through fixingSubgroupLeBaseStatement. The source
instance M096.003 is not used. The original LICENSE and NOTICE are retained
in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.U002.Proofs

/-!
# Relative coset action on intermediate-field units

The proof that the abstract relative coset action of a coset `q` on the fixed
coefficient of `x : Eˣ` is the action on `x` of the Galois automorphism of
`E/K` corresponding to `q`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory ClassFormation CyclicCohomology

variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

section FiniteGaloisIntermediate

variable (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]

omit [FiniteDimensional K E] in
/-- The relative coset action on the fixed coefficient of an intermediate-field
unit is the corresponding Galois action on that unit. -/
theorem relativeCosetAction_intermediateFieldUnit_val
    (x : Eˣ)
    (q : (closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E)
        (fixingSubgroupLeBase K Ω E)) :
    relativeCosetAction_intermediateFieldUnit_valStatement K Ω E x q := by
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

end FiniteGaloisIntermediate

end Langlands.NYLL.LocalClassFieldTheory
