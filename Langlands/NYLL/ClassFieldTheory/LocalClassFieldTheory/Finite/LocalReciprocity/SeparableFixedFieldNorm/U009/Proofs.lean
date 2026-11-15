/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 731, 15 November 2026: adapt the source theorem
LocalClassFieldTheory.relativeNorm_intermediateFieldUnit_val_of_isSeparable
(inventory M165.009, lines 199–262 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709) to prove the
published target
Langlands.NYLL.LocalClassFieldTheory.relativeNorm_intermediateFieldUnit_val_of_isSeparableStatement;
prefix the namespace with Langlands.NYLL; write the section variables as
explicit binders; replace the source's private local instance
finiteSeparableAlgHomFintype (M165.007) by a local use of the published
instance Langlands.NYLL.PortInternal.M164.d001, which has the same body;
begin the proof with `unfold` of the target and replace the source step
`rw [relativeNormValue]` by `unfold relativeNormValue`; replace the source
imports by the published modules used. The rest of the tactic proof is the
source's. The retained license and notice are licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U009.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U005.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableNormProduct.U003.Proofs

/-!
# Norms from a finite separable intermediate field: the abstract norm is the field norm

The proof of the NYLL M165.009 theorem for the exact published target.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology ClassFormation

noncomputable section

open scoped BigOperators

section NormAsProduct

attribute [local instance] Langlands.NYLL.PortInternal.M164.d001

/-- For every finite separable intermediate field, including a nonnormal
one, the abstract class-formation left-coset norm is the ordinary field norm. -/
theorem relativeNorm_intermediateFieldUnit_val_of_isSeparable
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (E : IntermediateField K Ω)
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (x : Eˣ) :
    relativeNorm_intermediateFieldUnit_val_of_isSeparableStatement K Ω E x := by
  unfold relativeNorm_intermediateFieldUnit_val_of_isSeparableStatement
  let Q := (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup ⧸
    extensionSubgroup
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
  let := Fintype.ofFinite Q
  change
    ((Additive.toMul
      (relativeNormValue (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x))) : Ωˣ) : Ω) = _
  unfold relativeNormValue
  change
    (↑(Additive.toMul (∑ q : Q,
      relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q) : Ωˣ) : Ω) = _
  change (Units.coeHom Ω) (∏ q : Q,
    Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q)) = _
  rw [map_prod]
  change
    (∏ q : Q,
      ((Additive.toMul
        (relativeCosetAction (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
          (intermediateFieldUnitsEquivGaloisFixed K Ω E
            (Additive.ofMul x)) q) : Ωˣ) : Ω)) = _
  calc
    _ = ∏ σ : E →ₐ[K] Ω, σ (x : E) := by
      exact Fintype.prod_equiv
        (baseFixingCosetEquivAlgHom K Ω E)
        (fun q : Q =>
          ((Additive.toMul
            (relativeCosetAction (galoisAmbientUnitsRep K Ω)
              (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
              (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
              (intermediateFieldUnitsEquivGaloisFixed K Ω E
                (Additive.ofMul x)) q) : Ωˣ) : Ω))
        (fun σ : E →ₐ[K] Ω => σ (x : E))
        (relativeCosetAction_intermediateFieldUnit_val_of_isSeparable
          K Ω E x)
    _ = algebraMap K Ω (Algebra.norm K (x : E)) :=
      (algebraMap_norm_eq_prod_embeddings_of_isSepClosed
        K Ω E (x : E)).symm

end NormAsProduct

end

end Langlands.NYLL.LocalClassFieldTheory
