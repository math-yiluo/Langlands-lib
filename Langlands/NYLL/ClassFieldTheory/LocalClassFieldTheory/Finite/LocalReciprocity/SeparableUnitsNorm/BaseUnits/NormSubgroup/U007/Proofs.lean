/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Norm.Transitivity
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.NormSubgroup.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.U004.Proofs

/-!
# The finite norm subgroup is the additive field-norm subgroup

Modified by Worker 290, 16 November 2026: extract the proof of M096.007
from `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean`
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, use the focused published statement and M096.004 proof
imports, and unfold the target at the start. M096.005 and M096.006 are not
published at this Library base, so retain their source arguments only as
private lemmas `normValueForSubgroup` and `normForSubgroup`; replace
`rw [relativeNormValue]` by `unfold relativeNormValue`. The subgroup proof
is otherwise unchanged. No theorem under a sibling's adapted name is added.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory KummerTheory LocalFieldTheory ClassFormation CyclicCohomology

noncomputable section

open scoped BigOperators

variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]
variable (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]

/-- Private source M096.005 calculation: coset products give the field norm. -/
private theorem normValueForSubgroup (x : Eˣ) :
    ((Additive.toMul
      ((relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
      algebraMap K Ω (Algebra.norm K (x : E)) := by
  let Q := (closedFixingSubgroup K Ω
      (⊥ : IntermediateField K Ω)).toSubgroup ⧸
    extensionSubgroup
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E)
      (fixingSubgroupLeBase K Ω E)
  let := Fintype.ofFinite Q
  change
    ((Additive.toMul
      (relativeNormValue (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x))) : Ωˣ) : Ω) = _
  unfold relativeNormValue
  let action : Q → Additive Ωˣ := fun q =>
    relativeCosetAction (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
      (intermediateFieldUnitsEquivGaloisFixed K Ω E
        (Additive.ofMul x)) q
  change (↑(Additive.toMul (∑ q : Q, action q)) : Ω) = _
  rw [toMul_sum]
  change (Units.coeHom Ω) (∏ q : Q, Additive.toMul (action q)) = _
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
    _ = ∏ σ : Gal(E / K), E.val (σ (x : E)) := by
      exact Fintype.prod_equiv
        (baseFixingExtensionQuotientEquivGaloisGroup K Ω E).toEquiv
        (fun q : Q => ((Additive.toMul (action q) : Ωˣ) : Ω))
        (fun σ : Gal(E / K) => E.val (σ (x : E)))
        (relativeCosetAction_intermediateFieldUnit_val K Ω E x)
    _ = E.val (algebraMap K E (Algebra.norm K (x : E))) := by
      rw [Algebra.norm_eq_prod_automorphisms, map_prod]
    _ = algebraMap K Ω (Algebra.norm K (x : E)) := rfl

/-- Private source M096.006 comparison in the fixed coefficient group. -/
private theorem normForSubgroup (x : Eˣ) :
    relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) =
      baseUnitsEquivGaloisAmbientFixed K Ω
        (Additive.ofMul (normUnits K E x)) := by
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  exact normValueForSubgroup K Ω E x

/-- Under the base-field fixed-unit equivalence, the abstract finite norm
subgroup is exactly the ordinary field-norm subgroup. -/
theorem map_finiteNormSubgroup_eq_additiveNormSubgroup :
    map_finiteNormSubgroup_eq_additiveNormSubgroupStatement K Ω E := by
  unfold map_finiteNormSubgroup_eq_additiveNormSubgroupStatement
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨b, rfl⟩
    let u : Eˣ := Additive.toMul
      ((intermediateFieldUnitsEquivGaloisFixed K Ω E).symm b)
    have hb :
        intermediateFieldUnitsEquivGaloisFixed K Ω E
            (Additive.ofMul u) = b := by
      change intermediateFieldUnitsEquivGaloisFixed K Ω E
          ((intermediateFieldUnitsEquivGaloisFixed K Ω E).symm b) = b
      exact (intermediateFieldUnitsEquivGaloisFixed K Ω E).apply_symm_apply b
    rw [← hb, normForSubgroup]
    change (baseUnitsEquivGaloisAmbientFixed K Ω).symm
      (baseUnitsEquivGaloisAmbientFixed K Ω
        (Additive.ofMul (normUnits K E u))) ∈ additiveNormSubgroup K E
    rw [(baseUnitsEquivGaloisAmbientFixed K Ω).symm_apply_apply]
    exact ⟨u, rfl⟩
  · intro hy
    change Additive.toMul y ∈ localNormSubgroup K E at hy
    rcases hy with ⟨u, hu⟩
    refine ⟨baseUnitsEquivGaloisAmbientFixed K Ω
      (Additive.ofMul (normUnits K E u)), ?_, ?_⟩
    · refine ⟨intermediateFieldUnitsEquivGaloisFixed K Ω E
        (Additive.ofMul u), ?_⟩
      exact normForSubgroup K Ω E u
    · change (baseUnitsEquivGaloisAmbientFixed K Ω).symm
        (baseUnitsEquivGaloisAmbientFixed K Ω
          (Additive.ofMul (normUnits K E u))) = y
      rw [(baseUnitsEquivGaloisAmbientFixed K Ω).symm_apply_apply]
      exact congrArg Additive.ofMul hu

end

end Langlands.NYLL.LocalClassFieldTheory
