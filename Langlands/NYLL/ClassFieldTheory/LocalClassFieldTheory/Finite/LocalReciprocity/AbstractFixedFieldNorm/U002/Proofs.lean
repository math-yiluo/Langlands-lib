/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 731, 15 November 2026: adapt the source theorems
LocalClassFieldTheory.normToBase_abstractFixedFieldUnit_val_of_isSeparable
(inventory M166.002, lines 65–106),
LocalClassFieldTheory.localBaseValuation_normToBase_abstractFixedFieldUnit
(M166.003, lines 108–170) and
LocalClassFieldTheory.localBaseValuation_comp_normToBase_range_eq_residueFinrank
(M166.004, lines 172–277) of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709 to prove the
published targets with the suffix Statement; prefix the namespace with
Langlands.NYLL; write the section variables of M166.002 as explicit binders;
begin each proof with `unfold` of its target; in M166.003 replace the
rewrite by the unpublished M092.003 normUnits_apply_coe with `rfl`; in
M166.004 prove the unpublished M025.005 mem_nsmulImage_iff in place by
`Iff.rfl`, drop the local `let f`, obtain the norm valuation identity
by unfolding the published M162.019 statement and rewriting `v` into
`valuationMap` with the published valuationMap_apply, and close each
inclusion by rewriting with map_nsmul and nsmul_eq_mul (the second also
with hwz and a final `rfl`) instead of the source's `congr 1` and `calc`;
replace the source imports by the published modules used. The remaining
tactic steps are the source's. The retained license and notice are
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldNorm.U002.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldNorm.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnitsEquiv.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Initial.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.U002.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.HenselianValuationBase.U004.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U019.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U005.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U004.Proofs

/-!
# Finite local reciprocity: the norm of a finite abstract field

The proofs of the NYLL M166.002, M166.003 and M166.004 theorems for the
exact published targets. NYLL's `valuationMap` is the negative of the usual
normalized order: a prime element has value `-1`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology KummerTheory ClassFormation

open LocalFieldTheory

noncomputable section

open scoped ValuativeRel

/-- For an arbitrary finite separable abstract field, the abstract class-formation norm on
fixed coefficients has the same underlying field element as the ordinary
field norm from its concrete fixed field. -/
theorem normToBase_abstractFixedFieldUnit_val_of_isSeparable
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (H : ClosedSubgroup (Gal(Ω/K)))
    [Finite ((baseField (Gal(Ω/K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/K))) H (le_baseField H))]
    [FiniteDimensional K (abstractFixedField K Ω H)]
    [Algebra.IsSeparable K (abstractFixedField K Ω H)]
    (x : (abstractFixedField K Ω H)ˣ) :
    normToBase_abstractFixedFieldUnit_val_of_isSeparableStatement K Ω H x := by
  unfold normToBase_abstractFixedFieldUnit_val_of_isSeparableStatement
  let E := abstractFixedField K Ω H
  let y : ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω) H :=
    abstractFixedFieldUnitsEquivGaloisFixed K Ω H (Additive.ofMul x)
  let yE := intermediateFieldUnitsEquivGaloisFixed K Ω E (Additive.ofMul x)
  have hy : yE.1 = y.1 := by
    rw [intermediateFieldUnitsEquivGaloisFixed_coe]
    exact (abstractFixedFieldUnitsEquivGaloisFixed_coe
      K Ω H (Additive.ofMul x)).symm
  have hnorm :=
    relativeNorm_intermediateFieldUnit_val_of_isSeparable K Ω E x
  have htransport := relativeNorm_coe_eq_of_closedSubgroup_eq
    (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (baseField (Gal(Ω / K)))
    (closedFixingSubgroup K Ω E) H
    (fixingSubgroupLeBase K Ω E) (le_baseField H)
    (closedFixingSubgroup_bot_eq_baseField K Ω)
    (closedFixingSubgroup_abstractFixedField_eq K Ω H)
    yE y hy
  have htransport' := congrArg
    (fun z : Additive Ωˣ => ((Additive.toMul z : Ωˣ) : Ω)) htransport
  change
    ((Additive.toMul
      ((normToBase (galoisAmbientUnitsRep K Ω) H y).1 :
        Additive Ωˣ) : Ωˣ) : Ω) = _
  exact htransport'.symm.trans hnorm

/-- The base normalized valuation of the abstract norm is the ordinary
normalized valuation of the concrete field norm. -/
theorem localBaseValuation_normToBase_abstractFixedFieldUnit
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K)))
    [Finite ((baseField (Gal(SeparableClosure K/K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(SeparableClosure K/K))) H
        (le_baseField H))]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ) :
    localBaseValuation_normToBase_abstractFixedFieldUnitStatement K H x := by
  unfold localBaseValuation_normToBase_abstractFixedFieldUnitStatement
  let E := abstractFixedField K (SeparableClosure K) H
  let a := normToBase
    (galoisAmbientUnitsRep K (SeparableClosure K)) H
    (abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H (Additive.ofMul x))
  have ha : (baseFieldUnitsEquiv K).symm a =
      Additive.ofMul (normUnits K E x) := by
    apply (baseFieldUnitsEquiv K).injective
    rw [(baseFieldUnitsEquiv K).apply_symm_apply]
    apply Subtype.ext
    apply Additive.ext
    apply Units.ext
    calc
      ((Additive.toMul
          ((normToBase
            (galoisAmbientUnitsRep K (SeparableClosure K)) H
            (abstractFixedFieldUnitsEquivGaloisFixed
              K (SeparableClosure K) H (Additive.ofMul x))).1 :
              Additive (SeparableClosure K)ˣ) :
            (SeparableClosure K)ˣ) : SeparableClosure K) =
          algebraMap K (SeparableClosure K)
            (Algebra.norm K (x : E)) :=
        normToBase_abstractFixedFieldUnit_val_of_isSeparable
          K (SeparableClosure K) H x
      _ = algebraMap K (SeparableClosure K)
          ((normUnits K E x : Kˣ) : K) := by
        -- Source: `rw [LocalFieldTheory.normUnits_apply_coe]` (M092.003,
        -- whose proof is unpublished); the two sides agree by definition.
        rfl
      _ =
          ((Additive.toMul
            ((baseFieldUnitsEquiv K
              (Additive.ofMul (normUnits K E x))).1 :
                Additive (SeparableClosure K)ˣ) :
              (SeparableClosure K)ˣ) : SeparableClosure K) :=
        (baseFieldUnitsEquiv_val K (normUnits K E x)).symm
  rw [show normToBase
      (galoisAmbientUnitsRep K (SeparableClosure K)) H
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H (Additive.ofMul x)) = a from rfl]
  change Int.castRingHom ZHat
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
        ((baseFieldUnitsEquiv K).symm a)) = _
  rw [ha]

/-- For an arbitrary finite separable abstract field, the image of the
base valuation after the abstract class-formation norm is exactly the actual residue-degree
multiple of the base value group. -/
theorem localBaseValuation_comp_normToBase_range_eq_residueFinrank
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K)))
    [Finite ((baseField (Gal(SeparableClosure K/K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(SeparableClosure K/K))) H
        (le_baseField H))]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    [ValuativeRel (abstractFixedField K (SeparableClosure K) H)]
    [TopologicalSpace (abstractFixedField K (SeparableClosure K) H)]
    [IsNonarchimedeanLocalField
      (abstractFixedField K (SeparableClosure K) H)]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation
        (abstractFixedField K (SeparableClosure K) H))]
    [hIntegralClosure : IsIntegralClosure
      𝒪[abstractFixedField K (SeparableClosure K) H] 𝒪[K]
      (abstractFixedField K (SeparableClosure K) H)] :
    localBaseValuation_comp_normToBase_range_eq_residueFinrankStatement K H := by
  unfold localBaseValuation_comp_normToBase_range_eq_residueFinrankStatement
  -- Source M025.005 `mem_nsmulImage_iff` (its proof is unpublished), proved
  -- here by `Iff.rfl`; the source proof is `rfl`.
  have mem_nsmulImage_iff (Z : AddSubgroup ZHat) (n : ℕ) (z : ZHat) :
      z ∈ nsmulImage Z n ↔ ∃ x ∈ Z, n • x = z := Iff.rfl
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    let x : Additive
        (abstractFixedField K (SeparableClosure K) H)ˣ :=
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H).symm a
    have hxa : abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H x = a :=
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H).apply_symm_apply a
    rw [← hxa]
    change localBaseValuation K
      (normToBase (galoisAmbientUnitsRep K (SeparableClosure K)) H
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H
            (Additive.ofMul (Additive.toMul x)))) ∈ _
    rw [localBaseValuation_normToBase_abstractFixedFieldUnit]
    have hnorm :=
      @v_normUnits_eq_residue_finrank_mul_of_isSeparable
        K (abstractFixedField K (SeparableClosure K) H)
          _ _ _ _ _ _ _ _ _ _ _ _ hIntegralClosure (Additive.toMul x)
    have hnorm' := hnorm
    unfold v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement at hnorm'
    rw [← IsNonarchimedeanLocalField.valuationMap_apply,
      ← IsNonarchimedeanLocalField.valuationMap_apply, ofMul_toMul] at hnorm'
    rw [hnorm', mem_nsmulImage_iff]
    refine ⟨Int.castRingHom ZHat
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
          (abstractFixedField K (SeparableClosure K) H) x),
      intToProCInteger_mem_localBaseValuation_range K _, ?_⟩
    rw [← map_nsmul, nsmul_eq_mul]
  · rw [mem_nsmulImage_iff]
    rintro ⟨w, hw, hwz⟩
    rw [localBaseValuation_range K] at hw
    obtain ⟨m, rfl⟩ := hw
    obtain ⟨x, hx⟩ :=
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective
        (abstractFixedField K (SeparableClosure K) H) m
    refine ⟨abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H x, ?_⟩
    change localBaseValuation K
      (normToBase (galoisAmbientUnitsRep K (SeparableClosure K)) H
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H
            (Additive.ofMul (Additive.toMul x)))) = z
    rw [localBaseValuation_normToBase_abstractFixedFieldUnit]
    have hnorm :=
      @v_normUnits_eq_residue_finrank_mul_of_isSeparable
        K (abstractFixedField K (SeparableClosure K) H)
          _ _ _ _ _ _ _ _ _ _ _ _ hIntegralClosure (Additive.toMul x)
    have hnorm' := hnorm
    unfold v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement at hnorm'
    rw [← IsNonarchimedeanLocalField.valuationMap_apply,
      ← IsNonarchimedeanLocalField.valuationMap_apply, ofMul_toMul] at hnorm'
    rw [hnorm', hx, ← hwz, ← map_nsmul, nsmul_eq_mul]
    rfl

end

end Langlands.NYLL.LocalClassFieldTheory
