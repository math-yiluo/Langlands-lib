/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 15 November 2026:
Extract the proofs of M163.004 (lines 49–63), M163.006 (73–79), M163.007
(81–95), M163.008 (97–102), M163.010 (110–119), M163.011 (121–154) and
M163.013 (167–189) of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
HenselianValuationBase.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and keep the source opens (lines 21–26). Import the
published U004 Statements module and the published proofs of M096.002
(baseUnitsEquivGaloisAmbientFixed_val), M134.005 (valuationMap_surjective)
and M009.007 (zHatReduction_int) instead of the source imports. State each
theorem as the published closed proposition, introduce its binders (the
source section variables, then the theorem's own binders; in M163.010 the
source `intro a` joins this `intro`) and then run the source proof. The
source names inside the proofs denote the closed theorems
of this file and the published theorems above. One step changes: in
M163.011 the source `rw [← hm, zHatReduction_int] at hz0; exact hz0` is
replaced by `rw [← hm] at hz0` followed by the equation
`(zHatReduction_int n hn m).symm` composed with `hz0`, because the equation
of the published zHatReduction_int has the left side
`zHatReduction n hn (m : ZHat)` (Int.cast), so `rw` finds no occurrence of it
in `zHatReduction n hn (Int.castRingHom ZHat m)`; the two left sides are
definitionally equal. The source `@[simp]` attributes of M163.004 and M163.006 are not
put on the closed theorems, where they would not give usable simp lemmas;
the source simp behavior is restored by two explicit-telescope `@[simp]`
wrappers with the suffix `_apply`, derived from the exact closed theorems.
Omit the source noncomputable section and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.HenselianValuationBase.U004.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.U002.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U005.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U007.Proofs

/-!
# Finite local reciprocity: the base value group in `ℤ̂`, proofs

The fixed coefficient of a unit `x` of a nonarchimedean local field `K` is
`x` in the separable closure; the transported valuation takes NYLL's
`valuationMap` value there; its range is the image of `ℤ` in `ℤ̂`, which
contains every integer; and reduction modulo a positive `n` on that value
group is surjective with kernel `n` times the value group, so the canonical
map from the value group modulo `n` to `ZMod n` is bijective.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory KummerTheory

open LocalFieldTheory

open ClassFormation

/-- States the theorem `baseFieldUnitsEquiv_val`. -/
theorem baseFieldUnitsEquiv_val : baseFieldUnitsEquiv_valStatement := by
  intro K _ x
  change
    ((Additive.toMul
      ((baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul x)).1 :
        Additive (SeparableClosure K)ˣ) : (SeparableClosure K)ˣ) :
      SeparableClosure K) = algebraMap K (SeparableClosure K) (x : K)
  exact baseUnitsEquivGaloisAmbientFixed_val K (SeparableClosure K) x

/-- Explicit-telescope simp form of `baseFieldUnitsEquiv_val`. -/
@[simp]
theorem baseFieldUnitsEquiv_val_apply (K : Type) [Field K] (x : Kˣ) :
    ((Additive.toMul
      ((baseFieldUnitsEquiv K (Additive.ofMul x)).1 :
        Additive (SeparableClosure K)ˣ) : (SeparableClosure K)ˣ) :
      SeparableClosure K) = algebraMap K (SeparableClosure K) (x : K) :=
  baseFieldUnitsEquiv_val K x

/-- States the theorem `localBaseValuation_baseFieldUnitsEquiv`. -/
theorem localBaseValuation_baseFieldUnitsEquiv :
    localBaseValuation_baseFieldUnitsEquivStatement := by
  intro K _ _ _ _ x
  simp [localBaseValuation]

/-- Explicit-telescope simp form of `localBaseValuation_baseFieldUnitsEquiv`. -/
@[simp]
theorem localBaseValuation_baseFieldUnitsEquiv_apply (K : Type) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Additive Kˣ) :
    localBaseValuation K (baseFieldUnitsEquiv K x) =
      Int.castRingHom ZHat
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x) :=
  localBaseValuation_baseFieldUnitsEquiv K x

/-- The value group is exactly the image of the ordinary integers in the
profinite integers. -/
theorem localBaseValuation_range : localBaseValuation_rangeStatement := by
  intro K _ _ _ _
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨IsNonarchimedeanLocalField.valuationMap K
      ((baseFieldUnitsEquiv K).symm x), rfl⟩
  · rintro z ⟨m, rfl⟩
    obtain ⟨x, hx⟩ :=
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective K m
    refine ⟨baseFieldUnitsEquiv K x, ?_⟩
    rw [localBaseValuation_baseFieldUnitsEquiv, hx]
    rfl

/-- Every ordinary integer occurs as a value, as required in the Henselian valuation condition. -/
theorem intToProCInteger_mem_localBaseValuation_range :
    intToProCInteger_mem_localBaseValuation_rangeStatement := by
  intro K _ _ _ _ m
  rw [localBaseValuation_range]
  exact ⟨m, rfl⟩

/-- States the theorem `localValueGroupReduction_surjective`. -/
theorem localValueGroupReduction_surjective :
    localValueGroupReduction_surjectiveStatement := by
  intro K _ _ _ _ n hn a
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
  let z : (localBaseValuation K).range :=
    ⟨Int.castRingHom ZHat m,
      intToProCInteger_mem_localBaseValuation_range K m⟩
  refine ⟨z, ?_⟩
  exact zHatReduction_int n hn m

/-- The kernel of reduction on the value group is precisely `nZ`. -/
theorem localValueGroupReduction_ker : localValueGroupReduction_kerStatement := by
  intro K _ _ _ _ n hn
  apply le_antisymm
  · intro z hz
    have hzInt : (z : ZHat) ∈
        (Int.castRingHom ZHat).toAddMonoidHom.range := by
      rw [← localBaseValuation_range K]
      exact z.property
    obtain ⟨m, hm⟩ := hzInt
    change Int.castRingHom ZHat m = (z : ZHat) at hm
    have hmod : (m : ZMod n) = 0 := by
      have hz0 : localValueGroupReduction K n hn z = 0 := hz
      change zHatReduction n hn (z : ZHat) = 0 at hz0
      -- Adapted: the source `rw [← hm, zHatReduction_int] at hz0; exact hz0`.
      rw [← hm] at hz0
      exact (Eq.symm (zHatReduction_int n hn m)).trans hz0
    have hdiv : (n : ℤ) ∣ m := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hmod
    obtain ⟨k, hk⟩ := hdiv
    let w : (localBaseValuation K).range :=
      ⟨Int.castRingHom ZHat k,
        intToProCInteger_mem_localBaseValuation_range K k⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change n • Int.castRingHom ZHat k = (z : ZHat)
    rw [← map_nsmul]
    have hnk : n • k = m := by
      simpa [nsmul_eq_mul] using hk.symm
    rw [hnk, hm]
  · rintro z ⟨w, rfl⟩
    change zHatReduction n hn (n • (w : ZHat)) = 0
    rw [map_nsmul]
    simp [nsmul_eq_mul]

/-- The inclusion-and-reduction quotient map of the Henselian valuation condition is
bijective for the actual local value group. -/
theorem localCanonicalValueQuotientMap_bijective :
    localCanonicalValueQuotientMap_bijectiveStatement := by
  intro K _ _ _ _ n hn
  constructor
  · intro q₁ q₂
    refine Quotient.inductionOn' q₁ ?_
    intro z₁
    refine Quotient.inductionOn' q₂ ?_
    intro z₂ h
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    rw [← localValueGroupReduction_ker K n hn]
    change localValueGroupReduction K n hn (z₁ - z₂) = 0
    rw [map_sub]
    change localValueGroupReduction K n hn z₁ =
      localValueGroupReduction K n hn z₂ at h
    rw [h, sub_self]
  · intro a
    obtain ⟨z, hz⟩ := localValueGroupReduction_surjective K n hn a
    refine ⟨QuotientAddGroup.mk'
      (nsmulWithin (localBaseValuation K).range n) z, ?_⟩
    exact hz

end Langlands.NYLL.LocalClassFieldTheory
