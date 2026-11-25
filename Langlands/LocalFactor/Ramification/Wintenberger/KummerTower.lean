import Langlands.LocalFactor.Ramification.Wintenberger.APF
import Langlands.LocalFactor.Ramification.Herbrand.KummerTowerLimitUpperSupProof
import Langlands.Galois.Local.UnramifiedCriterionProof
import Langlands.ClassFieldTheory.Local.PrimeRamificationArithmeticSupport
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.Weil.Local.ExtensionResidue
import FontaineWintenberger.APF.Tower.Criterion
import FontaineWintenberger.Ramification.Lower.Degree
import Mathlib.Algebra.Module.Torsion.Field

/-!
# The Kummer tower is arithmetically profinite

For a `p`-adic field `F`, a uniformizer `ϖ` and a compatible system `πs` of its `p^n`-th roots,
the tower `L = ⋃ F(πs n)` is an infinite arithmetically profinite extension of `F` in the sense of
Wintenberger 1.2.1, and `ψ_{L/F}` is the identity on `(-∞, p e/(p - 1)]`.
-/

noncomputable section

namespace Langlands.Ramification.Wintenberger

open LocalClassField Polynomial Weil.Local
open Langlands.Ramification.Kummer (kummerBreak IsKummerRootSystem kummerStage kummerTower
  adjoinFiniteIntermediate)

universe u

variable {p : ℕ} [Fact p.Prime]

section Stage

variable (F : PadicField.{u} p) (K : PadicField.{u} p) [Algebra F.Carrier K.Carrier]
  [IsScalarTower (Padic p) F.Carrier K.Carrier] [FiniteDimensional F.Carrier K.Carrier]

/-- A root `β` of `X ^ (p ^ n) - ϖ`, for a uniformizer `ϖ` of `F`, in an extension of degree at
most `p ^ n` is a uniformizer, and the extension has absolute ramification index `p ^ n e_F`. -/
theorem ord_eq_one_and_ramificationIndex_of_pow_eq {ϖ : F.Carrier}
    (hϖ : F.canonicalTopologicalData.ord ϖ = 1) {n : ℕ} (β : K.Carrier)
    (hβ : β ^ (p ^ n) = algebraMap F.Carrier K.Carrier ϖ)
    (hdeg : Module.finrank F.Carrier K.Carrier ≤ p ^ n) :
    K.canonicalTopologicalData.ord β = 1 ∧
      K.canonicalTopologicalData.ramificationIndex =
        p ^ n * F.canonicalTopologicalData.ramificationIndex := by
  let T := F.canonicalTopologicalData
  let S := K.canonicalTopologicalData
  have hp : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  let f := IsScalarTower.toAlgHom (Padic p) F.Carrier K.Carrier
  have hdegreeIdentity := PadicField.ramificationIndex_mul_extensionResidueDegree F K f
  rw [extensionDegree_suppliedAlgebra] at hdegreeIdentity
  have hbound : S.ramificationIndex ≤ p ^ n * T.ramificationIndex := calc
    _ ≤ S.ramificationIndex * extensionResidueDegree F K f :=
      Nat.le_mul_of_pos_right _ (extensionResidueDegree_pos F K f)
    _ = Module.finrank F.Carrier K.Carrier * T.ramificationIndex := hdegreeIdentity
    _ ≤ _ := Nat.mul_le_mul_right _ hdeg
  have hord := ramificationIndex_mul_ord_relative_algebraMap F K T S ϖ
  rw [← hβ, Kummer.ord_pow, hϖ, mul_one, ← mul_assoc] at hord
  have hfactor : 0 < (T.ramificationIndex : ℤ) * ((p ^ n : ℕ) : ℤ) :=
    mul_pos (by exact_mod_cast T.ramificationIndex_pos) (by exact_mod_cast hp)
  have hpos : 0 < S.ord β := by
    apply (mul_pos_iff_of_pos_left hfactor).mp
    rw [hord]
    exact_mod_cast S.ramificationIndex_pos
  have hle : S.ord β ≤ 1 := by
    apply (mul_le_mul_iff_right₀ hfactor).mp
    rw [hord, mul_one, mul_comm]
    exact_mod_cast hbound
  have hβ1 : S.ord β = 1 := by omega
  refine ⟨hβ1, ?_⟩
  rw [hβ1, mul_one, mul_comm] at hord
  exact_mod_cast hord.symm

/-- Under the same hypotheses the degree is exactly `p ^ n`. -/
theorem finrank_eq_of_pow_eq {ϖ : F.Carrier} (hϖ : F.canonicalTopologicalData.ord ϖ = 1)
    {n : ℕ} (β : K.Carrier) (hβ : β ^ (p ^ n) = algebraMap F.Carrier K.Carrier ϖ)
    (hdeg : Module.finrank F.Carrier K.Carrier ≤ p ^ n) :
    Module.finrank F.Carrier K.Carrier = p ^ n := by
  obtain ⟨-, he⟩ := ord_eq_one_and_ramificationIndex_of_pow_eq F K hϖ β hβ hdeg
  let f := IsScalarTower.toAlgHom (Padic p) F.Carrier K.Carrier
  have hdegreeIdentity := PadicField.ramificationIndex_mul_extensionResidueDegree F K f
  rw [extensionDegree_suppliedAlgebra, he] at hdegreeIdentity
  have hT := F.canonicalTopologicalData.ramificationIndex_pos
  have hfpos := extensionResidueDegree_pos F K f
  have h1 : p ^ n ≤ Module.finrank F.Carrier K.Carrier := by
    have h2 : p ^ n * F.canonicalTopologicalData.ramificationIndex ≤
        Module.finrank F.Carrier K.Carrier * F.canonicalTopologicalData.ramificationIndex := by
      calc _ ≤ p ^ n * F.canonicalTopologicalData.ramificationIndex *
            extensionResidueDegree F K f := Nat.le_mul_of_pos_right _ hfpos
        _ = _ := hdegreeIdentity
    exact Nat.le_of_mul_le_mul_right h2 hT
  omega

end Stage


section Tower

variable (F : PadicField.{u} p)

local instance kummerPadicFieldCharZero : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

/-- The comparison of the algebraic closure with the separable closure of a `p`-adic field. -/
def sepClosureEquiv : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] SeparableClosure F.Carrier :=
  IsSepClosure.equiv F.Carrier (AlgebraicClosure F.Carrier) (SeparableClosure F.Carrier)

variable (πs : ℕ → AlgebraicClosure F.Carrier)

/-- The root `πs n`, in the separable closure. -/
def towerRoot (n : ℕ) : SeparableClosure F.Carrier := sepClosureEquiv F (πs n)

/-- The finite stage `F(πs n)`, in the separable closure. -/
def towerStage (n : ℕ) :
    FontaineWintenberger.FiniteIntermediateField F.Carrier (SeparableClosure F.Carrier) :=
  ⟨IntermediateField.adjoin F.Carrier {towerRoot F πs n},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)⟩

instance towerStage_finiteDimensional_padic (n : ℕ) :
    FiniteDimensional (Padic p) (towerStage F πs n).val :=
  FiniteDimensional.trans (Padic p) F.Carrier (towerStage F πs n).val

/-- The finite stage as a `p`-adic field with the same carrier. -/
abbrev towerStagePadic (n : ℕ) : PadicField.{u} p := PadicField.ofField (towerStage F πs n).val

instance towerStagePadic_algebra (n : ℕ) :
    Algebra F.Carrier (towerStagePadic F πs n).Carrier :=
  inferInstanceAs (Algebra F.Carrier (towerStage F πs n).val)

instance towerStagePadic_isScalarTower (n : ℕ) :
    IsScalarTower (Padic p) F.Carrier (towerStagePadic F πs n).Carrier :=
  inferInstanceAs (IsScalarTower (Padic p) F.Carrier (towerStage F πs n).val)

instance towerStagePadic_finiteDimensional (n : ℕ) :
    FiniteDimensional F.Carrier (towerStagePadic F πs n).Carrier :=
  inferInstanceAs (FiniteDimensional F.Carrier (towerStage F πs n).val)

/-- The generator of the stage. -/
abbrev towerStageRoot (n : ℕ) : (towerStage F πs n).val :=
  IntermediateField.AdjoinSimple.gen F.Carrier (towerRoot F πs n)

variable {F} {ϖ : F.Carrier}

theorem towerRoot_succ_pow (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
    towerRoot F πs (n + 1) ^ p = towerRoot F πs n := by
  simp only [towerRoot, ← map_pow, hπ.2.2 n]

theorem towerRoot_pow (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
    towerRoot F πs n ^ (p ^ n) = algebraMap F.Carrier (SeparableClosure F.Carrier) ϖ := by
  induction n with
  | zero =>
    simp only [pow_zero, pow_one, towerRoot, hπ.2.1, AlgEquiv.commutes]
  | succ n ih =>
    rw [pow_succ' p n, pow_mul, towerRoot_succ_pow πs hπ n, ih]

theorem towerStage_finrank_le (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
    Module.finrank F.Carrier (towerStage F πs n).val ≤ p ^ n := by
  have hp : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  change Module.finrank F.Carrier (IntermediateField.adjoin F.Carrier {towerRoot F πs n}) ≤ p ^ n
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := F.Carrier) _)]
  have hroot : aeval (towerRoot F πs n) (X ^ (p ^ n) - C ϖ) = 0 := by
    simpa only [map_sub, map_pow, aeval_X, aeval_C] using sub_eq_zero.mpr (towerRoot_pow πs hπ n)
  calc
    _ ≤ (X ^ (p ^ n) - C ϖ).natDegree :=
      natDegree_le_of_dvd (minpoly.dvd F.Carrier _ hroot) (monic_X_pow_sub_C ϖ hp.ne').ne_zero
    _ = _ := natDegree_X_pow_sub_C

theorem towerStageRoot_pow (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
    towerStageRoot F πs n ^ (p ^ n) = algebraMap F.Carrier (towerStage F πs n).val ϖ :=
  Subtype.ext (towerRoot_pow πs hπ n)

/-- The generator of each stage is a uniformizer, and the stage has absolute ramification index
`p ^ n e_F`. -/
theorem towerStage_ord_and_ramificationIndex (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
    (towerStagePadic F πs n).canonicalTopologicalData.ord (towerStageRoot F πs n) = 1 ∧
      (towerStagePadic F πs n).canonicalTopologicalData.ramificationIndex =
        p ^ n * F.canonicalTopologicalData.ramificationIndex :=
  ord_eq_one_and_ramificationIndex_of_pow_eq F (towerStagePadic F πs n) hπ.1
    (towerStageRoot F πs n) (towerStageRoot_pow πs hπ n) (towerStage_finrank_le πs hπ n)

theorem towerStage_finrank (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
    Module.finrank F.Carrier (towerStage F πs n).val = p ^ n :=
  finrank_eq_of_pow_eq F (towerStagePadic F πs n) hπ.1 (towerStageRoot F πs n)
    (towerStageRoot_pow πs hπ n) (towerStage_finrank_le πs hπ n)

theorem towerStage_le_succ (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
    towerStage F πs n ≤ towerStage F πs (n + 1) := by
  change IntermediateField.adjoin F.Carrier {towerRoot F πs n} ≤
    IntermediateField.adjoin F.Carrier {towerRoot F πs (n + 1)}
  rw [IntermediateField.adjoin_simple_le_iff, ← towerRoot_succ_pow πs hπ n]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _

theorem towerStage_strictMono (hπ : IsKummerRootSystem F ϖ πs) :
    StrictMono (towerStage F πs) := by
  apply strictMono_nat_of_lt_succ
  intro n
  refine lt_of_le_of_ne (towerStage_le_succ πs hπ n) fun h => ?_
  have h1 := towerStage_finrank πs hπ n
  have h2 := towerStage_finrank πs hπ (n + 1)
  rw [h] at h1
  rw [h1, pow_succ] at h2
  have hp := (Fact.out : p.Prime).one_lt
  have hpn : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  nlinarith

/-- The level of the `n`-th step: the first Kummer break of the stage. -/
def towerLevel (n : ℕ) : ℝ := kummerBreak (towerStagePadic F πs n)

theorem towerLevel_eq (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
    towerLevel πs n = (p : ℝ) ^ n * kummerBreak F := by
  unfold towerLevel kummerBreak
  rw [(towerStage_ord_and_ramificationIndex πs hπ n).2]
  push_cast
  ring

theorem kummerBreak_pos (F : PadicField.{u} p) : 0 < kummerBreak F := by
  unfold kummerBreak
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have he : (0 : ℝ) < F.canonicalTopologicalData.ramificationIndex := by
    exact_mod_cast F.canonicalTopologicalData.ramificationIndex_pos
  positivity

end Tower

section StepEmbedding

variable {F : PadicField.{u} p}

local instance kummerPadicFieldCharZero'' : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

variable (πs : ℕ → AlgebraicClosure F.Carrier) {ϖ : F.Carrier}

/-- The step `F(πs (n + 1)) / F(πs n)` embeds into an algebraic closure of its base, with image
generated by a `p`-th root of the stage generator. -/
theorem towerStep_exists_embedding (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
    ∃ (f : IntermediateField.extendScalars (towerStage_le_succ πs hπ n) →ₐ[(towerStage F πs n).val]
        AlgebraicClosure (towerStage F πs n).val) (α : AlgebraicClosure (towerStage F πs n).val),
      α ^ p = algebraMap (towerStage F πs n).val (AlgebraicClosure (towerStage F πs n).val)
        (towerStageRoot F πs n) ∧
      f.fieldRange = IntermediateField.adjoin (towerStage F πs n).val {α} := by
  have hEE' := towerStage_le_succ πs hπ n
  have halg : Algebra.IsAlgebraic (towerStage F πs n).val (SeparableClosure F.Carrier) :=
    Algebra.IsAlgebraic.tower_top (K := F.Carrier) (towerStage F πs n).val
  have htf : Module.IsTorsionFree (towerStage F πs n).val (SeparableClosure F.Carrier) :=
    DivisionSemiring.to_moduleIsTorsionFree
  have htf' : Module.IsTorsionFree (towerStage F πs n).val
      (AlgebraicClosure (towerStage F πs n).val) :=
    DivisionSemiring.to_moduleIsTorsionFree
  let g : SeparableClosure F.Carrier →ₐ[(towerStage F πs n).val]
      AlgebraicClosure (towerStage F πs n).val := IsAlgClosed.lift
  refine ⟨g.comp (IntermediateField.extendScalars hEE').val, g (towerRoot F πs (n + 1)), ?_, ?_⟩
  · rw [← map_pow, towerRoot_succ_pow πs hπ n]
    exact g.commutes (towerStageRoot F πs n)
  · have hL : IntermediateField.extendScalars hEE' =
        IntermediateField.adjoin (towerStage F πs n).val {towerRoot F πs (n + 1)} := by
      apply IntermediateField.restrictScalars_injective F.Carrier
      rw [IntermediateField.extendScalars_restrictScalars,
        IntermediateField.restrictScalars_adjoin_eq_sup]
      exact (sup_eq_right.mpr hEE').symm
    rw [← AlgHom.map_fieldRange, IntermediateField.fieldRange_val, hL,
      IntermediateField.adjoin_map, Set.image_singleton]

end StepEmbedding

section Steps

variable {F : PadicField.{u} p}

local instance kummerPadicFieldNormedField : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance kummerPadicFieldNormedAlgebra : NormedAlgebra (Padic p) F.Carrier :=
  F.canonicalNormedAlgebra
local instance kummerPadicFieldLocalField : FontaineWintenberger.IsPerfectResidueLocalField F.Carrier :=
  padicField_isPerfectResidueLocalField F
local instance kummerPadicFieldCharZero' : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

variable (πs : ℕ → AlgebraicClosure F.Carrier) {ϖ : F.Carrier}

/-- **Each step of the Kummer tower is elementary** in the sense of Wintenberger 1.3.1, of level
the first Kummer break of its base, for the spectral norm of the base. -/
theorem towerStep_isElementaryStep (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
    FontaineWintenberger.IsElementaryStep F.Carrier (towerStage F πs n)
      (towerStage F πs (n + 1)) (towerStage_le_succ πs hπ n) (towerLevel πs n) := by
  obtain ⟨f, α, hα, hf⟩ := towerStep_exists_embedding πs hπ n
  have hord := (towerStage_ord_and_ramificationIndex πs hπ n).1
  have hlevel := kummerBreak_pos (towerStagePadic F πs n)
  apply isElementaryStep_of_absoluteUpper (Padic p) (padicBaseNorm_compatible p) F.Carrier
    (towerStage F πs n) (towerStage F πs (n + 1)) (towerStage_le_succ πs hπ n)
    (AlgebraicClosure (towerStage F πs n).val) f hlevel
  · rw [hf]
    exact Kummer.kummerStepUpperSup p (towerStagePadic F πs n) (towerStageRoot F πs n) α hord hα
      (towerLevel πs n) (by unfold towerLevel; linarith) le_rfl
  · intro x hx
    rw [hf]
    exact Kummer.kummerStep_upper_le_fixingSubgroup (towerStagePadic F πs n) hord hα hx

end Steps

section Criterion

variable {F : PadicField.{u} p}

local instance kummerPadicFieldNormedField₂ : NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField
local instance kummerPadicFieldNormedAlgebra₂ : NormedAlgebra (Padic p) F.Carrier :=
  F.canonicalNormedAlgebra
local instance kummerPadicFieldLocalField₂ : FontaineWintenberger.IsPerfectResidueLocalField F.Carrier :=
  padicField_isPerfectResidueLocalField F
local instance kummerPadicFieldCharZero₂ : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

variable (πs : ℕ → AlgebraicClosure F.Carrier) {ϖ : F.Carrier}

theorem towerStage_zero (hπ : IsKummerRootSystem F ϖ πs) : (towerStage F πs 0).val = ⊥ := by
  change IntermediateField.adjoin F.Carrier {towerRoot F πs 0} = ⊥
  rw [IntermediateField.adjoin_simple_eq_bot_iff, towerRoot, hπ.2.1, AlgEquiv.commutes]
  exact IntermediateField.algebraMap_mem _ _

theorem towerLevel_strictMono (hπ : IsKummerRootSystem F ϖ πs) : StrictMono (towerLevel πs) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [towerLevel_eq πs hπ, towerLevel_eq πs hπ, pow_succ]
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hk := kummerBreak_pos F
  have hpn : (0 : ℝ) < (p : ℝ) ^ n * kummerBreak F := mul_pos (by positivity) hk
  nlinarith

/-- The ramification index of a stage over `F`, in the sense of the FontaineWintenberger library,
is positive and at most the degree `p ^ n`. -/
theorem towerStage_ramificationIdx_le (hπ : IsKummerRootSystem F ϖ πs) (n : ℕ) :
    0 < (towerStage F πs n).ramificationIdx F.Carrier ∧
      (towerStage F πs n).ramificationIdx F.Carrier ≤ p ^ n := by
  have h := FontaineWintenberger.local_ramificationIdx_mul_inertiaDeg
    (NormedField.valuation (K := F.Carrier)).valuationSubring
    (FontaineWintenberger.spectralIntegerRing F.Carrier (towerStage F πs n).val)
  rw [FontaineWintenberger.spectralIntegerRing_finrank, towerStage_finrank πs hπ n] at h
  have hpn : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  change 0 < (IsLocalRing.maximalIdeal _).ramificationIdx _ ∧
    (IsLocalRing.maximalIdeal _).ramificationIdx _ ≤ p ^ n
  constructor
  · rcases Nat.eq_zero_or_pos ((IsLocalRing.maximalIdeal
      (FontaineWintenberger.spectralIntegerRing F.Carrier (towerStage F πs n).val)).ramificationIdx
      (NormedField.valuation (K := F.Carrier)).valuationSubring) with h0 | h0
    · rw [h0, zero_mul] at h
      omega
    · exact h0
  · rw [← h]
    apply Nat.le_mul_of_pos_right
    rcases Nat.eq_zero_or_pos ((IsLocalRing.maximalIdeal
      (FontaineWintenberger.spectralIntegerRing F.Carrier (towerStage F πs n).val)).inertiaDeg
      (NormedField.valuation (K := F.Carrier)).valuationSubring) with h0 | h0
    · rw [h0, mul_zero] at h
      omega
    · exact h0

/-- The union of the stages, inside the separable closure, is arithmetically profinite. -/
theorem isAPF_iSup_towerStage (hπ : IsKummerRootSystem F ϖ πs) :
    FontaineWintenberger.IsAPF F.Carrier ↥(⨆ n, (towerStage F πs n).val) := by
  have htame : ∀ u : ℝ, 0 < u → FontaineWintenberger.absoluteUpperRamificationGroup F.Carrier u ≤
      (towerStage F πs 0).val.fixingSubgroup := by
    intro u _
    rw [towerStage_zero πs hπ, IntermediateField.fixingSubgroup_bot]
    exact le_top
  rw [FontaineWintenberger.isAPF_iSup_iff_tendsto_of_isElementaryStep F.Carrier (towerStage F πs)
    (towerLevel πs) (towerStage_strictMono πs hπ) (towerLevel_strictMono πs hπ)
    (towerStep_isElementaryStep πs hπ) htame]
  set c : ℝ := ((p : ℝ) - 1) * kummerBreak F / p with hc
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hcpos : 0 < c := by
    have := kummerBreak_pos F
    rw [hc]
    apply div_pos (mul_pos (by linarith) this)
    linarith
  have hbound : ∀ n : ℕ, (n : ℝ) * c ≤
      FontaineWintenberger.apfPhi F.Carrier (towerStage F πs n).val (towerLevel πs n) := by
    intro n
    rw [FontaineWintenberger.apfPhi_eq_sum_of_isElementaryStep F.Carrier (towerStage F πs)
      (towerLevel πs) (towerStage_strictMono πs hπ).monotone (towerLevel_strictMono πs hπ)
      (towerStep_isElementaryStep πs hπ) htame n]
    have h0 : 0 ≤ towerLevel πs 0 /
        ((towerStage F πs 0).ramificationIdx F.Carrier : ℝ) :=
      div_nonneg (by rw [towerLevel_eq πs hπ]; simpa using (kummerBreak_pos F).le)
        (Nat.cast_nonneg _)
    have hterm : ∀ k ∈ Finset.range n, c ≤ (towerLevel πs (k + 1) - towerLevel πs k) /
        ((towerStage F πs (k + 1)).ramificationIdx F.Carrier : ℝ) := by
      intro k _
      obtain ⟨hpos, hle⟩ := towerStage_ramificationIdx_le πs hπ (k + 1)
      have hpos' : (0 : ℝ) < (towerStage F πs (k + 1)).ramificationIdx F.Carrier := by
        exact_mod_cast hpos
      have hle' : ((towerStage F πs (k + 1)).ramificationIdx F.Carrier : ℝ) ≤
          (p : ℝ) ^ (k + 1) := by
        exact_mod_cast hle
      rw [le_div_iff₀ hpos', towerLevel_eq πs hπ, towerLevel_eq πs hπ, hc]
      have hk := kummerBreak_pos F
      have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
      have hp0 : (0 : ℝ) < p := by linarith
      calc ((p : ℝ) - 1) * kummerBreak F / p *
            ((towerStage F πs (k + 1)).ramificationIdx F.Carrier : ℝ) ≤
          ((p : ℝ) - 1) * kummerBreak F / p * (p : ℝ) ^ (k + 1) := by
            apply mul_le_mul_of_nonneg_left hle'
            apply div_nonneg (mul_nonneg (by linarith) hk.le) hp0.le
        _ = (p : ℝ) ^ (k + 1) * kummerBreak F - (p : ℝ) ^ k * kummerBreak F := by
            rw [pow_succ]
            field_simp
    have hsum := Finset.card_nsmul_le_sum (Finset.range n) _ c hterm
    rw [Finset.card_range, nsmul_eq_mul] at hsum
    linarith
  refine Filter.tendsto_atTop_mono hbound ?_
  exact tendsto_natCast_atTop_atTop.atTop_mul_const hcpos

theorem kummerTower_map_eq :
    (kummerTower F πs).map (sepClosureEquiv F).toAlgHom = ⨆ n, (towerStage F πs n).val := by
  rw [kummerTower, IntermediateField.map_iSup]
  refine iSup_congr fun n => ?_
  change (IntermediateField.adjoin F.Carrier {πs n}).map (sepClosureEquiv F).toAlgHom =
    IntermediateField.adjoin F.Carrier {towerRoot F πs n}
  rw [IntermediateField.adjoin_map, Set.image_singleton]
  rfl

/-- **The Kummer tower is arithmetically profinite** (Wintenberger 1.2.1), for the canonical norm
of the base. -/
theorem kummerTower_isAPF (hπ : IsKummerRootSystem F ϖ πs) :
    FontaineWintenberger.IsAPF F.Carrier (kummerTower F πs) := by
  rw [FontaineWintenberger.isAPF_algEquiv F.Carrier
    (IntermediateField.intermediateFieldMap (sepClosureEquiv F) (kummerTower F πs)),
    kummerTower_map_eq πs]
  exact isAPF_iSup_towerStage πs hπ

/-- The Kummer tower is an infinite extension. -/
theorem kummerTower_not_finite (hπ : IsKummerRootSystem F ϖ πs) :
    ¬ Module.Finite F.Carrier (kummerTower F πs) := by
  intro hfin
  have hfin' : FiniteDimensional F.Carrier ↥(⨆ n, (towerStage F πs n).val) := by
    rw [← kummerTower_map_eq πs]
    exact (IntermediateField.intermediateFieldMap (sepClosureEquiv F)
      (kummerTower F πs)).toLinearEquiv.finiteDimensional
  set N := Module.finrank F.Carrier ↥(⨆ n, (towerStage F πs n).val)
  have hn : N < p ^ N := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
  have hle := IntermediateField.finrank_le_of_le_right
    (le_iSup (fun n => (towerStage F πs n).val) N)
  rw [towerStage_finrank πs hπ N] at hle
  omega

/-- **`ψ` of the Kummer tower is the identity up to the first Kummer break.** -/
theorem kummerTower_apfPsi (hπ : IsKummerRootSystem F ϖ πs) {u : ℝ} (hu : u ≤ kummerBreak F) :
    FontaineWintenberger.apfPsi F.Carrier (kummerTower F πs) u = u := by
  apply apfPsi_eq_self_of_sup_eq_top (Padic p) (padicBaseNorm_compatible p) F.Carrier
    (AlgebraicClosure F.Carrier) _ (kummerTower F πs).val _ hu
  rw [IntermediateField.fieldRange_val]
  exact Kummer.kummerTowerLimitUpperSup p F ϖ πs hπ (kummerBreak F)
    (by linarith [kummerBreak_pos F]) le_rfl

end Criterion

end Langlands.Ramification.Wintenberger
