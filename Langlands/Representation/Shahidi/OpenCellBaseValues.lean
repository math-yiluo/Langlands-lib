import Langlands.Representation.Shahidi.OpenCellBaseStep
import Langlands.Representation.RankinSelberg.TwoBlockDominantBlockSupport
import Langlands.Representation.RankinSelberg.TwoBlockJacquetData
import Langlands.Representation.Shahidi.Characters

/-! # Values of the `(1, n)` open-cell integrand

Support (for `Ψ` right invariant under the integral group) and periodicity and integrability
(for such `Ψ` and `ψ` of conductor `𝒪`) of the integrand `Y ↦ F(lower Y) conj ψ(Y_last)`, and,
for `Ψ` of Whittaker type, its values on a column `(y, c)` with `c` integral (for `ψ` of conductor
`𝒪`) and with `v(c) = v(ϖ)^(-e)`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell.Base

open Langlands.GeneralLinear Langlands.Conductor MeasureTheory
open scoped NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocBaseValuesTopology : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance ocBaseValuesValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocBaseValuesLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocBaseValuesT2 : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocBaseValuesSecondCountable : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocBaseValuesMeasurable : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocBaseValuesBorel : BorelSpace K.Carrier := ⟨rfl⟩

variable {ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology}
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
variable {t : ℕ}

section Support

variable (hψ : HasIntegerConductor ψ)
variable {d : ℤ} {Ψ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
  (hΨ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers t, Ψ (g * k) = Ψ g)

include hψ hΨ in
theorem baseIntegrand_isLatticePeriodic :
    IsLatticePeriodic K (baseIntegrand ψ hϖ d Ψ) := by
  intro Y Z hZ
  simp only [baseIntegrand]
  rw [liftFunction_lower_add_integral hϖ (isLeviInvariant_shellΦ d hΨ) Y Z hZ]
  congr 1
  have hz : Z (Fin.last t) 0 ∈ K.canonicalTopologicalData.Integers :=
    (mem_integralMatrices_iff K _ _ Z).1 hZ _ _
  have h : (ψ (Y (Fin.last t) 0 + Z (Fin.last t) 0) : ℂ) = (ψ (Y (Fin.last t) 0) : ℂ) := by
    rw [← HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, AddChar.map_add_eq_mul,
      HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
      HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, hψ.1 _ hz]
    simp
  change starRingEnd ℂ (ψ (Y (Fin.last t) 0 + Z (Fin.last t) 0) : ℂ) =
    starRingEnd ℂ (ψ (Y (Fin.last t) 0) : ℂ)
  rw [h]

include hΨ in
theorem baseIntegrand_eq_zero_of_depth_ne (Y : Matrix (Fin (t + 1)) (Fin 1) K.Carrier)
    (hY : openCellDepth hϖ Y ≠ d) : baseIntegrand ψ hϖ d Ψ Y = 0 := by
  rw [baseIntegrand, liftFunction_shellΦ_eq_zero hϖ d hΨ Y hY, zero_mul]

include hψ hΨ in
theorem integrable_baseIntegrand : Integrable (baseIntegrand ψ hϖ d Ψ) (matrixHaar K (t + 1) 1) := by
  refine (integrable_and_hasSum_of_isLatticePeriodic K (baseIntegrand_isLatticePeriodic hϖ hψ hΨ)
    ?_).1
  set S : Set (Matrix (Fin (t + 1)) (Fin 1) K.Carrier ⧸ integralMatrices K (t + 1) 1) :=
    {y | ∀ i j, ((ϖ ^ (d.toNat : ℤ) : K.Carrierˣ) : K.Carrier) * (Quotient.out y) i j ∈
      K.canonicalTopologicalData.Integers}
  have hS : S.Finite := (finite_and_ncard_le K hϖ (t + 1) 1 S fun y hy => hy).1
  refine summable_of_ne_finset_zero (s := hS.toFinset) fun y hy => ?_
  rw [Set.Finite.mem_toFinset] at hy
  rw [baseIntegrand_eq_zero_of_depth_ne hϖ hΨ, norm_zero]
  intro hd
  apply hy
  intro i j
  have h := uniformizer_pow_depth_mul_mem hϖ (Quotient.out y) i j
  have hd0 : (d.toNat : ℤ) = d := by
    have := openCellDepth_nonneg hϖ (Quotient.out y)
    omega
  rw [hd] at h
  rw [hd0]
  exact h

end Support

section Blocks

theorem blockSum_one_mem_upperUnipotent {n : ℕ} {u : Langlands.GeneralLinear n K.Carrier}
    (hu : u ∈ upperUnipotent n K.Carrier) :
    GeneralLinear.blockSum (n := n) (m := 1) (u, 1) ∈ upperUnipotent (n + 1) K.Carrier := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · revert hij
    induction i using Fin.addCases with
    | left i' =>
      induction j using Fin.addCases with
      | left j' =>
        intro hij
        rw [blockSum_apply_left]
        have h := (Fin.lt_def).1 hij
        simp only [id, Fin.val_castAdd] at h
        exact hu.1 (show j' < i' from Fin.lt_def.2 h)
      | right j' =>
        intro hij
        exfalso
        have h := (Fin.lt_def).1 hij
        simp only [id, Fin.val_castAdd, Fin.val_natAdd] at h
        omega
    | right i' =>
      induction j using Fin.addCases with
      | left j' =>
        intro _
        exact blockSum_apply_right_left _ _ _ _
      | right j' =>
        intro hij
        exfalso
        have h := (Fin.lt_def).1 hij
        simp only [id, Fin.val_natAdd] at h
        have := i'.isLt
        have := j'.isLt
        omega
  · refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
    · rw [blockSum_apply_left]
      exact hu.2 i'
    · rw [blockSum_apply_right, Subsingleton.elim i' 0]
      simp

theorem standardCharacter_blockSum_one (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
      K.canonicalTopologicalData.topology) {n : ℕ} (u : upperUnipotent (n + 1) K.Carrier) :
    @Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ (n + 1)
        ⟨GeneralLinear.blockSum (n := n + 1) (m := 1) (u.val, 1),
          blockSum_one_mem_upperUnipotent u.2⟩ =
      @Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ n u := by
  apply Units.ext
  rw [Whittaker.standardCharacter_apply, Whittaker.standardCharacter_apply]
  congr 1
  rw [Fin.sum_univ_castSucc]
  have hlast : (GeneralLinear.blockSum (n := n + 1) (m := 1) (u.val, 1) :
      Matrix _ _ K.Carrier) (Fin.last n).castSucc (Fin.last n).succ = 0 := by
    rw [show (Fin.last n).castSucc = Fin.castAdd 1 (Fin.last n) from rfl,
      show (Fin.last n).succ = Fin.natAdd (n + 1) (0 : Fin 1) from Fin.ext (by simp)]
    exact blockSum_apply_left_right _ _ _ _
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show i.castSucc.castSucc = Fin.castAdd 1 i.castSucc from rfl,
    show i.castSucc.succ = Fin.castAdd 1 i.succ from Fin.ext (by simp)]
  exact blockSum_apply_left _ _ _ _

theorem torus_const_zero {n : ℕ} : Iwasawa.torus ϖ (fun _ : Fin n => (0 : ℤ)) = 1 := by
  apply Units.ext
  rw [Iwasawa.torus_val]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply]

end Blocks

variable {r : ℕ} in
theorem liftFunction_one {Φ : Langlands.GeneralLinear (r + 1) K.Carrier →
      Langlands.GeneralLinear (t + 1) K.Carrier → ℂ} (hΦ : IsLeviInvariant Φ) :
    liftFunction hϖ Φ 1 = Φ 1 1 := by
  have h := liftFunction_law hϖ hΦ 0 1 1 1 (one_mem _)
  have e : upper (r + 1) (t + 1) K.Carrier 0 * GeneralLinear.blockSum (1, 1) * 1 = 1 := by
    rw [upper_zero, one_mul, mul_one, ← Prod.one_eq_mk, map_one]
  rwa [e] at h

section StepMem

variable {t' : ℕ}

/-- The function `h ↦ Ψ(diag(h, 1))` on `GL_(t'+1)`. -/
def restrictOne (Ψ : Langlands.GeneralLinear ((t' + 1) + 1) K.Carrier → ℂ)
    (h : Langlands.GeneralLinear (t' + 1) K.Carrier) : ℂ :=
  Ψ (GeneralLinear.blockSum (n := t' + 1) (m := 1) (h, 1))

theorem restrictOne_mul_integral {Ψ : Langlands.GeneralLinear ((t' + 1) + 1) K.Carrier → ℂ}
    (hΨ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers (t' + 1),
      Ψ (g * k) = Ψ g) :
    ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers t',
      restrictOne Ψ (g * k) = restrictOne Ψ g := by
  intro g k hk
  have e : GeneralLinear.blockSum (n := t' + 1) (m := 1) (g * k, 1) =
      GeneralLinear.blockSum (n := t' + 1) (m := 1) (g, 1) *
        GeneralLinear.blockSum (n := t' + 1) (m := 1) (k, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [restrictOne]
  rw [e, hΨ _ _ (blockSum_one_mem k hk)]

variable (hψ : HasIntegerConductor ψ)

open Classical in
include hψ in
/-- **The integrand on a column whose last entry is integral**, for `ψ` of conductor `𝒪` and `Ψ`
of Whittaker type. -/
theorem baseIntegrand_joinColumn_of_mem {d : ℤ}
    {Ψ : Langlands.GeneralLinear ((t' + 1) + 1) K.Carrier → ℂ} (hΨ : IsWhittakerType ψ Ψ)
    {c : K.Carrier} (hc : c ∈ K.canonicalTopologicalData.Integers)
    (y : Matrix (Fin (t' + 1)) (Fin 1) K.Carrier) :
    baseIntegrand ψ hϖ d Ψ (joinColumn K (t' + 1) c y) =
      if d = 0 ∧ y ∈ integralMatrices K (t' + 1) 1 then Ψ 1 else 0 := by
  have hψc : starRingEnd ℂ (ψ c : ℂ) = 1 := by
    rw [hψ.1 c hc]
    simp
  have hK := restrictOne_mul_integral hΨ.2
  have hΦ := isLeviInvariant_shellΦ (K := K) d hK
  unfold baseIntegrand
  rw [joinColumn_last, hψc, mul_one,
    liftFunction_lower_of_mem hϖ (isLeviInvariant_shellΦ d hΨ.2) _
      (by rw [joinColumn_last]; exact hc)]
  have hhead : headCol (joinColumn K (t' + 1) c y) = y := by
    ext i j
    rw [Subsingleton.elim j 0]
    simp [headCol]
  rw [hhead]
  change liftFunction hϖ (shellΦ d (restrictOne Ψ)) (lower (0 + 1) (t' + 1) K.Carrier y) = _
  by_cases hy : y ∈ integralMatrices K (t' + 1) 1
  · have hk := lower_mem_integralSubgroup y hy
    rw [show lower (0 + 1) (t' + 1) K.Carrier y = 1 * lower (0 + 1) (t' + 1) K.Carrier y by
      rw [one_mul], liftFunction_mul_integral hϖ hΦ 1 _ hk, liftFunction_one hϖ hΦ]
    simp only [shellΦ, map_one, Units.val_one, NNReal.coe_one, restrictOne]
    by_cases hd : d = 0
    · subst hd
      simp [← Prod.one_eq_mk, hy]
    · rw [ite_eq_right (fun h => hd (by
        have := zpow_residue_injective (K := K) (a := 0) (b := -d) (by rw [zpow_zero]; exact h)
        omega)), ite_eq_right (fun h => hd h.1)]
  · rw [ite_eq_right (fun h => hy h.2)]
    by_cases hd : openCellDepth hϖ y = d
    · obtain ⟨u₁, hu₁, u₂, hu₂, h⟩ := liftFunction_lower hϖ hΦ y
      rw [h]
      simp only [shellΦ, restrictOne]
      split_ifs
      · set μ : Fin (t' + 1) → ℤ := fun j => openCellExponent hϖ y (j.natAdd (0 + 1)) with hμ
        have e : GeneralLinear.blockSum (n := t' + 1) (m := 1) (u₂ * Iwasawa.torus ϖ μ, 1) =
            GeneralLinear.blockSum (n := t' + 1) (m := 1) (u₂, 1) *
              Iwasawa.torus ϖ (Fin.append μ (fun _ : Fin 1 => (0 : ℤ))) := by
          rw [← RankinSelberg.TwoBlockDominantRectangular.blockSum_torus, ← map_mul,
            Prod.mk_mul_mk, torus_const_zero, mul_one]
        rw [e, hΨ.1 ⟨_, blockSum_one_mem_upperUnipotent hu₂⟩]
        rw [whittaker_torus_eq_zero hϖ hψ hΨ, mul_zero]
        intro hanti
        apply hy
        have hdepth0 : openCellDepth hϖ y = 0 := by
          have hle : ∀ j, μ j ≤ 0 := fun j => openCellExponent_natAdd_nonpos hϖ y j
          have hge : ∀ j, 0 ≤ μ j := by
            intro j
            have := hanti (show Fin.castAdd 1 j ≤ Fin.natAdd (t' + 1) (0 : Fin 1) from
              Fin.le_def.2 (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega))
            simpa [Fin.append_left, Fin.append_right] using this
          have hsum := sum_openCellExponent_natAdd hϖ y
          have : ∑ j, μ j = 0 := Finset.sum_eq_zero fun j _ => le_antisymm (hle j) (hge j)
          change ∑ j, μ j = _ at hsum
          linarith
        refine (mem_integralMatrices_iff K _ _ y).2 fun i j => ?_
        have := uniformizer_pow_depth_mul_mem hϖ y i j
        rwa [hdepth0, zpow_zero, Units.val_one, one_mul] at this
      · rfl
    · exact liftFunction_shellΦ_eq_zero hϖ d hK y hd

end StepMem

section StepNotMem

variable {t' : ℕ}

/-- The function `h ↦ Ψ(diag(h, ϖ^(-e)))` on `GL_(t'+1)`. -/
def twistOne (ϖ : K.Carrierˣ) (Ψ : Langlands.GeneralLinear ((t' + 1) + 1) K.Carrier → ℂ) (e : ℕ)
    (h : Langlands.GeneralLinear (t' + 1) K.Carrier) : ℂ :=
  Ψ (GeneralLinear.blockSum (n := t' + 1) (m := 1) (h, Iwasawa.torus ϖ fun _ => -(e : ℤ)))

theorem isWhittakerType_twistOne {Ψ : Langlands.GeneralLinear ((t' + 1) + 1) K.Carrier → ℂ}
    (hΨ : IsWhittakerType ψ Ψ) (e : ℕ) : IsWhittakerType ψ (twistOne ϖ Ψ e) := by
  constructor
  · intro u g
    have e₁ : GeneralLinear.blockSum (n := t' + 1) (m := 1)
        (u.val * g, Iwasawa.torus ϖ fun _ => -(e : ℤ)) =
        GeneralLinear.blockSum (n := t' + 1) (m := 1) (u.val, 1) *
          GeneralLinear.blockSum (n := t' + 1) (m := 1) (g, Iwasawa.torus ϖ fun _ => -(e : ℤ)) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    simp only [twistOne]
    rw [e₁, hΨ.1 ⟨_, blockSum_one_mem_upperUnipotent u.2⟩, standardCharacter_blockSum_one]
  · intro g k hk
    have e₁ : GeneralLinear.blockSum (n := t' + 1) (m := 1)
        (g * k, Iwasawa.torus ϖ fun _ => -(e : ℤ)) =
        GeneralLinear.blockSum (n := t' + 1) (m := 1) (g, Iwasawa.torus ϖ fun _ => -(e : ℤ)) *
          GeneralLinear.blockSum (n := t' + 1) (m := 1) (k, 1) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    simp only [twistOne]
    rw [e₁, hΨ.2 _ _ (blockSum_one_mem k hk)]

theorem exists_unit_of_valuation {c : K.Carrier} {e : ℕ}
    (he : @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel c =
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (ϖ : K.Carrier)) ^
        (-(e : ℤ))) :
    ∃ w : K.Carrierˣ, @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel
        (w : K.Carrier) = 1 ∧ c = ((ϖ ^ (-(e : ℤ)) : K.Carrierˣ) : K.Carrier) * w := by
  set v := @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel
  have hv0 : 0 < v (ϖ : K.Carrier) := Iwasawa.valuation_pos v ϖ
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at he
    exact (zpow_ne_zero _ hv0.ne') he.symm
  refine ⟨Units.mk0 c hc0 * ϖ ^ (e : ℤ), ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mk0, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, he,
      ← zpow_add₀ hv0.ne', neg_add_cancel, zpow_zero]
  · rw [Units.val_mul, Units.val_mk0, ← mul_assoc, mul_comm _ c, mul_assoc, ← Units.val_mul,
      ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, mul_one]

theorem blockSum_one_diagonalUnits_mem {w : K.Carrierˣ}
    (hw : @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (w : K.Carrier) = 1) :
    GeneralLinear.blockSum (n := t' + 1) (m := 1) (1, Iwasawa.diagonalUnits fun _ : Fin 1 => w) ∈
      integralSubgroup K.canonicalTopologicalData.Integers (t' + 1) := by
  have hw1 : (w : K.Carrier) ∈ K.canonicalTopologicalData.Integers := hw.le
  have hw2 : ((w⁻¹ : K.Carrierˣ) : K.Carrier) ∈ K.canonicalTopologicalData.Integers := by
    change @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel _ ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hw, inv_one]
  refine (mem_integralSubgroup _ _ _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
      refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · rw [blockSum_apply_left]
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · rw [blockSum_apply_left_right]; exact zero_mem _
    · rw [blockSum_apply_right_left]; exact zero_mem _
    · rw [blockSum_apply_right, Subsingleton.elim i' j', Iwasawa.diagonalUnits_val,
        Matrix.diagonal_apply_eq]
      exact hw1
  · rw [← map_inv, Prod.inv_mk, inv_one, ← map_inv]
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
      refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · rw [blockSum_apply_left]
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · rw [blockSum_apply_left_right]; exact zero_mem _
    · rw [blockSum_apply_right_left]; exact zero_mem _
    · rw [blockSum_apply_right, Subsingleton.elim i' j', Iwasawa.diagonalUnits_val,
        Matrix.diagonal_apply_eq]
      simpa using hw2

theorem standardCharacter_upper (z : Matrix (Fin (t' + 1)) (Fin 1) K.Carrier) :
    (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ (t' + 1)
      ⟨upper (t' + 1) 1 K.Carrier z, upper_mem_upperUnipotent _ _ _ z⟩ : ℂ) =
      (ψ (z (Fin.last t') 0) : ℂ) := by
  rw [Whittaker.standardCharacter_apply, HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply]
  congr 2
  exact RankinSelberg.TwoBlockJacquet.sum_superdiagonal_upper (a := t') (b := 0) z

include hϖ in
theorem normalizedAbs_of_valuation {u : K.Carrierˣ} {e : ℕ}
    (hu : @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (u : K.Carrier) =
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (ϖ : K.Carrier)) ^
        (-(e : ℤ))) :
    K.canonicalTopologicalData.normalizedAbs (u : K.Carrier) =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^ (e : ℤ) := by
  obtain ⟨w, hw, huw⟩ := exists_unit_of_valuation hu
  rw [huw, K.canonicalTopologicalData.normalizedAbs_mul,
    normalizedAbs_zpow_of_isUniformizingElement K hϖ,
    (K.canonicalTopologicalData.normalizedAbs_eq_one_iff_valuation_eq_one _).2 hw, mul_one, neg_neg]

include hϖ in
/-- The relation between the shell functions on `GL_(1+(t'+2))` and `GL_(1+(t'+1))`. -/
theorem shellΦ_rel {d : ℤ} {Ψ : Langlands.GeneralLinear ((t' + 1) + 1) K.Carrier → ℂ}
    (hΨ : IsWhittakerType ψ Ψ) {u : K.Carrierˣ} {e : ℕ}
    (hu : @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (u : K.Carrier) =
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (ϖ : K.Carrier)) ^
        (-(e : ℤ)))
    (z : Matrix (Fin (t' + 1)) (Fin 1) K.Carrier) (m₁ : Langlands.GeneralLinear (0 + 1) K.Carrier)
    (m₂ : Langlands.GeneralLinear (t' + 1) K.Carrier) :
    shellΦ d Ψ (scalarGL u⁻¹ * m₁)
        (upper (t' + 1) 1 K.Carrier z *
          GeneralLinear.blockSum (n := t' + 1) (m := 1) (1, scalarGL u) *
          GeneralLinear.blockSum (n := t' + 1) (m := 1) (m₂, 1)) =
      (ψ (z (Fin.last t') 0) : ℂ) * shellΦ (d - e) (twistOne ϖ Ψ e) m₁ m₂ := by
  obtain ⟨w, hw, huw⟩ := exists_unit_of_valuation hu
  have hsc : (scalarGL u : Langlands.GeneralLinear 1 K.Carrier) =
      Iwasawa.torus ϖ (fun _ => -(e : ℤ)) * Iwasawa.diagonalUnits (fun _ : Fin 1 => w) := by
    rw [scalarGL, Iwasawa.torus, ← map_mul]
    congr 1
    funext i
    apply Units.ext
    rw [huw]
    rfl
  have hX : upper (t' + 1) 1 K.Carrier z *
      GeneralLinear.blockSum (n := t' + 1) (m := 1) (1, scalarGL u) *
      GeneralLinear.blockSum (n := t' + 1) (m := 1) (m₂, 1) =
      upper (t' + 1) 1 K.Carrier z *
        GeneralLinear.blockSum (n := t' + 1) (m := 1) (m₂, Iwasawa.torus ϖ fun _ => -(e : ℤ)) *
        GeneralLinear.blockSum (n := t' + 1) (m := 1) (1, Iwasawa.diagonalUnits fun _ : Fin 1 => w) := by
    rw [mul_assoc, mul_assoc, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, hsc]
    simp only [one_mul, mul_one]
  have hΨval : Ψ (upper (t' + 1) 1 K.Carrier z *
      GeneralLinear.blockSum (n := t' + 1) (m := 1) (1, scalarGL u) *
      GeneralLinear.blockSum (n := t' + 1) (m := 1) (m₂, 1)) =
      (ψ (z (Fin.last t') 0) : ℂ) * twistOne ϖ Ψ e m₂ := by
    rw [hX, hΨ.2 _ _ (blockSum_one_diagonalUnits_mem hw)]
    have := hΨ.1 ⟨upper (t' + 1) 1 K.Carrier z, upper_mem_upperUnipotent _ _ _ z⟩
      (GeneralLinear.blockSum (n := t' + 1) (m := 1) (m₂, Iwasawa.torus ϖ fun _ => -(e : ℤ)))
    rw [this, standardCharacter_upper]
    rfl
  have hdet : ((K.canonicalTopologicalData.determinantNorm (0 + 1) (scalarGL u⁻¹ * m₁) : ℝ≥0) : ℝ) =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^ (-(e : ℤ)) *
        ((K.canonicalTopologicalData.determinantNorm (0 + 1) m₁ : ℝ≥0) : ℝ) := by
    rw [map_mul, Units.val_mul, NNReal.coe_mul]
    congr 1
    rw [K.canonicalTopologicalData.determinantNorm_coe]
    change K.canonicalTopologicalData.normalizedAbs
      (((Iwasawa.diagonalUnits fun _ : Fin (0 + 1) => u⁻¹ : Langlands.GeneralLinear (0 + 1) K.Carrier) :
        Matrix (Fin (0 + 1)) (Fin (0 + 1)) K.Carrier)).det = _
    have hinv : K.canonicalTopologicalData.normalizedAbs ((u : K.Carrier)⁻¹) =
        (K.canonicalTopologicalData.normalizedAbs (u : K.Carrier))⁻¹ := by
      rw [← K.canonicalTopologicalData.normalizedAbsHom_coe,
        ← K.canonicalTopologicalData.normalizedAbsHom_coe, map_inv₀, NNReal.coe_inv]
    rw [Iwasawa.diagonalUnits_val, Matrix.det_diagonal, Fin.prod_univ_one, Units.val_inv_eq_inv_val,
      hinv, normalizedAbs_of_valuation hϖ hu, zpow_neg]
  have hq : (0 : ℝ) < K.canonicalTopologicalData.residueCardinality := by
    have := K.canonicalTopologicalData.residueCardinality_gt_one
    positivity
  simp only [shellΦ, hdet, hΨval]
  have hiff : (K.canonicalTopologicalData.residueCardinality : ℝ) ^ (-(e : ℤ)) *
      ((K.canonicalTopologicalData.determinantNorm (0 + 1) m₁ : ℝ≥0) : ℝ) =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^ (-d) ↔
      ((K.canonicalTopologicalData.determinantNorm (0 + 1) m₁ : ℝ≥0) : ℝ) =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^ (-(d - e)) := by
    set Q := (K.canonicalTopologicalData.residueCardinality : ℝ)
    set x := ((K.canonicalTopologicalData.determinantNorm (0 + 1) m₁ : ℝ≥0) : ℝ)
    rw [show -(d - (e : ℤ)) = -d + e by ring, zpow_add₀ hq.ne']
    have key : Q ^ (e : ℤ) * Q ^ (-(e : ℤ)) = 1 := by
      rw [← zpow_add₀ hq.ne', add_neg_cancel, zpow_zero]
    constructor
    · intro h
      calc x = (Q ^ (e : ℤ) * Q ^ (-(e : ℤ))) * x := by rw [key, one_mul]
        _ = Q ^ (e : ℤ) * (Q ^ (-(e : ℤ)) * x) := by ring
        _ = Q ^ (-d) * Q ^ (e : ℤ) := by rw [h]; ring
    · intro h
      rw [h]
      calc Q ^ (-(e : ℤ)) * (Q ^ (-d) * Q ^ (e : ℤ)) = Q ^ (-d) * (Q ^ (e : ℤ) * Q ^ (-(e : ℤ))) := by
            ring
        _ = Q ^ (-d) := by rw [key, mul_one]
  by_cases h1 : ((K.canonicalTopologicalData.determinantNorm (0 + 1) m₁ : ℝ≥0) : ℝ) =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^ (-(d - e))
  · rw [ite_eq_left (hiff.2 h1), ite_eq_left h1]
  · rw [ite_eq_right (fun h => h1 (hiff.1 h)), ite_eq_right h1, mul_zero]

include hϖ in
/-- **The integrand on a column whose last entry has valuation `v(ϖ)^(-e)`**, for `Ψ` of
Whittaker type. -/
theorem baseIntegrand_joinColumn_of_valuation {d : ℤ}
    {Ψ : Langlands.GeneralLinear ((t' + 1) + 1) K.Carrier → ℂ} (hΨ : IsWhittakerType ψ Ψ)
    {c : K.Carrier} {e : ℕ}
    (he : @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel c =
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (ϖ : K.Carrier)) ^
        (-(e : ℤ)))
    (y : Matrix (Fin (t' + 1)) (Fin 1) K.Carrier) :
    baseIntegrand ψ hϖ d Ψ (joinColumn K (t' + 1) c y) =
      starRingEnd ℂ (ψ c : ℂ) * ((ψ ((c⁻¹ • y) (Fin.last t') 0) : ℂ) *
        liftFunction hϖ (shellΦ (d - e) (twistOne ϖ Ψ e))
          (lower (0 + 1) (t' + 1) K.Carrier (c⁻¹ • y))) := by
  set v := @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel
  have hv0 : 0 < v (ϖ : K.Carrier) := Iwasawa.valuation_pos v ϖ
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at he
    exact (zpow_ne_zero _ hv0.ne') he.symm
  have hcI : c⁻¹ ∈ K.canonicalTopologicalData.Integers := by
    change v c⁻¹ ≤ 1
    rw [map_inv₀, he, ← zpow_neg, neg_neg]
    exact zpow_le_one₀ hv0 hϖ.1.le (by omega)
  set jc := joinColumn K (t' + 1) c y with hjc
  have hl : jc (Fin.last (t' + 1)) 0 = c := joinColumn_last K (t' + 1) c y 0
  have hc0' : jc (Fin.last (t' + 1)) 0 ≠ 0 := by rw [hl]; exact hc0
  have hq : quotCol jc = c⁻¹ • y := by
    ext i j
    rw [Subsingleton.elim j 0]
    simp only [quotCol, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hjc,
      joinColumn_castSucc, joinColumn_last]
    ring
  have hu : v ((Units.mk0 _ hc0' : K.Carrierˣ) : K.Carrier) = v (ϖ : K.Carrier) ^ (-(e : ℤ)) := by
    rw [Units.val_mk0, hl, he]
  have hrel := fun m₁ m₂ => shellΦ_rel hϖ (d := d) hΨ hu (quotCol jc) m₁ m₂
  unfold baseIntegrand
  rw [liftFunction_lower_of_inv_mem hϖ (isLeviInvariant_shellΦ d hΨ.2)
    (isLeviInvariant_shellΦ (d - e) (isWhittakerType_twistOne hΨ e).2) jc hc0'
    (by rw [hl]; exact hcI) _ hrel, hq, hl]
  ring

end StepNotMem

section Negation

variable {t' : ℕ}

theorem conj_char_neg (x : K.Carrier) : starRingEnd ℂ (ψ (-x) : ℂ) = (ψ x : ℂ) := by
  rw [show (ψ (-x) : ℂ) = (((ψ x)⁻¹ : Circle) : ℂ) from by
    rw [← AddChar.map_neg_eq_inv], Circle.coe_inv_eq_conj, Complex.conj_conj]

/-- The diagonal matrix `diag(-1, 1, …, 1)` in `GL_((0+1)+(t'+1))`. -/
def negGL : Langlands.GeneralLinear ((0 + 1) + (t' + 1)) K.Carrier :=
  GeneralLinear.blockSum (n := 0 + 1) (m := t' + 1) (scalarGL (-1), 1)

theorem negGL_eq_liftLevi : (negGL : Langlands.GeneralLinear ((0 + 1) + (t' + 1)) K.Carrier) =
    ((liftLevi K 0 t' (scalarGL (-1)) 1 : (liftShape 0 t').parabolic K.Carrier) :
      Langlands.GeneralLinear ((0 + 1) + (t' + 1)) K.Carrier) :=
  (liftLevi_val K 0 t' _ _).symm

/-- The diagonal entries `(-1, 1, …, 1)`. -/
def negDiag : Fin ((0 + 1) + (t' + 1)) → K.Carrier :=
  Fin.append (fun _ : Fin (0 + 1) => (-1 : K.Carrier)) (fun _ : Fin (t' + 1) => 1)

theorem negGL_val : ((negGL : Langlands.GeneralLinear ((0 + 1) + (t' + 1)) K.Carrier) :
    Matrix (Fin ((0 + 1) + (t' + 1))) (Fin ((0 + 1) + (t' + 1))) K.Carrier) =
      Matrix.diagonal negDiag := by
  ext i j
  refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
    refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
  · rw [negGL, blockSum_apply_left, scalarGL, Iwasawa.diagonalUnits_val, Matrix.diagonal_apply,
      Matrix.diagonal_apply, zero_fin_one i', zero_fin_one j']
    simp [negDiag]
  · rw [negGL, blockSum_apply_left_right, Matrix.diagonal_apply, ite_eq_right]
    intro h
    exact absurd (congrArg Fin.val h) (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega)
  · rw [negGL, blockSum_apply_right_left, Matrix.diagonal_apply, ite_eq_right]
    intro h
    exact absurd (congrArg Fin.val h) (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega)
  · rw [negGL, blockSum_apply_right, Units.val_one, Matrix.one_apply, Matrix.diagonal_apply]
    simp [negDiag, Fin.natAdd_inj]

theorem negDiag_sq (i : Fin ((0 + 1) + (t' + 1))) :
    negDiag (K := K) i ∈ K.canonicalTopologicalData.Integers ∧ negDiag (K := K) i * negDiag i = 1 := by
  refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
  · simp only [negDiag, Fin.append_left]
    exact ⟨neg_mem (one_mem _), by ring⟩
  · simp only [negDiag, Fin.append_right]
    exact ⟨one_mem _, by ring⟩

theorem negGL_mul_self : (negGL : Langlands.GeneralLinear ((0 + 1) + (t' + 1)) K.Carrier) * negGL = 1 := by
  apply Units.ext
  rw [Units.val_mul, negGL_val, Matrix.diagonal_mul_diagonal, Units.val_one]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · rw [(negDiag_sq i).2]
  · rfl

theorem negGL_mem : (negGL : Langlands.GeneralLinear ((0 + 1) + (t' + 1)) K.Carrier) ∈
    integralSubgroup K.canonicalTopologicalData.Integers (0 + 1 + t') := by
  have hinv : (negGL : Langlands.GeneralLinear ((0 + 1) + (t' + 1)) K.Carrier)⁻¹ = negGL :=
    inv_eq_of_mul_eq_one_right negGL_mul_self
  refine (mem_integralSubgroup _ _ _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [negGL_val, Matrix.diagonal_apply]
    split_ifs
    · exact (negDiag_sq i).1
    · exact zero_mem _
  · rw [hinv, negGL_val, Matrix.diagonal_apply]
    split_ifs
    · exact (negDiag_sq i).1
    · exact zero_mem _

theorem lower_neg_eq (z : Matrix (Fin (t' + 1)) (Fin 1) K.Carrier) :
    lower (0 + 1) (t' + 1) K.Carrier (-z) = negGL * lower (0 + 1) (t' + 1) K.Carrier z * negGL := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, negGL_val]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
    refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
  · rw [lower_first_first, lower_first_first, zero_fin_one i', zero_fin_one j']
    simp [negDiag]
  · rw [lower_first_second, lower_first_second]
    simp
  · rw [lower_second_first, lower_second_first]
    simp [negDiag]
  · rw [lower_second_second, lower_second_second]
    simp [negDiag]

theorem liftFunction_shellΦ_lower_neg {d : ℤ} {Ψ : Langlands.GeneralLinear (t' + 1) K.Carrier → ℂ}
    (hΨ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers t', Ψ (g * k) = Ψ g)
    (z : Matrix (Fin (t' + 1)) (Fin 1) K.Carrier) :
    liftFunction hϖ (shellΦ d Ψ) (lower (0 + 1) (t' + 1) K.Carrier (-z)) =
      liftFunction hϖ (shellΦ d Ψ) (lower (0 + 1) (t' + 1) K.Carrier z) := by
  have hΦ := isLeviInvariant_shellΦ (K := K) d hΨ
  rw [lower_neg_eq, liftFunction_mul_integral hϖ hΦ _ _ negGL_mem, negGL_eq_liftLevi]
  obtain ⟨m₁, m₂, h1, h2⟩ := liftFunction_parabolic_mul_left hϖ hΦ
    (liftLevi K 0 t' (scalarGL (-1)) 1) (lower (0 + 1) (t' + 1) K.Carrier z)
  rw [h2, h1, liftFirst_liftLevi, liftSecond_liftLevi, one_mul]
  simp only [shellΦ]
  have hdet : K.canonicalTopologicalData.determinantNorm (0 + 1) (scalarGL (-1) * m₁) =
      K.canonicalTopologicalData.determinantNorm (0 + 1) m₁ := by
    rw [map_mul, Langlands.Unramified.SphericalExistence.determinantNorm_eq_one_of_integral K
      K.canonicalTopologicalData (scalarGL (-1)), one_mul]
    · intro i j
      rw [scalarGL, Iwasawa.diagonalUnits_val, Matrix.diagonal_apply]
      split_ifs
      · exact neg_mem (one_mem _)
      · exact zero_mem _
    · intro i j
      rw [scalarGL, ← map_inv, Iwasawa.diagonalUnits_val, Matrix.diagonal_apply]
      split_ifs
      · simp only [Pi.inv_apply, inv_neg, inv_one, Units.val_neg, Units.val_one]
        exact neg_mem (one_mem _)
      · exact zero_mem _
  rw [hdet]

/-- **The character flip** (`z ↦ -z`), for `Ψ` right invariant under `GL_(t'+1)(𝒪)`. -/
theorem integral_char_mul_liftFunction {d : ℤ}
    {Ψ : Langlands.GeneralLinear (t' + 1) K.Carrier → ℂ}
    (hΨ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers t', Ψ (g * k) = Ψ g) :
    ∫ z, (ψ (z (Fin.last t') 0) : ℂ) *
        liftFunction hϖ (shellΦ d Ψ) (lower (0 + 1) (t' + 1) K.Carrier z) ∂matrixHaar K (t' + 1) 1 =
      ∫ z, baseIntegrand ψ hϖ d Ψ z ∂matrixHaar K (t' + 1) 1 := by
  rw [← integral_neg K (baseIntegrand ψ hϖ d Ψ)]
  congr 1
  funext z
  rw [baseIntegrand, liftFunction_shellΦ_lower_neg hϖ hΨ, Matrix.neg_apply, conj_char_neg, mul_comm]

end Negation

end Langlands.Shahidi.OpenCell.Base
