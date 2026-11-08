import Langlands.Representation.RankinSelberg.HighlyRamified.CoreJSide
import Langlands.Representation.RankinSelberg.HighlyRamified.TestData
import Langlands.Representation.RankinSelberg.HighlyRamified.InducedLevel

/-!
# The test data of the adjacent-rank step

Concrete choices for the Jacquet–Shalika §4.4 core, with the facts the assembly needs:

* the unit-character weight `S₁ = μ · 1_(O^×)` and the weight `η = μ⁻¹` of the last
  coordinate, with `S₁ (χ⁻¹) η = 1_(O^×)` when `μ_(S₁) = μ_η χ`, and the periodicity of `S₁`
  modulo `𝔭^b` when `μ` is trivial on `1 + 𝔭^b`;
* the right equivariance of `f̃'` under `diag(I, c)` from that of `f'`;
* the restricted Fourier transform `S₂` of `Φ₂` with the factorization of the finite Fourier
  transform of `Φ = Φ₁ ⊗ Φ₂` and the support of `S₂` in `(𝔭^f)^(m+1)`;
* `ord ϖ = 1 ⇒ ϖ ∈ 𝔭`, and triviality on `1 + 𝔭^n` from `a(χ) ≤ n`;
* the candidate test function as a model vector of the twisted candidate;
* the nonvanishing of the shell constant.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration Matrix Langlands.GeneralLinear

universe uF uV

section Field

variable {F : Type uF} [Field F] [ValuativeRel F] {m : ℕ}

theorem TrivialOnPrincipalUnits.mul {μ₁ μ₂ : Fˣ →* ℂˣ} {b : ℕ}
    (h₁ : TrivialOnPrincipalUnits μ₁ b) (h₂ : TrivialOnPrincipalUnits μ₂ b) :
    TrivialOnPrincipalUnits (μ₁ * μ₂) b := fun u hu => by
  rw [MonoidHom.mul_apply, h₁ u hu, h₂ u hu, one_mul]

theorem TrivialOnPrincipalUnits.pow {μ : Fˣ →* ℂˣ} {b : ℕ} (h : TrivialOnPrincipalUnits μ b)
    (n : ℕ) : TrivialOnPrincipalUnits (μ ^ n) b := fun u hu => by
  rw [MonoidHom.pow_apply, h u hu, one_pow]

open Classical in
/-- The weight `t ↦ μ(t)` on integral units, `0` elsewhere. -/
def unitCharWeight (μ : Fˣ →* ℂˣ) (t : F) : ℂ :=
  if h : IsIntegralUnit t then (μ (Units.mk0 t h.1) : ℂ) else 0

open Classical in
/-- The weight `t ↦ μ(t)⁻¹` on nonzero `t`. -/
def invCharWeight (μ : Fˣ →* ℂˣ) (t : F) : ℂ :=
  if h : t ≠ 0 then ((μ (Units.mk0 t h) : ℂ))⁻¹ else 0

theorem isIntegralUnit_add_iff {b : ℕ} (hb : 0 < b) {x d : F} (hd : InPow b d) :
    IsIntegralUnit (x + d) ↔ IsIntegralUnit x := by
  constructor
  · intro h
    have := h.add_inPow hb hd.neg
    rwa [add_neg_cancel_right] at this
  · intro h
    exact h.add_inPow hb hd

/-- `S₁ = μ · 1_(O^×)` is periodic modulo `𝔭^b` when `μ` is trivial on `1 + 𝔭^b`. -/
theorem unitCharWeight_add {μ : Fˣ →* ℂˣ} {b : ℕ} (hb : 0 < b)
    (hμ : TrivialOnPrincipalUnits μ b) (x : F) {d : F} (hd : InPow b d) :
    unitCharWeight μ (x + d) = unitCharWeight μ x := by
  classical
  by_cases hx : IsIntegralUnit x
  · have hxd : IsIntegralUnit (x + d) := (isIntegralUnit_add_iff hb hd).2 hx
    unfold unitCharWeight
    rw [dite_eq_left_of_eq_true (eq_true hxd), dite_eq_left_of_eq_true (eq_true hx)]
    congr 1
    apply omega_eq_of_sub_mem hμ
    · simpa using hx.2.2
    · obtain ⟨y, hy, hye⟩ := hd
      exact ⟨y, hy, by simp [hye]⟩
  · have hxd : ¬ IsIntegralUnit (x + d) := fun h => hx ((isIntegralUnit_add_iff hb hd).1 h)
    unfold unitCharWeight
    rw [dite_eq_right_of_eq_false (eq_false hxd), dite_eq_right_of_eq_false (eq_false hx)]

/-- `ϖ^c o ∈ 𝔭^c` for `ϖ ∈ 𝔭` and integral `o`. -/
theorem inPow_pow_mul {ϖ : F} (hϖ : InPow 1 ϖ) (c : ℕ) {o : F}
    (ho : o ∈ (ValuativeRel.valuation F).integer) : InPow c (ϖ ^ c * o) := by
  rw [mul_comm]
  exact (hϖ.pow c).integral_mul ho

/-- The restricted finite Fourier transform `S₂(v) = Σ_z Φ₂(z) ψ(⟨z, v⟩)` for integral `v`. -/
def integralFourier [TopologicalSpace F] (ψ : UnitaryAdditiveCharacter F)
    (T : Finset (Fin (m + 1) → F)) (Φ₂ : (Fin (m + 1) → F) → ℂ) (v : Fin (m + 1) → F) : ℂ := by
  classical
  exact if ∀ k, v k ∈ (ValuativeRel.valuation F).integer then
    ∑ z ∈ T, Φ₂ z * ψ.complex (∑ k, z k * v k) else 0

/-- The finite Fourier transform of `Φ₁ ⊗ Φ₂` factors on integral vectors. -/
theorem finiteFourier_product_eq [TopologicalSpace F] (ψ : UnitaryAdditiveCharacter F)
    (T₁ : Finset F) (T₂ : Finset (Fin (m + 1) → F)) (Φ₁ : F → ℂ)
    (Φ₂ : (Fin (m + 1) → F) → ℂ) (S1 : F → ℂ)
    (hΦ₁ : ∀ ξ ∈ (ValuativeRel.valuation F).integer, ∑ u ∈ T₁, Φ₁ u * ψ.complex (u * ξ) = S1 ξ)
    (ξ : Fin (m + 2) → F) (hξ : ∀ k, ξ k ∈ (ValuativeRel.valuation F).integer) :
    finiteFourier ψ (productTest T₁ T₂) (productWeight Φ₁ Φ₂) ξ =
      S1 (ξ 0) * integralFourier ψ T₂ Φ₂ (fun k => ξ k.succ) := by
  classical
  rw [finiteFourier_product, hΦ₁ _ (hξ 0)]
  unfold integralFourier
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show ∀ k : Fin (m + 1),
    (fun k => ξ k.succ) k ∈ (ValuativeRel.valuation F).integer from fun k => hξ k.succ))]

end Field

section GLOne

variable {F : Type uF} [Field F]

theorem lowerTriangular_entry_ne_zero (c : lowerTriangularSubgroup 1 F) : c.val 0 0 ≠ 0 := by
  rw [← det_gl_one_val]
  exact Units.ne_zero _

theorem determinant_lowerTriangular_eq (c : lowerTriangularSubgroup 1 F) :
    determinant c.val = Units.mk0 (c.val 0 0) (lowerTriangular_entry_ne_zero c) :=
  Units.ext (det_gl_one_val c.val)

/-- `S₁ χ⁻¹ η = 1_(O^×)` for `S₁ = (μ χ) 1_(O^×)` and `η = μ⁻¹`. -/
theorem lastWeight_unitCharWeight {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (χ μ : F.Carrierˣ →* ℂˣ) (c : lowerTriangularSubgroup (0 + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.localField
    lastWeight F χ (unitCharWeight (μ * χ)) (invCharWeight μ) c =
      ((unitLowerSubgroup F : Set (lowerTriangularSubgroup (0 + 1) F.Carrier))).indicator 1 c := by
  classical
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.localField
  have hne := lowerTriangular_entry_ne_zero c
  have hdet := determinant_lowerTriangular_eq c
  unfold lastWeight
  by_cases hc : c ∈ unitLowerSubgroup F
  · rw [Set.indicator_of_mem (show c ∈ ((unitLowerSubgroup F : Set _)) from hc), Pi.one_apply]
    obtain ⟨h1, h2⟩ := (mem_unitLowerSubgroup F c).1 hc
    rw [gl_one_inv_apply] at h2
    have hu : IsIntegralUnit (c.val 0 0) := ⟨hne, h1, h2⟩
    unfold unitCharWeight invCharWeight
    rw [dite_eq_left_of_eq_true (eq_true hu), dite_eq_left_of_eq_true (eq_true hne)]
    rw [hdet, MonoidHom.mul_apply, Units.val_mul]
    have h3 : ((μ (Units.mk0 (c.val 0 0) hne) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have h4 : ((χ (Units.mk0 (c.val 0 0) hne) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  · rw [Set.indicator_of_notMem (show c ∉ ((unitLowerSubgroup F : Set _)) from hc)]
    have hu : ¬ IsIntegralUnit (c.val 0 0) := by
      rintro ⟨-, h1, h2⟩
      apply hc
      rw [mem_unitLowerSubgroup, gl_one_inv_apply]
      exact ⟨h1, h2⟩
    unfold unitCharWeight
    rw [dite_eq_right_of_eq_false (eq_false hu), zero_mul, zero_mul]

variable {m : ℕ}

theorem lowerBlockPair_diag_one :
    (lowerBlockPair (1 : Langlands.GeneralLinear (m + 1) F) 0
      (1 : lowerTriangularSubgroup 1 F) : Langlands.GeneralLinear (m + 1 + 1) F) = 1 := by
  apply Units.ext
  ext i j
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => rw [lowerBlockPair_11]; simp [Matrix.one_apply, Fin.castAdd_inj]
    | right j =>
      rw [lowerBlockPair_12, Units.val_one, Matrix.one_apply_ne]
      exact fun h => by have := congrArg Fin.val h; simp at this; omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      rw [lowerBlockPair_21, Units.val_one, Matrix.one_apply_ne]
      · rfl
      · exact fun h => by have := congrArg Fin.val h; simp at this; omega
    | right j =>
      rw [lowerBlockPair_22, Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
      simp

theorem lowerBlockPair_diag_inv (c : lowerTriangularSubgroup 1 F) :
    (lowerBlockPair (1 : Langlands.GeneralLinear (m + 1) F) 0 c :
        Langlands.GeneralLinear (m + 1 + 1) F)⁻¹ =
      lowerBlockPair (1 : Langlands.GeneralLinear (m + 1) F) 0 c⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [lowerBlockPair_mul_lowerBlockPair]
  simp only [mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, mul_inv_cancel]
  exact lowerBlockPair_diag_one

theorem lowerBlockPair_diag_symm (c : lowerTriangularSubgroup 1 F)
    (i j : Fin (m + 1 + 1)) :
    (lowerBlockPair (1 : Langlands.GeneralLinear (m + 1) F) 0 c :
        Langlands.GeneralLinear (m + 1 + 1) F) j i =
      (lowerBlockPair (1 : Langlands.GeneralLinear (m + 1) F) 0 c :
        Langlands.GeneralLinear (m + 1 + 1) F) i j := by
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => rw [lowerBlockPair_11, lowerBlockPair_11]; simp [Matrix.one_apply, eq_comm]
    | right j => rw [lowerBlockPair_12, lowerBlockPair_21]; rfl
  | right i =>
    induction j using Fin.addCases with
    | left j => rw [lowerBlockPair_12, lowerBlockPair_21]; rfl
    | right j => rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]

theorem inverseTranspose_lowerBlockPair_diag (c : lowerTriangularSubgroup 1 F) :
    inverseTranspose (m + 1 + 1) F
        (lowerBlockPair (1 : Langlands.GeneralLinear (m + 1) F) 0 c) =
      lowerBlockPair (1 : Langlands.GeneralLinear (m + 1) F) 0 c⁻¹ := by
  apply Units.ext
  ext i j
  rw [inverseTranspose_entry, lowerBlockPair_diag_inv, lowerBlockPair_diag_symm]

end GLOne

section Canonical

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance coreTestFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance coreTestValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance coreTestLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance coreTestFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance coreTestFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance coreTestGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance coreTestGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable {m : ℕ}

/-- `f̃'` is right equivariant under `diag(I, c)`, `c ∈ O^×`, with the weight `μ⁻¹`, when `f'`
is right equivariant under `diag(I, c)` with the character `μ`. -/
theorem secondDual_lowerBlockPair (ψ : UnitaryAdditiveCharacter F.Carrier)
    (f' : InverseWhittakerFunctions ψ (m + 1)) (μ : F.Carrierˣ →* ℂˣ)
    (hequiv : ∀ (g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier)
      (c : lowerTriangularSubgroup 1 F.Carrier), IsIntegralUnit (c.val 0 0) →
        f'.val (g * lowerBlockPair (1 : Langlands.GeneralLinear (m + 1) F.Carrier) 0 c) =
          (μ (determinant c.val) : ℂ) * f'.val g)
    (y : Langlands.GeneralLinear (m + 1 + 1) F.Carrier) (c : lowerTriangularSubgroup 1 F.Carrier)
    (hc : c.val 0 0 ∈ (ValuativeRel.valuation F.Carrier).integer)
    (hc' : (c.val 0 0)⁻¹ ∈ (ValuativeRel.valuation F.Carrier).integer) :
    (secondDualFunction ψ (m + 1) f').val
        (y * (lowerBlockPair 1 0 c : Langlands.GeneralLinear (m + 1 + 1) F.Carrier)) =
      invCharWeight μ (c.val 0 0) * (secondDualFunction ψ (m + 1) f').val y := by
  classical
  have hne := lowerTriangular_entry_ne_zero c
  rw [secondDualFunction_apply, secondDualFunction_apply, map_mul, ← mul_assoc,
    inverseTranspose_lowerBlockPair_diag]
  have hu : IsIntegralUnit ((c⁻¹ : lowerTriangularSubgroup 1 F.Carrier).val 0 0) := by
    rw [InvMemClass.coe_inv, gl_one_inv_apply]
    exact ⟨inv_ne_zero hne, hc', by rwa [inv_inv]⟩
  rw [hequiv _ _ hu]
  simp only [invCharWeight, hne, ne_eq, not_false_eq_true, ↓reduceDIte]
  rw [InvMemClass.coe_inv, map_inv, map_inv, determinant_lowerTriangular_eq, Units.val_inv_eq_inv_val]

/-- An element of order one lies in the maximal ideal. -/
theorem inPow_one_of_ord_eq_one {ϖ : F.Carrier} (hϖ0 : ϖ ≠ 0)
    (hϖ : F.canonicalTopologicalData.ord ϖ = 1) : InPow 1 ϖ := by
  set T := F.canonicalTopologicalData with hT
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  have hO : ϖ ∈ (ValuativeRel.valuation F.Carrier).integer := by
    apply (T.normalizedAbs_le_one_iff_mem_integers ϖ).mp
    rw [T.normalizedAbs_of_ne_zero hϖ0, hϖ]
    exact zpow_le_one_of_nonpos₀ hq.le (by norm_num)
  have hinv : ϖ⁻¹ ∉ (ValuativeRel.valuation F.Carrier).integer := by
    intro h
    have h1 := (T.normalizedAbs_le_one_iff_mem_integers ϖ⁻¹).mpr h
    rw [T.normalizedAbs_of_ne_zero (inv_ne_zero hϖ0), T.ord_inv, hϖ, neg_neg, zpow_one] at h1
    linarith
  refine ⟨⟨ϖ, hO⟩, ?_, rfl⟩
  rw [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  apply hinv
  have h1 : (((u⁻¹ : (ValuativeRel.valuation F.Carrier).integerˣ) :
      (ValuativeRel.valuation F.Carrier).integer) : F.Carrier) * ϖ = 1 := by
    have := congrArg (fun x : (ValuativeRel.valuation F.Carrier).integer => (x : F.Carrier))
      u.inv_mul
    simpa [hu] using this
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact ((u⁻¹ : (ValuativeRel.valuation F.Carrier).integerˣ) :
    (ValuativeRel.valuation F.Carrier).integer).property

/-- A quasicharacter with `a(χ) ≤ n`, `n ≥ 1`, is trivial on `1 + 𝔭^n`. -/
theorem trivialOnPrincipalUnits_of_conductor_le
    (χ : Quasicharacter F.Carrier) {n : ℕ} (hn : 0 < n)
    (h : F.canonicalTopologicalData.multiplicativeConductor χ ≤ n) :
    TrivialOnPrincipalUnits (χ : F.Carrierˣ →* ℂˣ) n := by
  intro u ⟨y, hy, hu⟩
  obtain ⟨E, hE, hEY⟩ := UnequalRankMirabolicUnitTest.exists_mem_principalLevelSubgroup
    (F := F.Carrier) (m := 0) hn (fun _ _ => (u : F.Carrier)) (fun i l => by
      rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero l, Matrix.one_apply_eq, hu, add_sub_cancel_left]
      exact ⟨y, hy, rfl⟩)
  have hdet := determinant_mem_principalUnits F (g := E) hE
  have hEu : determinant E = u := by
    apply Units.ext
    rw [det_gl_one_val, hEY]
  rw [hEu] at hdet
  exact (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le χ n).mpr h u hdet

end Canonical

end Langlands.RankinSelberg.HighlyRamified
