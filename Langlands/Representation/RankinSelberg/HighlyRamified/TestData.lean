import Langlands.Representation.RankinSelberg.HighlyRamified.UnitInversion
import Langlands.Representation.RankinSelberg.HighlyRamified.ISide
import Langlands.Representation.RankinSelberg.HighlyRamified.DualValue

/-!
# The test data of Jacquet–Shalika (4.4.4), (4.4.6)–(4.4.8), (4.4.18)

The test function is `Φ(u, z) = Φ₁(u) Φ₂(z)` on `F × F^(m+1)`, summed over `T = T₁ × T₂`. Here
`Φ₂` is the weight (4.4.18) (`dualWeight`) over representatives `T₂` of `ϖ^(-c) O^(m+1)` modulo
`O^(m+1)`, and `Φ₁` inverts a prescribed function `S₁` on `O` (`exists_unit_inversion`). This
module proves the properties used elsewhere:

* the restricted Fourier transform of `Φ₂` is supported on `(𝔭^f)^(m+1)` once `c ≥ 2f`
  (condition (8));
* the finite Fourier transform of `Φ` factors as `S₁(ξ₀) S₂(ξ_tail)` on integral `ξ`;
* every point of `T` where `Φ` does not vanish is a deep first row (the `I`-side condition
  (4.4.19)–(4.4.21)), once `c ≥ f + b`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis

universe uF

section Powers

variable {F : Type uF} [Field F] [ValuativeRel F]

theorem InPow.mono {f c : ℕ} (hfc : f ≤ c) {x : F} (hx : InPow c x) : InPow f x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, Ideal.pow_le_pow_right hfc hy, rfl⟩

theorem InPow.mul {a b : ℕ} {x y : F} (hx : InPow a x) (hy : InPow b y) : InPow (a + b) (x * y) := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨x' * y', by rw [pow_add]; exact Ideal.mul_mem_mul hx' hy', rfl⟩

theorem InPow.pow {x : F} (hx : InPow 1 x) (c : ℕ) : InPow c (x ^ c) := by
  induction c with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ c ih => simpa [pow_succ] using ih.mul hx

theorem InPow.zero_of_integral {x : F} (hx : x ∈ (ValuativeRel.valuation F).integer) :
    InPow 0 x :=
  ⟨⟨x, hx⟩, by simp, rfl⟩

end Powers

section Product

variable {F : Type uF} [Field F] [TopologicalSpace F] {m : ℕ}

open Classical in
/-- The product set `T₁ × T₂ ⊆ F × F^(m+1) = F^(m+2)`. -/
def productTest (T₁ : Finset F) (T₂ : Finset (Fin (m + 1) → F)) : Finset (Fin (m + 2) → F) :=
  (T₁ ×ˢ T₂).image fun q => Fin.cons q.1 q.2

/-- The product weight `Φ(u, z) = Φ₁(u) Φ₂(z)`. -/
def productWeight (Φ₁ : F → ℂ) (Φ₂ : (Fin (m + 1) → F) → ℂ) (z : Fin (m + 2) → F) : ℂ :=
  Φ₁ (z 0) * Φ₂ (Fin.tail z)

omit [Field F] [TopologicalSpace F] in
theorem cons_injective_pair :
    Function.Injective fun q : F × (Fin (m + 1) → F) => (Fin.cons q.1 q.2 : Fin (m + 2) → F) := by
  intro a b h
  have h' : (Fin.cons a.1 a.2 : Fin (m + 2) → F) = Fin.cons b.1 b.2 := h
  have h0 := congrFun h' 0
  have h1 : (Fin.tail (Fin.cons a.1 a.2 : Fin (m + 2) → F) : Fin (m + 1) → F) =
      Fin.tail (Fin.cons b.1 b.2 : Fin (m + 2) → F) := by rw [h']
  simp only [Fin.cons_zero] at h0
  simp only [Fin.tail_cons] at h1
  exact Prod.ext h0 h1

/-- The finite Fourier transform of a product weight factors. -/
theorem finiteFourier_product (ψ : UnitaryAdditiveCharacter F) (T₁ : Finset F)
    (T₂ : Finset (Fin (m + 1) → F)) (Φ₁ : F → ℂ) (Φ₂ : (Fin (m + 1) → F) → ℂ)
    (ξ : Fin (m + 2) → F) :
    finiteFourier ψ (productTest T₁ T₂) (productWeight Φ₁ Φ₂) ξ =
      (∑ u ∈ T₁, Φ₁ u * ψ.complex (u * ξ 0)) *
        ∑ z ∈ T₂, Φ₂ z * ψ.complex (∑ k, z k * ξ k.succ) := by
  classical
  unfold finiteFourier productTest
  rw [Finset.sum_image fun a _ b _ h => cons_injective_pair h, Finset.sum_product,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun z _ => ?_
  simp only [productWeight, Fin.cons_zero, Fin.tail_cons]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [AddChar.map_add_eq_mul]
  ring

end Product

section Deep

variable {F : Type uF} [Field F] [ValuativeRel F] {m : ℕ}

/-- The `I`-side condition: at every point of `T₁ × T₂` where the product weight with
`Φ₂ = dualWeight` does not vanish, the first row is deep (Jacquet–Shalika 1985, (4.4.19)–(4.4.21)),
provided `T₁ ⊆ ϖ^(-b) O`, `ϖ ∈ 𝔭` and `c ≥ f + b`. -/
theorem productTest_isDeepFirstRow {ω : Fˣ →* ℂˣ} {f c b : ℕ} {ϖ : F} (hϖ : InPow 1 ϖ)
    (hc : f + b ≤ c) (T₁ : Finset F)
    (hT₁ : ∀ u ∈ T₁, ϖ ^ b * u ∈ (ValuativeRel.valuation F).integer)
    (T₂ : Finset (Fin (m + 1) → F)) (Φ₁ : F → ℂ) (z : Fin (m + 1 + 1) → F)
    (hz : z ∈ productTest T₁ T₂)
    (hΦ : productWeight Φ₁ (dualWeight ω ϖ c f) z ≠ 0) :
    IsDeepFirstRow f z := by
  classical
  unfold productTest at hz
  obtain ⟨⟨u, z₂⟩, hq, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hu, -⟩ := Finset.mem_product.mp hq
  simp only at hu
  unfold productWeight at hΦ
  simp only [Fin.cons_zero, Fin.tail_cons] at hΦ
  have hdw : dualWeight ω ϖ c f z₂ ≠ 0 := right_ne_zero_of_mul hΦ
  have hcond : (∀ i : Fin (m + 1), i ≠ Fin.last m → InPow f (ϖ ^ c * z₂ i)) ∧
      IsIntegralUnit (ϖ ^ c * z₂ (Fin.last m)) := by
    by_contra h
    exact hdw (unitLastWeight_of_not_cond ω h)
  obtain ⟨hrest, hd⟩ := hcond
  set d := ϖ ^ c * z₂ (Fin.last m) with hdd
  have hlast : (Fin.cons u z₂ : Fin (m + 1 + 1) → F) (Fin.last (m + 1)) = z₂ (Fin.last m) := by
    rw [← Fin.succ_last, Fin.cons_succ]
  have hz₂ : z₂ (Fin.last m) ≠ 0 := by
    intro h0
    apply hd.1
    rw [hdd, h0, mul_zero]
  have hϖc : ϖ ^ c ≠ 0 := by
    intro h0
    apply hd.1
    rw [hdd, h0, zero_mul]
  have hdinv : InPow 0 d⁻¹ := InPow.zero_of_integral hd.2.2
  refine ⟨by rw [hlast]; exact hz₂, ?_, ?_⟩
  · rw [hlast]
    have : 1 / z₂ (Fin.last m) = ϖ ^ c * d⁻¹ := by
      rw [hdd]; field_simp
    rw [this]
    exact ((hϖ.pow c).mul hdinv).mono (by omega)
  · intro j
    rw [hlast]
    refine Fin.cases ?_ (fun k => ?_) j
    · have hsplit : ϖ ^ c = ϖ ^ b * ϖ ^ (c - b) := by
        rw [← pow_add]; congr 1; omega
      have : (Fin.cons u z₂ : Fin (m + 1 + 1) → F) (Fin.castSucc 0) / z₂ (Fin.last m) =
          (ϖ ^ b * u) * ϖ ^ (c - b) * d⁻¹ := by
        have hprod : ϖ ^ b * ϖ ^ (c - b) ≠ 0 := hsplit ▸ hϖc
        have hb : ϖ ^ b ≠ 0 := left_ne_zero_of_mul hprod
        have hcb : ϖ ^ (c - b) ≠ 0 := right_ne_zero_of_mul hprod
        rw [show (Fin.castSucc (0 : Fin (m + 1)) : Fin (m + 1 + 1)) = 0 from rfl, Fin.cons_zero,
          hdd, hsplit]
        field_simp
      rw [this]
      have h1 := ((InPow.zero_of_integral (hT₁ u hu)).mul (hϖ.pow (c - b))).mul hdinv
      exact h1.mono (by omega)
    · have hk : (Fin.castSucc k.succ : Fin (m + 1 + 1)) = (Fin.castSucc k).succ := rfl
      have hne : (Fin.castSucc k : Fin (m + 1)) ≠ Fin.last m := Fin.castSucc_ne_last k
      have : (Fin.cons u z₂ : Fin (m + 1 + 1) → F) (Fin.castSucc k.succ) / z₂ (Fin.last m) =
          (ϖ ^ c * z₂ (Fin.castSucc k)) * d⁻¹ := by
        rw [hk, Fin.cons_succ, hdd]
        field_simp
      rw [this]
      have h1 := (hrest _ hne).mul hdinv
      simpa using h1

end Deep

section Canonical

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance testDataFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance testDataValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance testDataLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance testDataFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance testDataFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩

variable {m : ℕ}

theorem integerLattice_eq_pi :
    (integerLattice F m : Set (Fin (m + 1) → F.Carrier)) =
      Set.pi Set.univ fun _ => ((ValuativeRel.valuation F.Carrier).integer : Set F.Carrier) := by
  ext z
  simp [mem_integerLattice]

theorem integerLattice_le_scaledLattice {ϖ : F.Carrier}
    (hϖ : ϖ ∈ (ValuativeRel.valuation F.Carrier).integer) (c : ℕ) :
    integerLattice F m ≤ scaledLattice F ϖ c m := by
  intro z hz
  rw [mem_scaledLattice]
  rw [mem_integerLattice] at hz
  exact fun i => Subring.mul_mem _ (Subring.pow_mem _ hϖ c) (hz i)

/-- Condition (4.4.8): the restricted Fourier transform of `Φ₂` vanishes at integral `v` unless
every `v_k ∈ 𝔭^f`, provided `c ≥ 2f` and `ϖ ∈ 𝔭`. -/
theorem dualWeight_fourier_eq_zero (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductorAt F ψ) (η : AdditiveHaarMeasure F.Carrier)
    {ω : F.Carrierˣ →* ℂˣ} {f c : ℕ} (hf : 0 < f) (hω : TrivialOnPrincipalUnits ω f)
    {ϖ : F.Carrier} (hϖ0 : ϖ ≠ 0) (hϖ : InPow 1 ϖ) (hc : f + f ≤ c)
    (T : Finset (Fin (m + 1) → F.Carrier))
    (hTK : (T : Set (Fin (m + 1) → F.Carrier)) ⊆ scaledLattice F ϖ c m)
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ integerLattice F m → t = t')
    (hcov : ∀ v ∈ scaledLattice F ϖ c m, ∃ t ∈ T, v - t ∈ integerLattice F m)
    (v : Fin (m + 1) → F.Carrier) (hv : ∀ k, v k ∈ (ValuativeRel.valuation F.Carrier).integer)
    (hnot : ¬ ∀ k, InPow f (v k)) :
    ∑ z ∈ T, dualWeight ω ϖ c f z * ψ.complex (∑ k, z k * v k) = 0 := by
  classical
  obtain ⟨k₀, hk₀⟩ := not_forall.mp hnot
  have hϖO : ϖ ∈ (ValuativeRel.valuation F.Carrier).integer := hϖ.integral
  have hcf : f ≤ c - f := by omega
  have hpow : ∀ n, (ϖ ^ n : F.Carrier) ≠ 0 := fun n => pow_ne_zero _ hϖ0
  -- `ϖ^(f-c) v_(k₀)` is not integral
  have hdeep : (ϖ ^ (c - f))⁻¹ * v k₀ ∉ (ValuativeRel.valuation F.Carrier).integer := by
    intro h
    apply hk₀
    have : v k₀ = ϖ ^ (c - f) * ((ϖ ^ (c - f))⁻¹ * v k₀) := by
      field_simp [hpow (c - f)]
    rw [this]
    have := (hϖ.pow (c - f)).mul (InPow.zero_of_integral h)
    exact (this.mono (by omega))
  obtain ⟨z, hz, hne⟩ := hψ.nontrivial _ hdeep
  set δ : Fin (m + 1) → F.Carrier := Pi.single k₀ (z * (ϖ ^ (c - f))⁻¹) with hδ
  have hδper : ∀ i, InPow f (ϖ ^ c * δ i) := by
    intro i
    by_cases hi : i = k₀
    · subst hi
      have : ϖ ^ c * δ i = ϖ ^ f * z := by
        rw [hδ, Pi.single_eq_same]
        have hcsplit : ϖ ^ c = ϖ ^ f * ϖ ^ (c - f) := by
          rw [← pow_add]; congr 1; omega
        rw [hcsplit]
        field_simp [hpow (c - f)]
      rw [this]
      simpa using (hϖ.pow f).mul (InPow.zero_of_integral hz)
    · rw [hδ, Pi.single_eq_of_ne hi, mul_zero]
      exact ⟨0, Submodule.zero_mem _, rfl⟩
  have hscale : ∀ o ∈ (ValuativeRel.valuation F.Carrier).integer, InPow f (ϖ ^ c * o) :=
    fun o ho => ((hϖ.pow c).mul (InPow.zero_of_integral ho)).mono (by omega)
  have hδK : δ ∈ scaledLattice F ϖ c m := by
    rw [mem_scaledLattice]
    exact fun i => (hδper i).integral
  set g : (Fin (m + 1) → F.Carrier) → ℂ :=
    fun x => dualWeight ω ϖ c f x * ψ.complex (∑ k, x k * v k) with hg
  have hgper : ∀ x l, l ∈ integerLattice F m → g (x + l) = g x := by
    intro x l hl
    rw [mem_integerLattice] at hl
    simp only [hg]
    rw [dualWeight_add hf hω hscale x l hl]
    congr 1
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul]
    rw [UnitaryAdditiveCharacter.complex_apply (x := ∑ k, l k * v k),
      hψ.trivial _ (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hl k) (hv k))]
    simp
  have hgshift : ∀ x, g (x + δ) = g x * ψ.complex (δ k₀ * v k₀) := by
    intro x
    simp only [hg]
    have hdw : dualWeight ω ϖ c f (x + δ) = dualWeight ω ϖ c f x := by
      unfold dualWeight
      have : (fun i => ϖ ^ c * (x + δ) i) =
          (fun i => ϖ ^ c * x i) + fun i => ϖ ^ c * δ i := by
        funext i; simp [mul_add]
      rw [this, unitLastWeight_add hf hω _ _ hδper]
    rw [hdw]
    have hsum : ∑ k, (x + δ) k * v k = ∑ k, x k * v k + δ k₀ * v k₀ := by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single k₀]
      · intro b _ hb; rw [hδ, Pi.single_eq_of_ne hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ k₀) h
    rw [hsum, AddChar.map_add_eq_mul]
    ring
  -- the measure on `F^(m+1)`
  have : SigmaFinite η.measure :=
    InducedTailIntermediate.scalarHaar_sigmaFinite F.canonicalTopologicalData η
  set μ : Measure (Fin (m + 1) → F.Carrier) := Measure.pi fun _ => η.measure with hμ
  have hOm : MeasurableSet ((ValuativeRel.valuation F.Carrier).integer : Set F.Carrier) :=
    (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier)).measurableSet
  have hLm : MeasurableSet (integerLattice F m : Set (Fin (m + 1) → F.Carrier)) := by
    rw [integerLattice_eq_pi]
    exact MeasurableSet.univ_pi fun _ => hOm
  have hOfin : η.measure ((ValuativeRel.valuation F.Carrier).integer : Set F.Carrier) < ⊤ :=
    (isCompact_integer F).measure_lt_top
  have hOpos : 0 < η.measure ((ValuativeRel.valuation F.Carrier).integer : Set F.Carrier) :=
    (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier)).measure_pos _
      ⟨0, Subring.zero_mem _⟩
  have hLμ : μ (integerLattice F m : Set (Fin (m + 1) → F.Carrier)) =
      ∏ _i : Fin (m + 1), η.measure ((ValuativeRel.valuation F.Carrier).integer : Set F.Carrier) := by
    rw [integerLattice_eq_pi, hμ, Measure.pi_pi]
  have hLfin : μ (integerLattice F m : Set (Fin (m + 1) → F.Carrier)) < ⊤ := by
    rw [hLμ]
    exact ENNReal.prod_lt_top fun _ _ => hOfin
  have hLpos : 0 < μ (integerLattice F m : Set (Fin (m + 1) → F.Carrier)) := by
    rw [hLμ]
    exact CanonicallyOrderedAdd.prod_pos.mpr fun _ _ => hOpos
  have hshift := sum_reps_shift μ (scaledLattice F ϖ c m) (integerLattice F m)
    (integerLattice_le_scaledLattice F hϖO c) hLm hLfin hLpos T hTK hT hcov g hgper δ hδK
  simp_rw [hgshift] at hshift
  rw [← Finset.sum_mul] at hshift
  have hne' : ψ.complex (δ k₀ * v k₀) ≠ 1 := by
    rw [hδ, Pi.single_eq_same, UnitaryAdditiveCharacter.complex_apply]
    intro h
    apply hne
    rw [UnitaryAdditiveCharacter.complex_apply, ← mul_assoc]
    exact h
  change ∑ x ∈ T, g x = 0
  have : (∑ x ∈ T, g x) * (ψ.complex (δ k₀ * v k₀) - 1) = 0 := by
    rw [mul_sub, mul_one, hshift, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hne'

end Canonical

end Langlands.RankinSelberg.HighlyRamified
