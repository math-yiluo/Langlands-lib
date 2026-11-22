import Langlands.Global.AdelicHeightPowerPolynomialBound
import Langlands.Global.AdelicIntertwiningImaginaryUnitarityReduction
import Mathlib.Topology.Order.Lattice

/-! # Compact translation bounds and weights in Iwasawa height coordinates -/

noncomputable section
set_option autoImplicit false

universe u v

open AlgebraicGeometry CategoryTheory Set
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.AdelicGroupPoints

open RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  {J : Type v}

/-- Finitely many continuous linear coordinates of the Iwasawa height have one uniform
bound on their displacement under right translations by a compact set. -/
def IwasawaHeightCoordinateRightShiftStatement (s : Finset J)
    (ell : J → RealCharacterDual F P →ₗ[ℝ] ℝ) : Prop :=
  (∀ j ∈ s, Continuous (ell j)) →
    ∀ (C : Set (AdelicGroupPoints F G)), IsCompact C →
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (x : AdelicGroupPoints F G), ∀ a ∈ C, ∀ j ∈ s,
      |ell j (hK.height (x * a)) - ell j (hK.height x)| ≤ b

/-- Each height increment is the height of an element in the compact product `K * C`. -/
theorem IsIwasawaCompact.iwasawaHeightCoordinateRightShift (s : Finset J)
    (ell : J → RealCharacterDual F P →ₗ[ℝ] ℝ) :
    IwasawaHeightCoordinateRightShiftStatement hK s ell := by
  intro hell C hC
  let f (g : AdelicGroupPoints F G) := ∑ j ∈ s, |ell j (hK.height g)|
  have hf : Continuous f := continuous_finsetSum _ (fun j hj =>
    ((hell j hj).comp hK.continuous_height).abs)
  obtain ⟨B, hB⟩ := (hK.isCompact.mul hC).bddAbove_image hf.continuousOn
  refine ⟨max 0 B, le_max_left _ _, fun x a ha j hj => ?_⟩
  obtain ⟨k, hk, heq⟩ := hK.exists_height_mul_eq_add x a
  have hka : f (k * a) ≤ B := hB ⟨k * a, mul_mem_mul hk ha, rfl⟩
  rw [heq, map_add, add_sub_cancel_left]
  exact (Finset.single_le_sum (fun j _ => abs_nonneg (ell j (hK.height (k * a)))) hj).trans
    (hka.trans (le_max_right _ _))

variable (F P) in
/-- A log weight given by the maximum of a nonempty finite family of real character pairings. -/
def finiteMaximumLogWeight (s : Finset J) (hs : s.Nonempty)
    (lam : J → RealCharacterParameter F P) (H : RealCharacterDual F P) : ℝ :=
  s.sup' hs (fun j => realParameterPairing F P (lam j) H)

omit [NumberField F] [IsAffine P.X.left] in
private theorem parameterRealPart_realToComplexParameter (lam : RealCharacterParameter F P) :
    parameterRealPart F P (realToComplexParameter P lam) = lam := by
  induction lam using TensorProduct.inductionOn with
  | tmul t χ => simp [realToComplexParameter_tmul]
  | add x y hx hy => simp [hx, hy]

omit [NumberField F] [IsAffine P.X.left] in
private theorem continuous_parameterPairing (lam : RealCharacterParameter F P) :
    Continuous (realParameterPairing F P lam) := by
  have h := Complex.continuous_re.comp
    (continuous_complexParameterPairing_apply (realToComplexParameter P lam))
  simpa only [Function.comp_def, complexParameterPairing_re,
    parameterRealPart_realToComplexParameter] using h

/-- Finite maximum weights are continuous, have polynomial exponential growth, and have
uniformly bounded log displacement for compact right translations. -/
def IwasawaFiniteMaximumWeightStatement {n : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin n))
    (s : Finset J) (hs : s.Nonempty) (lam : J → RealCharacterParameter F P) : Prop :=
  let ell := finiteMaximumLogWeight F P s hs lam
  Continuous ell ∧
    (0 < n → GroupScheme.IsClosedSubgroup rho →
      ∃ A r : ℝ, 0 < A ∧ 0 ≤ r ∧ ∀ g : AdelicGroupPoints F G,
        Real.exp (ell (hK.height g)) ≤ A * adelicHeight F G rho g ^ r) ∧
    (∀ (C : Set (AdelicGroupPoints F G)), IsCompact C →
      ∃ b : ℝ, 0 ≤ b ∧ ∀ (x : AdelicGroupPoints F G), ∀ a ∈ C,
        |ell (hK.height (x * a)) - ell (hK.height x)| ≤ b)

theorem IsIwasawaCompact.iwasawaFiniteMaximumWeight {n : ℕ}
    (rho : GroupScheme.MatrixRepresentation G (Fin n))
    (s : Finset J) (hs : s.Nonempty) (lam : J → RealCharacterParameter F P) :
    IwasawaFiniteMaximumWeightStatement hK rho s hs lam := by
  let ℓ (j : J) := realParameterPairing F P (lam j)
  have hℓ (j : J) : Continuous (ℓ j) := continuous_parameterPairing (lam j)
  refine ⟨Continuous.finset_sup'_apply hs (fun j _ => hℓ j), ?_, ?_⟩
  · intro hn hrho
    choose A r hA hr hbound using fun j =>
      hK.exists_norm_heightPower_le_adelicHeight rho hn hrho (realToComplexParameter P (lam j))
    let j₀ := hs.choose
    have hj₀ : j₀ ∈ s := hs.choose_spec
    refine ⟨s.sup' hs A, s.sup' hs r, (hA j₀).trans_le (Finset.le_sup' A hj₀),
      (hr j₀).trans (Finset.le_sup' r hj₀), fun g => ?_⟩
    change Real.exp (s.sup' hs (fun j => ℓ j (hK.height g))) ≤ _
    rw [Finset.apply_sup'_eq_sup'_comp hs Real.exp
      (fun a b => Monotone.map_sup Real.exp_monotone a b)]
    apply Finset.sup'_le
    intro j hj
    have hg := hbound j g
    rw [hK.norm_heightPower, parameterRealPart_realToComplexParameter] at hg
    refine hg.trans (mul_le_mul (Finset.le_sup' A hj) ?_ ?_ ?_)
    · exact Real.rpow_le_rpow_of_exponent_le (one_le_adelicHeight F G rho hn g) (Finset.le_sup' r hj)
    · exact Real.rpow_nonneg (zero_le_one.trans (one_le_adelicHeight F G rho hn g)) _
    · exact (hA j₀).le.trans (Finset.le_sup' A hj₀)
  · intro C hC
    obtain ⟨b, hb, hshift⟩ := hK.iwasawaHeightCoordinateRightShift s ℓ (fun j _ => hℓ j) C hC
    refine ⟨b, hb, fun x a ha => ?_⟩
    let m (H : RealCharacterDual F P) := finiteMaximumLogWeight F P s hs lam H
    have hle (H H' : RealCharacterDual F P) (h : ∀ j ∈ s, ℓ j H - ℓ j H' ≤ b) :
        m H - m H' ≤ b := by
      apply sub_le_iff_le_add.mpr
      apply Finset.sup'_le
      intro j hj
      exact (sub_le_iff_le_add.mp (h j hj)).trans
        (add_le_add_right (Finset.le_sup' (fun i => ℓ i H') hj) b)
    have h₁ := hle _ _ (fun j hj => (abs_le.mp (hshift x a ha j hj)).2)
    have h₂ := hle (hK.height x) (hK.height (x * a)) (fun j hj => by
      linarith [(abs_le.mp (hshift x a ha j hj)).1])
    exact abs_le.mpr ⟨by linarith, h₁⟩

omit [NumberField F] [IsAffine P.X.left] in
/-- One linear weight plus absolute values of finitely many linear coordinates is the
maximum of the weights obtained by choosing each of the signs. -/
theorem finiteMaximumLogWeight_signs [Fintype J] [DecidableEq J] (base : RealCharacterParameter F P)
    (center : J → RealCharacterParameter F P) (H : RealCharacterDual F P) :
    finiteMaximumLogWeight F P (Finset.univ : Finset (J → Bool)) Finset.univ_nonempty
        (fun s => base + ∑ j, if s j then center j else -center j) H =
      realParameterPairing F P base H + ∑ j, |realParameterPairing F P (center j) H| := by
  classical
  let t (j : J) := realParameterPairing F P (center j) H
  have he (s : J → Bool) :
      realParameterPairing F P (base + ∑ j, if s j then center j else -center j) H =
        realParameterPairing F P base H + ∑ j, if s j then t j else -t j := by
    simp only [map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    cases s j <;> simp [t]
  apply le_antisymm
  · apply Finset.sup'_le
    intro s _
    rw [he]
    apply add_le_add_right
    exact Finset.sum_le_sum fun j _ => by cases s j <;> simp [t, le_abs_self, neg_le_abs]
  · let s (j : J) : Bool := decide (0 ≤ t j)
    refine Finset.le_sup'_of_le _ (Finset.mem_univ s) ?_
    rw [he]
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro j _
    change |t j| ≤ if s j then t j else -t j
    by_cases hj : 0 ≤ t j
    · simp [s, hj, abs_of_nonneg hj]
    · simp [s, hj, abs_of_neg (lt_of_not_ge hj)]

end Langlands.Global.AdelicGroupPoints
