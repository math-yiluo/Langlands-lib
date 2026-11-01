import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceSupport
import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceCoordinates
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-! # Internal block-root support for actual induced sections -/

noncomputable section

open scoped BigOperators

namespace Langlands.RankinSelberg.TwoBlockDominantSectionSupport

open HarmonicAnalysis Whittaker GeneralLinear TwoBlockJacquet TwoBlockDeformation
  TwoBlockConvergence TwoBlockLowerFixedSlice

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance sectionSupportTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance sectionSupportValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance sectionSupportLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

private theorem rootBounded_mono {n L L' : ℕ} {lam : Fin (n + 1) → ℤ}
    (h : RootBounded L lam) (hL : L ≤ L') : RootBounded L' lam := by
  intro i
  exact (h i).trans (add_le_add_right (Int.ofNat_le.mpr hL) _)

/-- Every tensor contraction has one internal root bound in both blocks,
uniformly in the block diagonal exponents and right integral factors. -/
theorem exists_blockTensor_rootBounded
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsSmooth (τ i)) (ell : ∀ i, glFunctionals ψ (m i) (τ i))
    (w : PiTensorProduct ℂ W) :
    ∃ L : ℕ, ∀ (lam : ∀ i, Fin (m i + 1) → ℤ)
      (c : (succBlockShape m h).Levi F.Carrier),
      (∀ i, c i ∈ integralOpen F (m i)) →
      tensorContraction (fun i => (ell i).val)
        ((succBlockShape m h).blockTensor τ
          (fun i => Iwasawa.torus
            (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) (lam i) * c i)
          w) ≠ 0 →
      ∀ i, RootBounded L (lam i) := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    choose L hL using fun i => exists_coefficient_rootBounded F ψ (τ i) (hτ i) (ell i)
      (modelMap (τ i) (ell i) (v i))
    refine ⟨Finset.univ.sup L, fun lam c hc hne i => ?_⟩
    have hprod : (∏ i, (ell i).val (τ i (Iwasawa.torus
        (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) (lam i) * c i)
        (v i))) ≠ 0 := by
      intro hz
      apply hne
      rw [map_smul, map_smul, BlockShape.blockTensor_tprod, tensorContraction_tprod, hz,
        smul_zero]
    have hi := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
    exact rootBounded_mono (hL i (lam i) (c i) (hc i) hi)
      (Finset.le_sup (Finset.mem_univ i))
  | add w₁ w₂ h₁ h₂ =>
    obtain ⟨L₁, hL₁⟩ := h₁
    obtain ⟨L₂, hL₂⟩ := h₂
    refine ⟨max L₁ L₂, fun lam c hc hne i => ?_⟩
    by_cases hne₁ : tensorContraction (fun i => (ell i).val)
        ((succBlockShape m h).blockTensor τ
          (fun i => Iwasawa.torus
            (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) (lam i) * c i)
          w₁) = 0
    · have hne₂ : tensorContraction (fun i => (ell i).val)
          ((succBlockShape m h).blockTensor τ
            (fun i => Iwasawa.torus
              (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) (lam i) * c i)
            w₂) ≠ 0 := by
        intro hz
        apply hne
        rw [map_add, map_add, hne₁, hz, add_zero]
      exact rootBounded_mono (hL₂ lam c hc hne₂ i) (le_max_right _ _)
    · exact rootBounded_mono (hL₁ lam c hc hne₁ i) (le_max_left _ _)

/-- Finitely many section values on the integral subgroup share one root bound. -/
theorem exists_integral_blockTensor_rootBounded
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (τ σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsSmooth (τ i)) (ell : ∀ i, glFunctionals ψ (m i) (τ i))
    (f : Sections F h σ) :
    ∃ L : ℕ, ∀ (c : GeneralLinear (t + 1) F.Carrier), c ∈ integralOpen F t →
      ∀ (lam : ∀ i, Fin (m i + 1) → ℤ)
        (d : (succBlockShape m h).Levi F.Carrier),
        (∀ i, d i ∈ integralOpen F (m i)) →
        tensorContraction (fun i => (ell i).val)
          ((succBlockShape m h).blockTensor τ
            (fun i => Iwasawa.torus
              (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) (lam i) * d i)
            (sectionEval F h σ f c)) ≠ 0 →
        ∀ i, RootBounded L (lam i) := by
  classical
  have hfin := finite_image_sectionEval_integralOpen F h σ f
  choose Lw hLw using fun w => exists_blockTensor_rootBounded F h ψ τ hτ ell w
  refine ⟨hfin.toFinset.sup Lw, fun c hc lam d hd hne i => ?_⟩
  have hw : sectionEval F h σ f c ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨c, hc, rfl⟩
  exact rootBounded_mono (hLw _ lam d hd hne i) (Finset.le_sup hw)

/-- A uniform internal block-root bound for nonzero values of an actual
oppositely twisted scalar section on the original torus times the integral subgroup. -/
def IsSectionTorusRootBounded
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) (u : ℝ)
    (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u)) (L : ℕ) : Prop :=
  ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F.Carrier),
    c ∈ integralOpen F t →
    scalarSection (fun i => (ell i).val) f
      (Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c)
      1 ≠ 0 →
    ∀ i, RootBounded L (fun a => lam ((succBlockShape m h).index i a))

/-- Every actual smooth block section admits a uniform internal root bound. -/
theorem exists_section_torus_rootBounded
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsSmooth (τ i)) (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) (u : ℝ)
    (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u)) :
    ∃ L, IsSectionTorusRootBounded F h ψ τ ell u f L := by
  let ellD : ∀ i, glFunctionals (ψ.scale (-1)) (m i) (τ i) :=
    fun i => functionalsCongr (standardCharacter_scale_neg_one ψ (m i)).symm (ell i)
  obtain ⟨L, hL⟩ := exists_integral_blockTensor_rootBounded F h (ψ.scale (-1)) τ
    (twoBlockOppositeTwistBlocks F m τ u) hτ ellD f
  refine ⟨L, fun lam c hc hne => ?_⟩
  apply hL c hc (fun i a => lam ((succBlockShape m h).index i a)) 1
    (fun i => (integralOpen F (m i)).one_mem)
  intro hz
  apply hne
  have hcov := scalarSection_covariant (fun i => (ell i).val) f
    ((succBlockShape m h).oppositeLeviInParabolic F.Carrier (torusLevi F h lam))
    ((succBlockShape m h).oppositeLeviProjection_section F.Carrier (torusLevi F h lam)) c 1
  rw [BlockShape.oppositeLeviInParabolic_val, one_mul, torusLevi_embedding] at hcov
  rw [hcov, scalarSection_def,
    tensorContraction_blockTensor_twist F h τ u (fun i => (ell i).val)]
  have hz' : tensorContraction (fun i => (ell i).val)
      ((succBlockShape m h).blockTensor τ (torusLevi F h lam)
        (sectionEval F h (twoBlockOppositeTwistBlocks F m τ u) f c)) = 0 := by
    unfold TwoBlockLowerFixedSlice.torusLevi
    simpa only [Pi.one_apply, mul_one, ellD, functionalsCongr] using hz
  rw [hz', mul_zero, mul_zero]

end Langlands.RankinSelberg.TwoBlockDominantSectionSupport
