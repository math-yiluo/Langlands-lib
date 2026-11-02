import Langlands.Representation.RankinSelberg.TwoBlockDominantMatrixGrowth
import Langlands.Representation.RankinSelberg.TwoBlockDominantOriginalCone
import Langlands.Representation.RankinSelberg.TwoBlockDominantKernelRegularity

/-! # A uniform torus majorant for the actual dominant raw kernel -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear Whittaker HarmonicAnalysis TwoBlockDeformation TwoBlockJacquet
  TwoBlockConvergence TwoBlockLowerFixedSlice TwoBlockLowerUnipotentQuotient
open scoped BigOperators

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance torusMajorantTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance torusMajorantValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance torusMajorantLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

variable {t r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- The ambient coefficient growth base can be chosen before the complementary
rectangle dimensions and all their coefficient-image tests. -/
theorem exists_coefficient_rectangle_growth_uniform
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (j k : ℕ) (hr : r = t + (j + k + 1)),
      IsCoefficientRectangleGrowth F h hr ψ π lambda B := by
  obtain ⟨B, hB, hcoeff⟩ := exists_coefficient_growth F ψ π hπ lambda
  refine ⟨B * B, one_le_mul_of_one_le_of_one_le hB hB, fun j k hr Wtest => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hcoeff Wtest
  obtain ⟨N, hN⟩ :=
    exists_torus_rectangle_box_support F ψ h hr π hπ.1.1 lambda Wtest
  refine ⟨C * B ^ N, by positivity, fun lam c x y hc => ?_⟩
  by_cases hw : Wtest.val.val (matrix h hr (Iwasawa.torus
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c) x y) = 0
  · rw [hw, norm_zero]
    positivity
  obtain ⟨hx, hy⟩ := hN lam c x y hc hw
  have htorus := isEntryBounded_torus F (uniformizerUnit_isUniformizingElement F)
    lam (torusSize lam) (torusSize_bounds lam)
  have hc' : IsEntryBounded
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) 0 c := by
    have hi := (mem_integralOpen F c).mp hc
    intro i l
    simpa only [pow_zero, one_mul] using And.intro (hi.1 i l) (hi.2 i l)
  have hg := htorus.mul hc'
  rw [add_zero] at hg
  have hb := hC _ _ (matrix_isEntryBounded F h hr hg hx hy)
  calc
    _ ≤ C * B ^ (N + torusSize lam + torusSize lam) := hb
    _ = _ := by simp only [pow_add, mul_pow]; ring

/-- One growth base precedes every real twist, section, complementary rectangle
dimension and coefficient-image test. Nonzero raw values lie in both explicit
rectangle boxes and one opposing cone. -/
def IsRawKernelTorusMajorant
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (a : Fin t) (B : ℝ) : Prop :=
  ∀ (u : ℝ) (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
    (j k : ℕ) (hr : r = t + (j + k + 1))
    (Wtest : (coefficientModel π lambda).toSubmodule),
    ∃ (C : ℝ) (N M : ℕ), 0 ≤ C ∧
      ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F.Carrier)
        (x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier)
        (y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier),
        c ∈ integralOpen F t →
        let g := (blockRotation h F.Carrier)⁻¹ * Iwasawa.torus
          (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c
        let K := rawKernel
          (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i))
          f Wtest.val hr g x y
        ‖K‖ ≤ C * B ^ torusSize lam *
          (F.canonicalTopologicalData.residueCardinality : ℝ) ^
            (-u * (twistDegree (Finset.Iic a.castSucc) lam : ℝ)) ∧
        (K ≠ 0 → OppositeCone M (Finset.Iic a.castSucc) lam ∧
          x ∈ box F (m 0 + 1) k (N + torusSize lam) ∧
          y ∈ box F j (m 1 + 1) (N + torusSize lam))

/-- The actual raw product has a uniform geometric bound and simultaneous
cone and rectangle support, with no integrability assumption. -/
theorem exists_rawKernel_torus_majorant
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (a : Fin t) (ha : a.val = m 1) :
    ∃ B : ℝ, 1 ≤ B ∧ IsRawKernelTorusMajorant F h ψ π lambda τ ell a B := by
  obtain ⟨Bw, hBw, hcoeff⟩ := exists_coefficient_rectangle_growth_uniform F h ψ π hπ lambda
  obtain ⟨Bs, hBs, hsection⟩ := exists_rotated_section_growth F h ψ τ hτ ell a ha
  refine ⟨Bw * Bs, one_le_mul_of_one_le_of_one_le hBw hBs,
    fun u f j k hr Wtest => ?_⟩
  obtain ⟨Cw, hCw0, hCw⟩ := hcoeff j k hr Wtest
  obtain ⟨Cs, hCs0, hCs⟩ := hsection u f
  obtain ⟨N, hN⟩ := exists_torus_rectangle_box_support F ψ h hr π hπ.1.1 lambda Wtest
  obtain ⟨M, hM⟩ := exists_rotated_torus_oppositeCone F h hr ψ π hπ.1.1
    lambda Wtest τ (fun i => (hτ i).1.1) ell u f a ha
  refine ⟨Cw * Cs, N, M, mul_nonneg hCw0 hCs0, fun lam c x y hc => ?_⟩
  dsimp only
  let g := (blockRotation h F.Carrier)⁻¹ * Iwasawa.torus
    (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c
  have he : g = Iwasawa.torus
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
      (rotatedExponents h lam) * ((blockRotation h F.Carrier)⁻¹ * c) := by
    dsimp only [g]
    rw [blockRotation_inv_mul_torus, mul_assoc]
  have hc' := blockRotation_inv_mul_mem_integralOpen F h hc
  have hw := hCw (rotatedExponents h lam) ((blockRotation h F.Carrier)⁻¹ * c) x y hc'
  rw [← he, torusSize_rotatedExponents] at hw
  constructor
  · change ‖scalarSection _ f g 1 * Wtest.val.val (matrix h hr g x y)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ (Cs * Bs ^ torusSize lam *
          (F.canonicalTopologicalData.residueCardinality : ℝ) ^
            (-u * (twistDegree (Finset.Iic a.castSucc) lam : ℝ))) *
          (Cw * Bw ^ torusSize lam) :=
        mul_le_mul (hCs lam c hc) hw (norm_nonneg _) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  · intro hne
    change scalarSection _ f g 1 * Wtest.val.val (matrix h hr g x y) ≠ 0 at hne
    obtain ⟨hsne, hwne⟩ := mul_ne_zero_iff.mp hne
    have hboxes := hN (rotatedExponents h lam) ((blockRotation h F.Carrier)⁻¹ * c)
      x y hc' (by simpa only [← he] using hwne)
    rw [torusSize_rotatedExponents] at hboxes
    exact ⟨hM lam c x y hc hwne hsne, hboxes⟩

end Langlands.RankinSelberg.TwoBlockDominantRectangular
