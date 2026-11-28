import Langlands.Global.AdelicCuspidalFibreVector
import Langlands.Global.AdelicLeviFibreSmoothingGrowth

/-! # Finite assembly of a continuous projection from Levi fibre vectors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ fam.M J)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F (fam.M J))).IsMulRightInvariant]

local notation "A" => AdelicGroupPoints F G
local notation "M" => fam.M J
local notation "hM" => IsRationalLeviSubgroup.isConnectedReductive
  (ParabolicRootPresentationData.IsCompatible.levi (fam.isCompatible J))
local notation "AM" => AdelicGroupPoints F M
local notation "A₁" => normOneSubgroup F M
local notation "X₁" => NormOneRationalQuotient F M
local notation "Q" => PositiveRationalQuotient F M T i
local notation "V" => Lp ℂ 2 (positiveRationalQuotientHaarMeasure F M T i)
local notation "S" => fullAEL2CuspidalSubmodule F M parabolicDynamic hM T i hi I e hc
local notation "Pos" => intrinsicSubgroup F T
local notation "pp" => positivePointMap F M T i
local notation "νP" => normalizedPositiveHaarMeasure F M T i hi I e hc
local notation "μ₁" => normOneRationalQuotientHaarMeasure F M
local notation "δ" => fam.leviModulus J
local notation "d" => (fun b : Pos => Complex.ofReal ((δ (pp b) : ℝ)⁻¹))
local notation "ι" => map F M G (fam.l J ≫ fam.p J)
local notation "Γ" => parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)

variable {n : ℕ} (β : Fin n → C_c(AdelicGroupPoints F G, ℂ))
  (k : Fin n → AdelicGroupPoints F G) (φ : AdelicGroupPoints F G → ℂ) (c : ℝ)

/-- At each fixed base point the finite sum of cuspidal fibre vectors represents the
recentered unfolding, with `c` the Iwasawa integration factor. -/
def finiteLeviFibreVector (j : Fin n) (b : Pos) : S :=
  (c : ℂ) • ∑ l, cuspidalFibreVector hM T i hi I e hc
    (fam.radicalKernelCc J (β l) (k j) 1) (fam.leviFibre J φ (k l)) d b

/-- Smooth the representing vectors against the corresponding radical kernels and sum over
the base points. -/
def finiteLeviFibreProjection (g : A) : ℂ :=
  (c : ℂ) • ∑ j, fam.leviFibreSmoothing J T i hi I e hc (β j)
    (fun b => (fam.finiteLeviFibreVector J T i hi I e hc β k φ c j b).val) g

/-- The vector integrals converge, and each vector varies continuously with polynomial norm
growth in the positive parameter. All vectors use the same degree. -/
theorem finiteLeviFibreVector_properties (hDecay : NormOnePartialConvolutionRapidDecayStatement.{u})
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hK : ∀ j l, IsAdelicTestFunction F M (fam.radicalKernelCc J (β l) (k j) 1))
    (hφ : Continuous φ) (hφInv : IsLeftInvariantUnder F G Γ φ) (hφGrowth : HasHeightGrowth rho φ) :
    (∀ j l b, Integrable (cuspidalFibreVectorIntegrand hM T i hi I e hc
      (fam.radicalKernelCc J (β l) (k j) 1) (fam.leviFibre J φ (k l)) d b) (Measure.prod νP μ₁)) ∧
    ∃ r : ℕ, ∀ j, Continuous (fam.finiteLeviFibreVector J T i hi I e hc β k φ c j) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ b,
        ‖fam.finiteLeviFibreVector J T i hi I e hc β k φ c j b‖ ≤
          B * adelicHeight F M ((fam.l J ≫ fam.p J) ≫ rho) (pp b) ^ r := by
  let rhoM := (fam.l J ≫ fam.p J) ≫ rho
  let : IsClosedImmersion rho.hom.hom.left := hrho
  let : IsClosedImmersion (fam.l J).hom.hom.left := (fam.isCompatible J).levi.isClosedSubgroup
  let : IsClosedImmersion (fam.p J).hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup
  have hrhoM : IsClosedSubgroup rhoM := by
    change IsClosedImmersion ((fam.l J ≫ fam.p J) ≫ rho).hom.hom.left
    simp only [Grp.comp_hom_hom, Over.comp_left]
    infer_instance
  have hd : Continuous (d : Pos → ℂ) := Complex.continuous_ofReal.comp
    ((NNReal.continuous_coe.comp ((fam.continuous_leviModulus J).comp (pp).continuous)).inv₀
      fun b => (NNReal.coe_pos.mpr (fam.leviModulus_pos J (pp b))).ne')
  obtain ⟨C, R, hC, _, hbound⟩ := hφGrowth
  let r := ⌈R⌉₊
  let H := adelicHeight F G rho
  let HM := adelicHeight F M rhoM
  have hH (g : A) : 0 ≤ H g := zero_le_one.trans (one_le_adelicHeight F G rho hN g)
  have hpow (g : A) : ‖φ g‖ ≤ C * H g ^ r := by
    rw [← Real.rpow_natCast]
    exact (hbound g).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (one_le_adelicHeight F G rho hN g) (Nat.le_ceil R)) hC)
  have hφbd (l : Fin n) (m : AM) :
      ‖fam.leviFibre J φ (k l) m‖ ≤ (C * H (k l) ^ r) * HM m ^ r := by
    calc
      ‖fam.leviFibre J φ (k l) m‖ ≤ C * H (ι m * k l) ^ r := hpow _
      _ ≤ C * (H (ι m) * H (k l)) ^ r := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hH _) (adelicHeight_mul_le F G rho hN _ _) _) hC
      _ = (C * H (k l) ^ r) * HM m ^ r := by
        change C * (adelicHeight F G rho (ι m) * H (k l)) ^ r =
          (C * H (k l) ^ r) * adelicHeight F M ((fam.l J ≫ fam.p J) ≫ rho) m ^ r
        rw [mul_pow, adelicHeight_map_eq_adelicHeight_comp]
        ring
  have hvec (j l : Fin n) := cuspidalFibreVector_properties hM T i hi I e hc hDecay rhoM hN hrhoM
    (fam.radicalKernelCc J (β l) (k j) 1) (fam.leviFibre J φ (k l)) d (hK j l)
    (fam.continuous_leviFibre J hφ (k l))
    (fun a m => fam.isLeftInvariantUnder_leviFibre J hφInv (k l) _ ⟨a, rfl⟩ m)
    hd r (C * H (k l) ^ r) (mul_nonneg hC (pow_nonneg (hH _) _)) (hφbd l)
  refine ⟨fun j l => (hvec j l).1, r, fun j => ⟨?_, ?_⟩⟩
  · exact (continuous_finsetSum Finset.univ fun l _ => (hvec j l).2.1).const_smul (c : ℂ)
  · choose B hB0 hB using fun l => (hvec j l).2.2
    refine ⟨‖(c : ℂ)‖ * ∑ l, B l, mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun l _ => hB0 l),
      fun b => ?_⟩
    unfold finiteLeviFibreVector
    rw [norm_smul, mul_assoc, Finset.sum_mul]
    exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun l _ => hB l b)) (norm_nonneg _)

/-- The scalar pairing of a finite vector is the sum of the recentered fibre integrals. -/
theorem inner_finiteLeviFibreVector (j : Fin n) (b : Pos) (v : S)
    (hInt : ∀ l, Integrable (cuspidalFibreVectorIntegrand hM T i hi I e hc
      (fam.radicalKernelCc J (β l) (k j) 1) (fam.leviFibre J φ (k l)) d b) (Measure.prod νP μ₁)) :
    inner ℂ v (fam.finiteLeviFibreVector J T i hi I e hc β k φ c j b) =
      c • ∑ l, ∫ t, ∫ ξ : X₁,
        let y := ((Quotient.out ξ : A₁) : AM)
        d t * fam.leviFibre J φ (k l) (y * (pp b * pp t)) *
          starRingEnd ℂ (normOnePartialConvolution T i (fam.radicalKernelCc J (β l) (k j) 1)
            (v.val : Q → ℂ) (y * pp t)) ∂μ₁ ∂νP := by
  let W (l : Fin n) : S := cuspidalFibreVector hM T i hi I e hc
    (fam.radicalKernelCc J (β l) (k j) 1) (fam.leviFibre J φ (k l)) d b
  calc
    inner ℂ v (fam.finiteLeviFibreVector J T i hi I e hc β k φ c j b) =
        (c : ℂ) * inner ℂ v (∑ l, W l) := inner_smul_right (𝕜 := ℂ) v _ (c : ℂ)
    _ = c • ∑ l, inner ℂ v (W l) := by
      rw [Complex.real_smul]
      exact congrArg ((c : ℂ) * ·) (inner_sum (𝕜 := ℂ) Finset.univ W v)
    _ = _ := congrArg (c • ·) (Finset.sum_congr rfl fun l _ =>
      inner_cuspidalFibreVector hM T i hi I e hc _ _ _ _ v (hInt l))

/-- Smoothing the finite family of vectors gives a left-invariant continuous function of
moderate growth on the parabolic quotient. -/
theorem isModerateContinuousOnParabolic_finiteLeviFibreProjection
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (K : Subgroup A) (hK : IsIwasawaCompact (fam.p J) K)
    (hvec : ∃ r : ℕ, ∀ j, Continuous (fam.finiteLeviFibreVector J T i hi I e hc β k φ c j) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ b,
        ‖fam.finiteLeviFibreVector J T i hi I e hc β k φ c j b‖ ≤
          B * adelicHeight F M ((fam.l J ≫ fam.p J) ≫ rho) (pp b) ^ r) :
    fam.IsModerateContinuousOnParabolic rho J (fam.finiteLeviFibreProjection J T i hi I e hc β k φ c) := by
  obtain ⟨r, hr⟩ := hvec
  let w (j : Fin n) (b : Pos) : V := (fam.finiteLeviFibreVector J T i hi I e hc β k φ c j b).val
  let f (j : Fin n) := fam.leviFibreSmoothing J T i hi I e hc (β j) (w j)
  have hInv (j : Fin n) := fam.isLeftInvariantUnder_leviFibreSmoothing J T i hi I e hc (β j) (w j)
  have hC (j : Fin n) := fam.continuous_leviFibreSmoothing J T i hi I e hc (β j) (w j)
    (continuous_subtype_val.comp (hr j).1)
  have hG (j : Fin n) : HasHeightGrowth rho (f j) := by
    obtain ⟨B, hB, hbound⟩ := (hr j).2
    exact fam.hasHeightGrowth_leviFibreSmoothing J T i hi I e hc rho hN hrho K hK (β j) (w j) B hB r hbound
  refine ⟨?_, (continuous_finsetSum Finset.univ fun j _ => hC j).const_smul (c : ℂ), ?_⟩
  · intro m hm g
    unfold finiteLeviFibreProjection
    exact congrArg ((c : ℂ) • ·) (Finset.sum_congr rfl fun j _ => hInv j m hm g)
  · apply (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).mpr
    have heq : fam.finiteLeviFibreProjection J T i hi I e hc β k φ c = (c : ℂ) • ∑ j, f j := by
      funext g
      simp only [finiteLeviFibreProjection, Pi.smul_apply, Finset.sum_apply, f, w]
    rw [heq]
    apply HasHeightGrowth.smul
    generalize Finset.univ (α := Fin n) = s
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using HasHeightGrowth.zero (rho := rho)
    | insert j s hj ih => rw [Finset.sum_insert hj]; exact (hG j).add hN ih

end Langlands.Global.StandardParabolicFamily
