import Langlands.Analysis.CompactBallSobolev
import Langlands.Automorphic.OperatorBandCoordinateDerivatives

/-! # The Sobolev bound near an actual determinant-band point -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Classical ContDiff NNReal ENNReal Matrix.Norms.Operator
open Set Metric MeasureTheory MeasureTheory.Measure

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global ArchimedeanGL ContinuousRationalFunctions

universe u

variable (F : Type u) [fieldF : Field F] [numberFieldF : NumberField F] (n : ℕ)

local instance localSobolevRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance localSobolevContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance localSobolevFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance localSobolevFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance localSobolevStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (S : OperatorRealization F n)
local instance localSobolevSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- Each actual band point has an open neighborhood with a uniform
pointwise Sobolev bound for the original vectors at the fixed finite level. -/
theorem exists_local_sobolev_of_mem_band
    (hL2 : ∀ v : S.Space,
      MemLp (toQuotient F n S v) 2 ((quotientHaarMeasure F n).restrict (band F n)))
    (J : Subgroup (FiniteAdelicGL F n)) (hJ : IsOpen (J : Set (FiniteAdelicGL F n)))
    (g : AdelicGL F n) (hg : point F n g ∈ band F n) :
    ∃ U : Set (AdelicGL F n), IsOpen U ∧ g ∈ U ∧
      ∃ (D : Finset (EnvelopingAlgebra F n)) (C : ℝ), 0 ≤ C ∧ ∀ v : S.Space,
        (∀ k : J, S.finiteRepresentation (k : FiniteAdelicGL F n) v = v) →
        ∀ y ∈ U, ‖evaluate F n (S.toContinuous v) y‖ ≤
          C * ∑ d ∈ D, ‖toL2 F n S (quotientHaarMeasure F n) hL2 (S.envelopingAction d v)‖ := by
  borelize (AdelicGL F n)
  let A := ArchimedeanMatrix F n
  let aNorm : NormedAddCommGroup A := inferInstanceAs (NormedAddCommGroup (ArchimedeanMatrix F n))
  let aSpace : NormedSpace ℝ A := inferInstanceAs (NormedSpace ℝ (ArchimedeanMatrix F n))
  let aDim : FiniteDimensional ℝ A := inferInstanceAs (FiniteDimensional ℝ (ArchimedeanMatrix F n))
  let : ProperSpace A := FiniteDimensional.proper ℝ (ArchimedeanMatrix F n)
  let mA : MeasurableSpace A := borel A
  let bA : BorelSpace A := ⟨rfl⟩
  let basis : Module.Basis (Fin (Module.finrank ℝ A)) ℝ A := lieBasis F n
  let μ : Measure A := basis.addHaar
  let hμ : IsAddHaarMeasure μ := isAddHaarMeasure_basis_addHaar basis
  let e := matrixSplit F n
  let a₀ := (e g).1
  let b := (e g).2
  obtain ⟨ρ, K, hρ, hKc, hKJ, htu, hP⟩ := exists_closedBall_productPatch F n g hg J hJ
  let t : Set A := closedBall (a₀ : A) ρ
  have ht : IsCompact t := isCompact_closedBall _ _
  have hinj : (matrixProductPatch F n t b K.toSubgroup).InjOn (point F n) := hP.1
  have hband : MapsTo (point F n) (matrixProductPatch F n t b K.toSubgroup) (band F n) := hP.2
  obtain ⟨Cl, hCl⟩ := exists_lintegral_coordinateSlice_le F n S μ hL2 t ht htu b K hKc hinj hband
  have htU : t ⊆ range (Units.val : ArchimedeanGL F n → A) := htu
  let N := Module.finrank ℝ A + 1
  have hjet := @exists_coordinateSlice_jet_bound F fieldF numberFieldF n S t ht htU N
  rcases hjet with ⟨D, Cj, hCj, hjets⟩
  have hTaylor := @Langlands.Analysis.exists_enorm_le_mul_of_lintegral_derivatives_le
    A aNorm aSpace aDim mA bA μ hμ (a₀ : A) ρ hρ
  obtain ⟨Cs, hCs⟩ := hTaylor
  let U := matrixProductPatch F n (ball (a₀ : A) (ρ / 2)) b K.toSubgroup
  have hU : IsOpen U :=
    ((isOpen_ball.preimage Units.continuous_val).prod (isOpenMap_mul_left b _ K.isOpen)).preimage
      e.continuous
  have hgU : g ∈ U := ⟨mem_ball_self (half_pos hρ), ⟨1, K.one_mem, mul_one b⟩⟩
  let C : ℝ := (Cs : ℝ) * Cj * (Cl : ℝ)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg Cs.coe_nonneg hCj) Cl.coe_nonneg
  refine ⟨U, hU, hgU, D, C, hC, fun v hv y hy => ?_⟩
  let f := coordinateSlice F n S b v
  let fD (d : EnvelopingAlgebra F n) := coordinateSlice F n S b (S.envelopingAction d v)
  let L (d : EnvelopingAlgebra F n) := toL2 F n S (quotientHaarMeasure F n) hL2 (S.envelopingAction d v)
  let B : ℝ≥0∞ := ENNReal.ofReal Cj * ((Cl : ℝ≥0∞) * ∑ d ∈ D, ‖L d‖ₑ)
  have hvK (k : FiniteAdelicGL F n) (hk : k ∈ K.toSubgroup) :
      S.finiteRepresentation k v = v := hv ⟨k, @hKJ k hk⟩
  have hfixed (d : EnvelopingAlgebra F n) :
      ∀ k : K, S.finiteRepresentation (k : FiniteAdelicGL F n) (S.envelopingAction d v) =
        S.envelopingAction d v := by
    intro k
    exact (S.finiteRepresentation_envelopingAction (k : FiniteAdelicGL F n) d v).trans
      (congrArg (fun w : S.Space => S.envelopingAction d w) (hvK k k.property))
  have hfD (d : EnvelopingAlgebra F n) : AEMeasurable (fun x => ‖fD d x‖ₑ) (μ.restrict t) := by
    have hcont : ContinuousOn (fD d) t :=
      (contDiffOn_coordinateSlice F n S b (S.envelopingAction d v)).continuousOn.mono htU
    exact (hcont.aestronglyMeasurable ht.measurableSet).aemeasurable.enorm
  have hB (j : ℕ) (hj : j ≤ Module.finrank ℝ A + 1) :
      ∫⁻ x in t, ‖iteratedFDeriv ℝ j f x‖ₑ ∂μ ≤ B := by
    calc
      _ ≤ ENNReal.ofReal Cj * ∑ d ∈ D, ∫⁻ x in t, ‖fD d x‖ₑ ∂μ :=
        Langlands.Analysis.lintegral_enorm_le_mul_sum μ ht.measurableSet D hCj _ fD
          (fun d _ => hfD d) (fun x hx => hjets b v x hx j hj)
      _ ≤ B := by
        apply mul_le_mul' le_rfl
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun d _ => hCl (S.envelopingAction d v) (hfixed d)
  let yA : A := (e y).1
  have hyA : yA ∈ ball (a₀ : A) (ρ / 2) := hy.1
  have hyB : (e y).2 ∈ finiteCoset F n b K.toSubgroup := hy.2
  obtain ⟨k, hk, hky⟩ := hyB
  change b * k = (e y).2 at hky
  have heval : evaluate F n (S.toContinuous v) y = f yA := by
    have h := evaluate_matrixSplit_symm_mul_right F n S (e y).1 b k v (hvK k hk)
    change evaluate F n (S.toContinuous v) (e.symm ((e y).1, b * k)) = f yA at h
    rwa [hky, Prod.mk.eta, e.symm_apply_apply] at h
  have hfs : ContDiffOn ℝ ∞ f t := (contDiffOn_coordinateSlice F n S b v).mono htU
  have hpoint : ‖f yA‖ₑ ≤ (Cs : ℝ≥0∞) * B := hCs f B hfs hB yA hyA
  suffices h : ‖f yA‖ ≤ C * ∑ d ∈ D, ‖L d‖ from
    (congrArg (fun z : ℂ => ‖z‖) heval).le.trans h
  have hprod : ENNReal.ofReal C = (Cs : ℝ≥0∞) * ENNReal.ofReal Cj * (Cl : ℝ≥0∞) := by
    rw [show C = (Cs : ℝ) * Cj * (Cl : ℝ) from rfl,
      ENNReal.ofReal_mul (mul_nonneg Cs.coe_nonneg hCj),
      ENNReal.ofReal_mul Cs.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  have hsum : 0 ≤ ∑ d ∈ D, ‖L d‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC hsum)).mp
  rw [ofReal_norm, ENNReal.ofReal_mul hC, hprod,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
  simpa only [ofReal_norm, mul_assoc] using hpoint

end Langlands.Automorphic.OperatorDeterminantSlice
