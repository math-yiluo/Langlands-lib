import Langlands.Automorphic.GroupSchemeCuspidalConvolutionEigenfunctions
import Langlands.Global.AdelicUniformDirectionalGrowth
import Langlands.Global.AdelicSymmetricCompactInvariantKernel
import Langlands.Global.AdelicHaarUnimodularityProof
import Langlands.Group.GL.LeviCentralQuotientMeasure
import Langlands.Representation.Unitary.IntegratedKernelLocalApproximation
import Langlands.Representation.Unitary.IntegratedUnitarySymmetryProof

/-! # Classical density in the full cuspidal Hilbert space -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NumberField MeasureTheory Set Filter
open scoped CategoryTheory.MonObj Classical Topology InnerProductSpace NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global AdelicGroupPoints PositiveRealTorus RepresentationGrowth InfiniteAdelicGroupPoints
  Langlands.GroupScheme Langlands.Analysis Module.End

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (rho : MatrixRepresentation G (Fin N)) (K : Subgroup (InfiniteAdelicGroupPoints F G))

local notation "A" => AdelicGroupPoints F G
local notation "Γ" => positiveRationalSubgroup F G T i
local notation "Q" => PositiveRationalQuotient F G T i
local notation "q" => LeftCosetSpace.mk Γ
local notation "dq" => positiveRationalQuotientHaarMeasure F G T i
local notation "dg" => (Measure.haar : Measure A)
local notation "V" => Lp ℂ 2 dq
local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
local notation "act" => fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc dg
local notation "π" => fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
local notation "hNorm" => norm_fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
local notation "hMeas" => fullAEL2CuspidalOrbit_aestronglyMeasurable F G hPD hG T i hi I e hc dg
local notation "W" => FinitePlotSmoothRationalFunctions F G
local notation "ev" => finitePlotSmoothEvaluation F G
local notation "hcalc" => adelicDifferentialCommutator_of_smooth F G hsmooth
local notation "H" => adelicHeight F G rho

private local instance : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ

/-- Classical cusp representatives with one common derivative exponent are dense
in the full cuspidal Hilbert space under center conjugation invariance. -/
def GroupSchemeClassicalCuspidalHilbertDensityStatement : Prop :=
  AdelicEnvelopingCenterConjugationStatement.{u} → 0 < N → IsClosedSubgroup rho →
  IsCompact (K : Set (InfiniteAdelicGroupPoints F G)) →
  ∀ (v : S) (ε : ℝ), 0 < ε → ∃ w : S, ∃ φ : C(Q, ℂ),
    ‖v - w‖ < ε ∧ (w.val : Q → ℂ) =ᵐ[dq] φ ∧
    IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) K rho (φ ∘ q) ∧
    HasZeroProperParabolicConstantTerms (φ ∘ q) ∧ HasUniformDirectionalHeightGrowth hsmooth rho (φ ∘ q)

theorem groupSchemeClassicalCuspidalHilbertDensity :
    GroupSchemeClassicalCuspidalHilbertDensityStatement T i hi I e hc hPD hG hsmooth rho K := by
  intro hAd hN hrho hK
  let D (s : List (smoothModel F d)) : W →ₗ[ℂ] (A → ℂ) :=
    (ev).comp (adelicEnvelopingAction F G hsmooth hcalc (adelicDirectionalWordEnveloping hsmooth s))
  have hD (s : List (smoothModel F d)) (f : W) :
      D s f = adelicIteratedDirectionalValue hsmooth s (ev f) :=
    evaluate_adelicDirectionalWordEnveloping hsmooth hcalc s f
  let C : Submodule ℂ S :=
    { carrier := {v | ∃ φ : C(Q, ℂ), ∃ f : W, ev f = φ ∘ q ∧ (v.val : Q → ℂ) =ᵐ[dq] φ ∧
        f ∈ adelicInfiniteFiniteSubmodule F G K ∧ f ∈ adelicCenterFiniteSubmodule F G hsmooth hcalc ∧
        HasUniformDirectionalHeightGrowth hsmooth rho (ev f)}
      zero_mem' := by
        refine ⟨0, 0, rfl, Lp.coeFn_zero ℂ 2 dq, Submodule.zero_mem _, Submodule.zero_mem _,
          0, le_rfl, fun s => ⟨0, le_rfl, fun x => ?_⟩⟩
        rw [← hD s, map_zero]
        simp
      add_mem' := by
        rintro v w ⟨φ, f, hφ, hv, hKf, hZf, r, hr, hf⟩ ⟨ψ, g, hψ, hw, hKg, hZg, t, ht, hg⟩
        refine ⟨φ + ψ, f + g, ?_, ?_, Submodule.add_mem _ hKf hKg, Submodule.add_mem _ hZf hZg,
          max r t, hr.trans (le_max_left _ _), fun s => ?_⟩
        · rw [map_add, hφ, hψ]; rfl
        · exact (Lp.coeFn_add v.val w.val).trans (hv.add hw)
        · obtain ⟨C₁, hC₁, h₁⟩ := hf s
          obtain ⟨C₂, hC₂, h₂⟩ := hg s
          refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun x => ?_⟩
          have hx : 1 ≤ H x := one_le_adelicHeight F G rho hN x
          rw [← hD s, map_add, Pi.add_apply]
          calc
            _ ≤ ‖D s f x‖ + ‖D s g x‖ := norm_add_le _ _
            _ ≤ C₁ * H x ^ r + C₂ * H x ^ t := add_le_add (by rw [hD]; exact h₁ x)
              (by rw [hD]; exact h₂ x)
            _ ≤ C₁ * H x ^ max r t + C₂ * H x ^ max r t := add_le_add
              (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)) hC₁)
              (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (le_max_right _ _)) hC₂)
            _ = _ := (add_mul _ _ _).symm
      smul_mem' := by
        rintro a v ⟨φ, f, hφ, hv, hKf, hZf, r, hr, hf⟩
        refine ⟨a • φ, a • f, ?_, ?_, Submodule.smul_mem _ _ hKf, Submodule.smul_mem _ _ hZf,
          r, hr, fun s => ?_⟩
        · rw [map_smul, hφ]; rfl
        · exact (Lp.coeFn_smul a v.val).trans (hv.const_smul a)
        · obtain ⟨C₁, hC₁, h₁⟩ := hf s
          refine ⟨‖a‖ * C₁, mul_nonneg (norm_nonneg _) hC₁, fun x => ?_⟩
          rw [← hD s, map_smul, Pi.smul_apply, norm_smul, hD, mul_assoc]
          exact mul_le_mul_of_nonneg_left (h₁ x) (norm_nonneg _) }
  have hIn (w : S) (φ : C(Q, ℂ)) (hw : (w.val : Q → ℂ) =ᵐ[dq] φ)
      (hf : IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) K rho (φ ∘ q))
      (hGrow : HasUniformDirectionalHeightGrowth hsmooth rho (φ ∘ q)) : w ∈ C := by
    obtain ⟨f, he, hA⟩ := (rationalAutomorphicFunctionComparison F G K rho hsmooth hcalc (φ ∘ q)).mp hf
    change ev f = φ ∘ q at he
    exact ⟨φ, f, he, hw, hA.1, hA.2.1, by rw [he]; exact hGrow⟩
  have hOrth : Cᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro v hv
    change v = 0
    by_contra hne
    have hvPos : 0 < ‖v‖ := norm_pos_iff.mpr hne
    let U : Set A := {a | ‖π a v - v‖ < ‖v‖ / 2}
    have hOrb : Continuous (fun a : A => π a v) :=
      (fullAEL2CuspidalOrbitMap F G hPD hG T i hi I e hc v).continuous
    have hU : U ∈ 𝓝 (1 : A) := Metric.continuousAt_iff'.mp hOrb.continuousAt _ (half_pos hvPos) |>.mono
      (fun a ha => by simpa only [map_one, one_apply_eq_self, dist_eq_norm] using ha)
    obtain ⟨h, hh, hSupp, hNonneg, hMass, hInv, hCentral⟩ :=
      adelicSymmetricCompactInvariantKernel (F := F) (G := G) hsmooth K hK U hU
    let k (a : A) := (h a : ℂ)
    have hhC : Continuous h := by
      have he := Complex.continuous_re.comp hh.1.1
      change Continuous (fun x => (k x).re) at he
      simpa only [k, Complex.ofReal_re] using he
    have hhS : HasCompactSupport h := by
      have ht : HasCompactSupport (fun x : A => (k x).re) := hh.2.1.comp_left Complex.zero_re
      simpa only [k, Complex.ofReal_re] using ht
    have hhI : Integrable h dg := hhC.integrable_of_hasCompactSupport hhS
    let B := act k hhI.ofReal
    let := adelicHaarUnimodularity.{u}.2 F G hG
    let := Langlands.isInvInvariant_of_isMulRightInvariant dg
    have hπinner : ∀ (a : A) (v w : S), inner ℂ (π a v) (π a w) = inner ℂ v w :=
      fun a => (LinearMap.norm_map_iff_inner_map_map (π a).toLinearMap).mp (hNorm a)
    have hSym : B.IsSymmetric := by
      refine integratedUnitarySymmetry dg π hπinner hMeas (fun _ => (1 : ℝ≥0)) measurable_const ?_ k hhI.ofReal ?_
      · simp [Measure.inv_eq_self]
      · exact Eventually.of_forall fun a => by simp [k, hInv]
    have hComm (b : K) (w : S) : π (ofInfinite F G b) (B w) = B (π (ofInfinite F G b) w) :=
      integratedIsometricAction_commute_conjugation dg π hNorm hMeas k hhI.ofReal (ofInfinite F G b)
        (fun a => congrArg (fun r : ℝ => (r : ℂ)) (hCentral b.val b.property a)) w
    have hB : IsCompactOperator B :=
      (groupSchemeCuspidalConvolutionCompact T i hi I e hc hG rho hPD hN hrho k hhI.ofReal hh).2
    have hEval (c : ℂ) (hc₀ : c ≠ 0) (w : S) (hw : B w = c • w) : w ∈ C := by
      obtain ⟨φ, hφ, hAuto, _, hGφ⟩ :=
        groupSchemeCuspidalConvolutionEigenfunctions T i hi I e hc hPD hG hsmooth rho K
          hAd hN hrho k hh hhI.ofReal hB hComm c hc₀ w hw
      exact hIn w φ hφ hAuto hGφ
    have hBvOrth : B v ∈ (⨆ c : ℂ, eigenspace B.toLinearMap c)ᗮ := by
      rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro c
      apply (Submodule.mem_orthogonal _ _).mpr
      intro w hw
      have he : B w = c • w := mem_eigenspace_iff.mp hw
      have hInner : inner ℂ (B w) v = inner ℂ w (B v) := hSym w v
      rw [← hInner, he]
      by_cases hc₀ : c = 0
      · simp [hc₀]
      · exact Submodule.inner_right_of_mem_orthogonal (C.smul_mem c (hEval c hc₀ w he)) hv
    have hBv : B v = 0 := by
      rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hB hSym] at hBvOrth
      exact hBvOrth
    have hClose : ‖B v - v‖ ≤ ‖v‖ / 2 :=
      integratedIsometricAction_sub_le_of_nonnegative dg π hNorm hMeas h hhI hNonneg hMass v _
        (fun a ha => (show ‖π a v - v‖ < ‖v‖ / 2 from hSupp (subset_tsupport h ha)).le)
    rw [hBv, zero_sub, norm_neg] at hClose
    linarith
  have hDense : C.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hOrth, Submodule.bot_orthogonal_eq_top]
  intro v ε hε
  have hv : v ∈ closure (C : Set S) := by
    change v ∈ C.topologicalClosure
    rw [hDense]
    trivial
  obtain ⟨w, hw, hDist⟩ := Metric.mem_closure_iff.mp hv ε hε
  obtain ⟨φ, f, he, hφ, hKf, hZf, hg⟩ := hw
  have hMod : HasAdelicModerateGrowth F G rho f.val := by
    obtain ⟨r, hr, hGrowth⟩ := hg
    obtain ⟨C₁, hC₁, h₁⟩ := hGrowth []
    exact (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).mpr
      ⟨C₁, r, hC₁, hr, h₁⟩
  refine ⟨w, φ, by simpa only [dist_eq_norm] using hDist, hφ, ?_, ?_, he ▸ hg⟩
  · rw [← he]
    exact (isAutomorphicFunctionOn_evaluate_iff F G hsmooth hcalc rho K f).mpr ⟨hKf, hZf, hMod⟩
  · exact hasZeroProperParabolicConstantTerms_of_normalized hPD hG _
      ((groupSchemeFullAEL2ContinuousCuspidality F G hPD hG T i hi I e hc φ w.val hφ).mp w.property)

end Langlands.Automorphic.GroupSchemeFunctions
