import Langlands.Global.RankinSelberg.RealGodementSpectralDescent
import Langlands.Global.RankinSelberg.RealGodementSpectralFrame
import Langlands.Global.RankinSelberg.RealGodementSpectralGrowth
import Langlands.Representation.Archimedean.RealInductionStagesFamily

/-! # The real Jacquet continuation rank step with uniform derivative growth -/

noncomputable section

open Langlands.Analysis
open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Filter Matrix MeasureTheory Metric Set
open scoped Classical ContDiff Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PartialJacquet PrincipalSeriesExtension RealGodementProfiles RealJacquetFrobenius

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "K" => unitaryCompact ℝ (t + 2)
local notation "P" => (Fin (t + 1) → ℂ)
local notation "P'" => (Fin (t + 2) → ℂ)
local notation "L'" => (Fin (t + 2) → Fin 2)

/-- The strict chamber of the real position exponents. -/
def realSpectralChamber (r : ℕ) : Set (Fin (r + 1) → ℂ) :=
  {z | ∀ i : Fin r, (z i.succ).re < (z i.castSucc).re}

theorem isOpen_realSpectralChamber (r : ℕ) : IsOpen (realSpectralChamber r) := by
  have h : realSpectralChamber r =
      ⋂ i : Fin r, {z : Fin (r + 1) → ℂ | (z i.succ).re < (z i.castSucc).re} := by
    ext z
    simp only [realSpectralChamber, mem_ofPred_eq, mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_lt
    (Complex.continuous_re.comp (continuous_apply i.succ))
    (Complex.continuous_re.comp (continuous_apply i.castSucc))

theorem realSpectralChamber_nonempty (r : ℕ) : (realSpectralChamber r).Nonempty := by
  refine ⟨fun i => -((i : ℕ) : ℂ), ?_⟩
  intro i
  change (-((i.succ : ℕ) : ℂ)).re < (-((i.castSucc : ℕ) : ℂ)).re
  simp only [Complex.neg_re, Complex.natCast_re, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one,
    Complex.add_re, Complex.one_re]
  linarith

theorem isStrictlyDominant_characterList {r : ℕ} (p : Fin (r + 1) → Fin 2)
    {z : Fin (r + 1) → ℂ} (hz : z ∈ realSpectralChamber r) :
    IsStrictlyDominant (realPositionExponent (characterList p z)) r := by
  intro j hj
  let i : Fin r := ⟨j, hj⟩
  change (realPositionExponent (characterList p z) i.succ).re <
    (realPositionExponent (characterList p z) i.castSucc).re
  simpa only [realPositionExponent_characterList] using hz i

private def tailParameter (z : P') : P := fun i => z i.succ

private theorem differentiable_tailParameter : Differentiable ℂ (tailParameter (t := t)) :=
  differentiable_pi.mpr fun i => (ContinuousLinearMap.proj i.succ : P' →L[ℂ] ℂ).differentiable

private theorem tailParameter_mem_chamber {z : P'} (hz : z ∈ realSpectralChamber (t + 1)) :
    tailParameter z ∈ realSpectralChamber t := by
  intro i
  change (z i.succ.succ).re < (z i.castSucc.succ).re
  have he : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
  simpa only [he] using hz i.succ

private theorem uniformGrowth_tailParameter (W : P → G → ℂ)
    (hW : HasLocallyUniformDerivativeGrowth univ W) :
    HasLocallyUniformDerivativeGrowth univ (fun z : P' => W (tailParameter z)) := by
  intro z _
  obtain ⟨δ, hδ, N, hN⟩ := hW (tailParameter z) (mem_univ _)
  have hNear : ∀ᶠ q in 𝓝 z, tailParameter q ∈ ball (tailParameter z) δ :=
    differentiable_tailParameter.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hδ)
  obtain ⟨ε, hε, hBall⟩ := Metric.eventually_nhds_iff_ball.mp hNear
  refine ⟨ε, hε, N, fun Xs => ?_⟩
  obtain ⟨C, hC, h⟩ := hN Xs
  exact ⟨C, hC, fun q hq => h (tailParameter q) (hBall q hq)⟩

/-- Fixed real compact profiles have a Jacquet family agreeing with the integral on
the strict chamber, with holomorphy and locally uniform growth for all right derivatives. -/
def HasLocallyUniformRealJacquetFamily (r : ℕ) (a : ℝˣ) : Prop :=
  ∀ (p : Fin (r + 1) → Fin 2) (φ : Matrix.unitaryGroup (Fin (r + 1)) ℝ → ℂ),
    IsCompactProfile p φ →
    ∃ W : (Fin (r + 1) → ℂ) → Langlands.GeneralLinear (r + 1) ℝ → ℂ,
      (∀ z Xs, RealLocalWhittaker.iteratedRightDerivative r Xs (W z) ∈
        RealLocalWhittaker.regularFunctions r (-a)) ∧
      HasLocallyUniformDerivativeGrowth univ W ∧
      (∀ Xs g, Differentiable ℂ (fun z => RealLocalWhittaker.iteratedRightDerivative r Xs (W z) g)) ∧
      ∀ z ∈ realSpectralChamber r, ∀ g, W z g = additiveJacquetIntegral a (standardSection z φ) g

/-- Left Whittaker covariance and locally uniform derivative growth give regular
Whittaker functions for every derivative of each smooth group slice. -/
theorem regular_iteratedRightDerivative_of_spectralGrowth {r n : ℕ} {a : ℝˣ}
    (W : (Fin n → ℂ) → Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (hSmooth : ∀ z, ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ (W z))
    (hGrowth : HasLocallyUniformDerivativeGrowth univ W)
    (hLaw : ∀ z u, u ∈ GeneralLinear.upperUnipotent (r + 1) ℝ → ∀ g,
      W z (u * g) = realWhittakerCharacter a u * W z g) :
    ∀ z Xs, RealLocalWhittaker.iteratedRightDerivative r Xs (W z) ∈
      RealLocalWhittaker.regularFunctions r a := by
  intro z Xs
  obtain ⟨δ, hδ, N, hN⟩ := hGrowth z (mem_univ z)
  obtain ⟨C, hC, h⟩ := hN Xs
  refine ⟨?_, RealUniformWhittaker.contMDiff_iteratedRightDerivative (hSmooth z) Xs,
    C, N, hC, h z (mem_ball_self hδ)⟩
  intro u hu
  clear h
  induction Xs with
  | nil => exact hLaw z u hu
  | cons Y Xs ih =>
    intro g
    exact rightDerivative_mul_left_of_eq
      (RealUniformWhittaker.contMDiff_iteratedRightDerivative (hSmooth z) Xs) ih Y g

private theorem det_ne_zero_of_spanning {k : ℕ} {J : Type*} (v : J → Fin k → ℂ)
    (hv : Submodule.span ℂ (range v) = ⊤) :
    ∃ b : Fin k → J, (Matrix.of fun i j => v (b i) j : Matrix (Fin k) (Fin k) ℂ).det ≠ 0 := by
  have hdim : Module.finrank ℂ (Submodule.span ℂ (range v)) = k := by
    rw [hv, finrank_top, Module.finrank_fin_fun]
  have h := Submodule.exists_fun_fin_finrank_span_eq ℂ (range v)
  rw [hdim] at h
  obtain ⟨f, hf, _, hfi⟩ := h
  choose b hb using hf
  refine ⟨b, (?_ : IsUnit (Matrix.det (fun i j => v (b i) j))).ne_zero⟩
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  have he : Matrix.row (fun i j => v (b i) j) = f := funext hb
  rwa [he]

private def spectralFrameLift (p : L') (W : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ f ∈ W, ∀ q : K, (fun k : K => f (q * k)) ∈ W) (z : P') :
    spectralFrameSpace p W →ₗ[ℂ] principalSeries ℝ (t + 2) (realPositionCharacter (characterList p z)) := by
  let R : spectralFrameSpace p W →ₗ[ℂ] (H → ℂ) := {
    toFun := fun f => standardSection z (frameProfile f.val)
    map_add' := fun x y => (extensionLinear _).map_add (frameProfile x.val) (frameProfile y.val)
    map_smul' := fun c x => (extensionLinear _).map_smul c (frameProfile x.val) }
  exact R.codRestrict _ fun f => (standardSection_mem (isCompactProfile_frameProfile hW f.property) z).1.1

private theorem basis_dotProduct {E : Type*} [AddCommGroup E] [Module ℂ E] {k : ℕ}
    (b : Module.Basis (Fin k) ℂ E) (L : E →ₗ[ℂ] ℂ) (v : E) :
    b.equivFun v ⬝ᵥ (fun i => L (b i)) = L v := by
  unfold dotProduct
  conv_rhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.equivFun_apply]

/-- The all-parameter real Jacquet continuation with simultaneous derivative estimates
passes through one Godement induction step. -/
def RealGodementSpectralStepStatement (t : ℕ) : Prop :=
  ∀ (_D : RealQuotientMeasureData t) (a : ℝˣ),
    HasLocallyUniformRealJacquetFamily t a → HasLocallyUniformRealJacquetFamily (t + 1) a

theorem realGodementSpectralStep : RealGodementSpectralStepStatement t := by
  intro D a hLower p φ hφ
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  let f := standardSection (0 : P') φ
  have hf := standardSection_mem hφ (0 : P')
  obtain ⟨W, hWFin, hfW, hW⟩ := exists_finite_leftStable_of_kFinite hf.2
  let A := spectralFrameSpace p W
  let : FiniteDimensional ℂ A := Submodule.finiteDimensional_of_le inf_le_left
  let x : A := ⟨compactSectionRestriction f, mem_spectralFrameSpace_of_principalSeries hW hf.1.1 hfW⟩
  have hx : frameProfile x.val = φ := compactRestriction_standardSection φ 0
  let k := Module.finrank ℂ A
  let β := Module.finBasis ℂ A
  let J := SpectralSectionFamily μ p W
  let v (j : J) (z : P') : A := ⟨j.column z, j.column_mem hW z⟩
  let c (j : J) (z : P') : Fin k → ℂ := β.equivFun (v j z)
  have hc (j : J) (i : Fin k) : Differentiable ℂ (fun z => c j z i) := by
    obtain ⟨n, g, w, he⟩ := InductionStages.exists_eval_sum A (β.coord i)
    have hEq : (fun z => c j z i) = fun z => ∑ l : Fin n, w l * j.upperSection z (g l).val :=
      funext fun z => he (v j z)
    rw [hEq]
    exact Differentiable.fun_sum fun l _ => (j.differentiable_section (g l).val).const_mul _
  have hSpan (z : P') : Submodule.span ℂ (range fun j => c j z) = ⊤ := by
    let B := Submodule.span ℂ (range fun j => v j z)
    have hMap : B.map A.subtype = A := by
      change (Submodule.span ℂ (range fun j => v j z)).map A.subtype = A
      rw [Submodule.map_span, ← Set.range_comp]
      exact realGodementSpectralFrame μ p W hW z
    have hB : B = ⊤ := by
      apply Submodule.map_injective_of_injective A.injective_subtype
      rw [hMap, Submodule.map_top, Submodule.range_subtype]
    have he := congrArg (fun T : Submodule ℂ A => T.map β.equivFun.toLinearMap) hB
    change (Submodule.span ℂ (range fun j => v j z)).map β.equivFun.toLinearMap =
      (⊤ : Submodule ℂ A).map β.equivFun.toLinearMap at he
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearMap.range_eq_top.mpr β.equivFun.surjective] at he
    exact he
  choose lower hLower' using fun j : J => hLower (fun i => p i.succ) j.lower j.lower_profile
  let F (j : J) (z : P') (g : H) :=
    godementLeadingFamily D a j.test (lower j (tailParameter z)) (p 0) g (z 0)
  have hF (j : J) := realGodementSpectralGrowth D a (p 0) univ isOpen_univ
    (fun z => lower j (tailParameter z)) (fun z : P' => z 0)
    (fun z _ Xs => (hLower' j).1 (tailParameter z) Xs)
    (fun g => (((hLower' j).2.2.1 [] g).comp differentiable_tailParameter).differentiableOn)
    (ContinuousLinearMap.proj 0 : P' →L[ℂ] ℂ).differentiable.differentiableOn
    (uniformGrowth_tailParameter (lower j) (hLower' j).2.1)
    j.support j.support_compact j.support_fullRank ⟨j.test, j.test_zero⟩
  have hDomColumn (j : J) (z : P') (hz : z ∈ realSpectralChamber (t + 1)) (g : H) :
      F j z g = additiveJacquetIntegral a (j.upperSection z) g := by
    let ds := characterList (fun i : Fin (t + 1) => p i.succ) (tailParameter z)
    have hTail := tailParameter_mem_chamber hz
    have hDom : IsStrictlyDominant (realPositionExponent ds) t := isStrictlyDominant_characterList _ hTail
    have hLead : (realPositionExponent ds 0).re < (z 0).re := by
      rw [show realPositionExponent ds 0 = tailParameter z 0 from realPositionExponent_characterList _ _ 0]
      exact hz (0 : Fin (t + 1))
    have hLowerEq : lower j (tailParameter z) = additiveJacquetIntegral a (j.lowerSection z) :=
      funext fun h => (hLower' j).2.2.2 _ hTail h
    let L : principalSeries ℝ (t + 1) (realPositionCharacter ds) :=
      ⟨j.lowerSection z, (standardSection_mem j.lower_profile (tailParameter z)).1.1⟩
    change godementLeadingFamily D a j.test (lower j (tailParameter z)) (p 0) g (z 0) = _
    rw [hLowerEq]
    exact (realGodementSmoothLeading t D a (p 0) ds L hDom j.support j.support_compact
      j.support_fullRank j.test j.test_zero g).2 (z 0) hLead
  let E (z : P') (hz : z ∈ realSpectralChamber (t + 1)) : A →ₗ[ℂ] (H → ℂ) :=
    (additiveJacquetLinear a (RealStrictCharacterLanglandsQuotient.isSignedPower _)
      (isStrictlyDominant_characterList p hz)).comp (spectralFrameLift p W hW z)
  let c₀ (z : P') (g : H) (i : Fin k) :=
    if hz : z ∈ realSpectralChamber (t + 1) then E z hz (β i) g else 0
  have hSeed (z : P') (hz : z ∈ realSpectralChamber (t + 1)) (j : J) (g : H) :
      c j z ⬝ᵥ c₀ z g = F j z g := by
    have he : c₀ z g = fun i => E z hz (β i) g := funext fun i => dite_eq_left hz
    rw [he]
    change β.equivFun (v j z) ⬝ᵥ (fun i => ((LinearMap.proj g).comp (E z hz)) (β i)) = _
    rw [basis_dotProduct, hDomColumn j z hz]
    change additiveJacquetIntegral a (standardSection z (frameProfile (j.column z))) g = _
    rw [← j.section_eq_standardSection hW]
  obtain ⟨B, _, hBSeed, hB⟩ := realGodementSpectralDescent c F hc
    (fun z => det_ne_zero_of_spanning _ (hSpan z))
    (fun j z => (hF j).2.1 z (mem_univ z))
    (fun j Xs g => differentiableOn_univ.mp ((hF j).2.2 Xs g))
    (fun j => (hF j).1) (realSpectralChamber (t + 1))
    (isOpen_realSpectralChamber _) (realSpectralChamber_nonempty _) c₀ hSeed
  let W₁ (z : P') := B z (β.equivFun x)
  obtain ⟨hSmooth, hGrowth, hDer⟩ := hB (β.equivFun x)
  have hCompare (z : P') (hz : z ∈ realSpectralChamber (t + 1)) (g : H) :
      W₁ z g = additiveJacquetIntegral a (standardSection z φ) g := by
    have he : c₀ z g = fun i => E z hz (β i) g := funext fun i => dite_eq_left hz
    change B z (β.equivFun x) g = _
    rw [hBSeed z hz, he]
    change β.equivFun x ⬝ᵥ (fun i => ((LinearMap.proj g).comp (E z hz)) (β i)) = _
    rw [basis_dotProduct]
    change additiveJacquetIntegral a (standardSection z (frameProfile x.val)) g = _
    rw [hx]
  have hLaw (z : P') (u : H) (hu : u ∈ GeneralLinear.upperUnipotent (t + 2) ℝ) (g : H) :
      W₁ z (u * g) = realWhittakerCharacter (-a) u * W₁ z g := by
    apply congrFun (eq_of_differentiable_eqOn_open (hDer [] (u * g)) ((hDer [] g).const_mul _)
      (isOpen_realSpectralChamber _) (realSpectralChamber_nonempty _) ?_) z
    intro q hq
    change W₁ q (u * g) = realWhittakerCharacter (-a) u * W₁ q g
    rw [hCompare q hq, hCompare q hq]
    exact realGodementOpenCellCovariance (t + 1) a (standardSection q φ) ⟨u, hu⟩ g
  exact ⟨W₁, regular_iteratedRightDerivative_of_spectralGrowth W₁ hSmooth hGrowth hLaw,
    hGrowth, hDer, hCompare⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
