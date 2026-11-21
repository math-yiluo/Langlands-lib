import Langlands.Global.RankinSelberg.RealGodementCompactOrbit
import Langlands.Global.RankinSelberg.RealGodementSpanEquivariance
import Langlands.Representation.Archimedean.RealSmoothRightAction

/-! # Smoothness and the Lie action on continued real Godement sections -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzCompactFamilies
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Filter MeasureTheory Set
open scoped ContDiff Matrix.Norms.Operator Manifold NNReal SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PartialJacquet RealJacquetFrobenius

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ
local notation "Y" => Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ
local notation "I" => matrixModel ℝ (t + 2)
local notation "R" => rightDerivative I

private theorem exists_sectionTestLinear (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (c : RealCharacterData) (f : G → ℂ) (hf : Continuous f) (g : H)
    {S : Set X} (hS : IsCompact S) (hRank : ∀ x ∈ S, HasFullRowRank x) :
    ∃ (L : supportedSchwartz S →ₗ[ℂ] ℂ) (q : Seminorm ℝ 𝓢(X, ℂ)), Continuous q ∧
      ∀ Φ : supportedSchwartz S, L Φ = sectionValue μ c f Φ.val g ∧ ‖L Φ‖ ≤ q Φ.val := by
  let V := {h : G | ∃ z ∈ ({g} : Set H), rowPoint h.val z ∈ S}
  have hV : IsCompact V := isCompact_support_preimage isCompact_singleton hS hRank
  let δ := determinantWeight c (((t + 1 : ℕ) : ℂ) / 2) g
  let k (h : G) := δ * (f h⁻¹ * determinantWeight c ((((t + 1 : ℕ) : ℂ) + 1) / 2) h)
  have hK : Continuous k := continuous_const.mul
    ((hf.comp continuous_inv).mul (contMDiff_determinantWeight c _).continuous)
  let F (Φ : supportedSchwartz S) (h : G) := k h * Φ.val (rowPoint h.val g)
  have hRow : Continuous (fun h : G => rowPoint h.val g) :=
    Units.continuous_val.matrix_mul continuous_const
  have hInt (Φ : supportedSchwartz S) : Integrable (F Φ) (μ.restrict V) :=
    (hK.mul (Φ.val.continuous.comp hRow)).continuousOn.integrableOn_compact hV
  let L : supportedSchwartz S →ₗ[ℂ] ℂ := {
    toFun := fun Φ => ∫ h in V, F Φ h ∂μ
    map_add' := fun Φ Ψ => by
      change (∫ h in V, F (Φ + Ψ) h ∂μ) = _
      have hAdd : F (Φ + Ψ) = fun h => F Φ h + F Ψ h := by
        funext h
        change k h * (Φ.val (rowPoint h.val g) + Ψ.val (rowPoint h.val g)) = _
        exact mul_add _ _ _
      rw [hAdd, integral_add (hInt Φ) (hInt Ψ)]
    map_smul' := fun b Φ => by
      change (∫ h in V, F (b • Φ) h ∂μ) = b • _
      have hSmul : F (b • Φ) = fun h => b • F Φ h := by
        funext h
        change k h * (b * Φ.val (rowPoint h.val g)) = b * (k h * Φ.val (rowPoint h.val g))
        exact mul_left_comm _ _ _
      rw [hSmul, integral_smul] }
  let C : ℝ≥0 := ⟨∫ h in V, ‖k h‖ ∂μ, integral_nonneg fun h => norm_nonneg _⟩
  let p := SchwartzMap.seminorm ℝ (E := X) (F := ℂ) 0 0
  have hp : Continuous p := (schwartz_withSeminorms ℝ X ℂ).continuous_seminorm (0, 0)
  refine ⟨L, C • p, hp.const_mul (C : ℝ), fun Φ => ⟨?_, ?_⟩⟩
  · have hZero : ∀ h ∉ V, F Φ h = 0 := by
      intro h hh
      change k h * Φ.val (rowPoint h.val g) = 0
      rw [Φ.property _ (fun hx => hh ⟨g, mem_singleton g, hx⟩), mul_zero]
    change (∫ h in V, F Φ h ∂μ) = δ * (∫ h,
      f h⁻¹ * determinantWeight c ((((t + 1 : ℕ) : ℂ) + 1) / 2) h *
        Φ.val (rowPoint h.val g) ∂μ)
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hZero, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun h => mul_assoc _ _ _)
  · have hIntK : Integrable (fun h => ‖k h‖) (μ.restrict V) :=
      hK.norm.continuousOn.integrableOn_compact hV
    change ‖∫ h in V, F Φ h ∂μ‖ ≤ (C : ℝ) * p Φ.val
    calc
      _ ≤ ∫ h in V, ‖F Φ h‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ h in V, ‖k h‖ * p Φ.val ∂μ := integral_mono (hInt Φ).norm
        (hIntK.mul_const _) (fun h => by
          rw [show F Φ h = k h * Φ.val (rowPoint h.val g) from rfl, norm_mul]
          exact mul_le_mul_of_nonneg_left (Φ.val.norm_le_seminorm ℝ _) (norm_nonneg _))
      _ = _ := integral_mul_const _ _

/-- A fixed first-column Mellin evaluation is bounded by a continuous Schwartz seminorm. -/
theorem exists_columnMellinLinear_bound (μ : Measure G) [μ.IsHaarMeasure]
    (a : ℝˣ) (W : G → ℂ)
    (hW : ∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W ∈
      RealLocalWhittaker.regularFunctions t (-a))
    (hGrowth : RealUniformWhittaker.HasUniformDerivativeGrowth W) (p : ℕ) (s : ℂ) :
    ∃ q : Seminorm ℝ 𝓢(X, ℂ), Continuous q ∧
      ∀ Φ : 𝓢(X, ℂ), ‖columnMellinLinear μ a W hW hGrowth p s Φ‖ ≤ q Φ := by
  let r := |s.re - (t + 1 : ℕ)|
  obtain ⟨q, B, hq, hB, hB₀, hBounds⟩ :=
    realGodementColumnSeminorm t μ a W hW hGrowth r (abs_nonneg _)
  let C : ℝ≥0 := ⟨∫ h, B h ∂μ, integral_nonneg hB₀⟩
  refine ⟨C • q, hq.const_mul (C : ℝ), fun Φ => ?_⟩
  let K := columnMellinIntegrand a Φ W p s
  have hI : Integrable K μ := (realGodementColumnConvergence t μ a Φ W hW hGrowth p).1 s
  change ‖∫ h, K h ∂μ‖ ≤ (C : ℝ) * q Φ
  calc
    _ ≤ ∫ h, ‖K h‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ h, B h * q Φ ∂μ := integral_mono hI.norm (hB.mul_const _) (fun h => by
      rw [mul_comm]
      exact hBounds Φ p s le_rfl h)
    _ = _ := integral_mul_const _ _

private theorem orbitTest_eq {S : Set X} {U : Set Y} (Φ : 𝓢(X, ℂ)) (Q : Y → supportedSchwartz S)
    (hQ : ∀ A ∈ U, ∀ x, (Q A).val x = Φ (x * A)) (q : H) (hq : q.val ∈ U) :
    (Q q.val).val = rectangularTranslate 1 q Φ := by
  ext x
  rw [hQ _ hq, rectangularTranslate_apply, Units.val_one, Matrix.one_mul]

private theorem contMDiff_compactTestOrbit {S : Set X} (hS : IsCompact S)
    (hRank : ∀ x ∈ S, HasFullRowRank x) (Φ : 𝓢(X, ℂ)) (hΦ : ∀ x ∉ S, Φ x = 0)
    (L : 𝓢(X, ℂ) →ₗ[ℂ] ℂ) (q : Seminorm ℝ 𝓢(X, ℂ)) (hq : Continuous q)
    (hBound : ∀ Φ, ‖L Φ‖ ≤ q Φ) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun g : H => L (rectangularTranslate 1 g Φ)) := by
  let F := fun g : H => L (rectangularTranslate 1 g Φ)
  refine contMDiff_of_contDiffOn (ψ := unitsExtension F) ?_ (fun g => (unitsExtension_val F g).symm)
  intro A hA
  obtain ⟨g, rfl⟩ := hA
  obtain ⟨U, T, hU, hg, hUnit, hT, _, _, Q, hQ⟩ := realGodementCompactOrbit S hS hRank Φ hΦ g
  let L' := L.comp (supportedSchwartz T).subtype
  have hEval := (compactOrbit_evaluation hT L' q hq (fun Ψ => hBound Ψ.val) hU Q Φ hQ).1
  have hNear : unitsExtension F =ᶠ[𝓝 g.val] fun A => L' (Q A) := by
    filter_upwards [hU.mem_nhds hg] with A hA
    obtain ⟨q, rfl⟩ := hUnit A hA
    rw [unitsExtension_val]
    exact congrArg L (orbitTest_eq Φ Q hQ q hA).symm
  exact ((hEval.contDiffAt (hU.mem_nhds hg)).congr_of_eventuallyEq hNear).contDiffWithinAt

/-- Compactly supported tests give smooth upper column values for every regular lower
coefficient with uniform derivative growth. -/
theorem contMDiff_godementLeadingFamily (D : RealQuotientMeasureData t) (a : ℝˣ) (W : G → ℂ)
    (hW : ∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W ∈
      RealLocalWhittaker.regularFunctions t (-a))
    (hGrowth : RealUniformWhittaker.HasUniformDerivativeGrowth W) (p : Fin 2) (w : ℂ)
    {S : Set X} (hS : IsCompact S) (hRank : ∀ x ∈ S, HasFullRowRank x)
    (Φ : 𝓢(X, ℂ)) (hΦ : ∀ x ∉ S, Φ x = 0) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞
      (fun g => godementLeadingFamily D a Φ W p g w) := by
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let L := columnMellinLinear μ a _ hW hGrowth p.val (w + (t : ℂ) / 2)
  obtain ⟨q, hq, hBound⟩ := exists_columnMellinLinear_bound μ a _ hW hGrowth p.val (w + (t : ℂ) / 2)
  have hEval := contMDiff_compactTestOrbit hS hRank Φ hΦ L q hq hBound
  have hPair := (contMDiff_determinantWeight (n := t + 2) (charData p w) (((t : ℂ) + 1) / 2)).prodMk hEval
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hPair
  have hMul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2) := contDiff_fst.mul contDiff_snd
  exact (hMul.comp_contMDiff hPair).comp (contMDiff_mul_left (a := weylLong (t + 2) ℝ))

private def determinantSlope (c : RealCharacterData) (B : Y) : ℂ :=
  fderiv ℝ (unitsExtension (determinantWeight c (((t + 1 : ℕ) : ℂ) / 2) : H → ℂ)) 1 B

private theorem rightDerivative_compactTestOrbit {S : Set X} (hS : IsCompact S)
    (L : supportedSchwartz S →ₗ[ℂ] ℂ) (q : Seminorm ℝ 𝓢(X, ℂ)) (hq : Continuous q)
    (hBound : ∀ Φ, ‖L Φ‖ ≤ q Φ.val)
    {U : Set Y} (hU : IsOpen U) (h₁ : 1 ∈ U) (hUnit : ∀ A ∈ U, IsUnit A)
    (Q : Y → supportedSchwartz S) (Φ : 𝓢(X, ℂ)) (hΦ : ∀ x ∉ S, Φ x = 0)
    (hQ : ∀ A ∈ U, ∀ x, (Q A).val x = Φ (x * A))
    (c : RealCharacterData) (B : Y) (g : H)
    {F : H → ℂ} (hF : ContMDiff I 𝓘(ℝ, ℂ) ∞ F)
    (hOrbit : ∀ k : H, k.val ∈ U → F (g * k) =
      determinantWeight c (((t + 1 : ℕ) : ℂ) / 2) k * L (Q k.val)) :
    R B F g = determinantSlope c B * F g + L (rectangularRightVariation Φ B S hS hΦ) := by
  let D : H →* ℂ := determinantWeight c (((t + 1 : ℕ) : ℂ) / 2)
  let W := unitsExtension (⇑D)
  have hW : DifferentiableAt ℝ W 1 :=
    differentiableAt_unitsExtension (contMDiff_determinantWeight c _) isUnit_one
  have hW₁ : W 1 = 1 := (unitsExtension_val (⇑D) (1 : H)).trans (map_one D)
  have hNear : (fun A : Y => unitsExtension F (g.val * A)) =ᶠ[𝓝 (1 : Y)]
      fun A => W A * L (Q A) := by
    filter_upwards [hU.mem_nhds h₁] with A hA
    obtain ⟨k, rfl⟩ := hUnit A hA
    rw [← Units.val_mul, unitsExtension_val, show W k.val = D k from unitsExtension_val _ k]
    exact hOrbit k hA
  have hVal : L (Q 1) = F g := by
    have h := hOrbit (1 : H) h₁
    rw [mul_one, map_one, one_mul] at h
    exact h.symm
  obtain ⟨hEval, hDeriv⟩ := compactOrbit_evaluation hS L q hq hBound hU Q Φ hQ
  have hEval' := (hEval.contDiffAt (hU.mem_nhds h₁)).differentiableAt (by simp)
  rw [rightDerivative_eq_fderiv_mul_left hF, hNear.fderiv_eq, fderiv_fun_mul hW hEval']
  change W 1 * fderiv ℝ (fun A => L (Q A)) 1 B + L (Q 1) * determinantSlope c B = _
  rw [hW₁, one_mul, hVal, hDeriv h₁ B hΦ]
  ring

private theorem determinantSlope_charData (p : Fin 2) (w : ℂ) (B : Y) :
    determinantSlope (charData p w) B =
      (w + (((t + 1 : ℕ) : ℂ) / 2)) * fderiv ℝ (fun A : Y => (Real.log A.det : ℂ)) 1 B := by
  let v := (((t + 1 : ℕ) : ℂ) / 2)
  let b : Y → ℂ := fun A => Real.log A.det
  let F : H → ℂ := determinantWeight (charData p w) v
  have hDet : ContDiff ℝ ∞ (Matrix.det : Y → ℝ) :=
    PrincipalSeriesExtension.contDiff_det_comp PrincipalSeriesExtension.contDiff_entry
  have hpos : ∀ᶠ A : Y in 𝓝 (1 : Y), 0 < A.det :=
    (isOpen_lt continuous_const hDet.continuous).mem_nhds (by simp)
  have hEq : unitsExtension F =ᶠ[𝓝 (1 : Y)] fun A => Complex.exp ((w + v) * b A) := by
    filter_upwards [hpos] with A hA
    obtain ⟨g, rfl⟩ := (Matrix.isUnit_iff_isUnit_det A).mpr hA.ne'.isUnit
    rw [unitsExtension_val]
    change charFun p w g.val.det * ((|g.val.det| : ℝ) : ℂ) ^ v = _
    have hne : (g.val.det : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
    unfold RealJacquetFrobenius.charFun
    simp only [abs_of_pos hA, div_self hA.ne', Complex.ofReal_one, one_pow, one_mul]
    rw [← Complex.cpow_add w v hne, Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hA.le, mul_comm]
  have hLog : DifferentiableAt ℝ b (1 : Y) := Complex.ofRealCLM.differentiableAt.comp _
    ((hDet.differentiable (by simp) 1).log (by simp))
  have hd := (hLog.hasFDerivAt.const_mul (w + v)).cexp.fderiv
  rw [determinantSlope, show (⇑(determinantWeight (charData p w) v) : H → ℂ) = F from rfl,
    hEq.fderiv_eq, hd]
  change Complex.exp ((w + v) * b 1) * ((w + v) * fderiv ℝ b 1 B) = _
  simp [b, v]

/-- The right derivative of the upper column is the sum of the determinant derivative
and the column formed with the first variation of the compact test. -/
theorem rightDerivative_godementLeadingFamily (D : RealQuotientMeasureData t) (a : ℝˣ) (W : G → ℂ)
    (hW : ∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W ∈
      RealLocalWhittaker.regularFunctions t (-a))
    (hGrowth : RealUniformWhittaker.HasUniformDerivativeGrowth W) (p : Fin 2) (w : ℂ)
    {S : Set X} (hS : IsCompact S) (hRank : ∀ x ∈ S, HasFullRowRank x)
    (Φ : 𝓢(X, ℂ)) (hΦ : ∀ x ∉ S, Φ x = 0) (B : Y) :
    let C (φ : 𝓢(X, ℂ)) (g : H) := godementLeadingFamily D a φ W p g w
    R B (C Φ) =
      ((w + (((t + 1 : ℕ) : ℂ) / 2)) * fderiv ℝ (fun A : Y => (Real.log A.det : ℂ)) 1 B) • C Φ +
      C (rectangularRightVariation Φ B S hS hΦ).val := by
  intro C
  let c := charData p w
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  have hC := contMDiff_godementLeadingFamily D a W hW hGrowth p w hS hRank Φ hΦ
  obtain ⟨U, T, hU, h₁, hUnit, hT, hST, _, Q, hQ⟩ := realGodementCompactOrbit S hS hRank Φ hΦ (1 : H)
  have hΦT : ∀ x ∉ T, Φ x = 0 := fun x hx => hΦ x fun h => hx (hST h)
  let ΨT := rectangularRightVariation Φ B T hT hΦT
  have hΨ : ΨT.val = (rectangularRightVariation Φ B S hS hΦ).val := by
    ext x
    rw [rectangularRightVariation_apply, rectangularRightVariation_apply]
  funext g
  let e := weylLong (t + 2) ℝ * g
  let s := w + (t : ℂ) / 2
  let P := rectangularTranslateCLM (r := t + 1) 1 e
  let δ := determinantWeight c (((t : ℂ) + 1) / 2) e
  let M := columnMellinLinear μ a W hW hGrowth p.val s
  let L := δ • ((M.comp P.toLinearMap).comp (supportedSchwartz T).subtype)
  have hL (φ : supportedSchwartz T) : L φ = C φ.val g := rfl
  obtain ⟨q, hq, hB⟩ := exists_columnMellinLinear_bound μ a W hW hGrowth p.val s
  let q' := ‖δ‖₊ • q.comp (P.restrictScalars ℝ).toLinearMap
  have hq' : Continuous q' := (hq.comp P.continuous).const_mul ‖δ‖
  have hB' (φ : supportedSchwartz T) : ‖L φ‖ ≤ q' φ.val := by
    change ‖δ * M (P φ.val)‖ ≤ ‖δ‖ * q (P φ.val)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  have hEq (k : H) (hk : k.val ∈ U) : C Φ (g * k) =
      determinantWeight c (((t + 1 : ℕ) : ℂ) / 2) k * L (Q k.val) := by
    rw [hL, orbitTest_eq Φ Q hQ k hk]
    exact godementLeadingFamily_rightTranslate D a Φ W p g k w
  have hd := rightDerivative_compactTestOrbit hT L q' hq' hB' hU h₁ hUnit Q Φ hΦT hQ c B g hC hEq
  rw [hd, show L ΨT = C ΨT.val g from hL ΨT, hΨ, show c = charData p w from rfl, determinantSlope_charData]
  rfl

private theorem compactGenerator_rightDerivative (D : RealQuotientMeasureData t) (a : ℝˣ)
    {ds : List RealBlock} (hDom : IsStrictlyDominant (realPositionExponent ds) t)
    (f : principalSeries ℝ (t + 1) (realPositionCharacter ds)) (p : Fin 2) (w : ℂ)
    {S : Set X} (hS : IsCompact S) (hRank : ∀ x ∈ S, HasFullRowRank x)
    (Φ : 𝓢(X, ℂ)) (hΦ : ∀ x ∉ S, Φ x = 0) (B : Y) :
    let c := charData p w
    let Ψ := (rectangularRightVariation Φ B S hS hΦ).val
    let F (φ : 𝓢(X, ℂ)) := sectionValue D.groupHaar c f.val φ
    let C (φ : 𝓢(X, ℂ)) (g : H) := godementLeadingFamily D a φ (additiveJacquetIntegral a f.val) p g w
    R B (F Φ) = determinantSlope c B • F Φ + F Ψ ∧
      R B (C Φ) = determinantSlope c B • C Φ + C Ψ := by
  intro c Ψ F C
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  obtain ⟨U, T, hU, h₁, hUnit, hT, hST, hRankT, Q, hQ⟩ :=
    realGodementCompactOrbit S hS hRank Φ hΦ (1 : H)
  have hΦT : ∀ x ∉ T, Φ x = 0 := fun x hx => hΦ x fun h => hx (hST h)
  let ΨT := rectangularRightVariation Φ B T hT hΦT
  have hΨ : ΨT.val = Ψ := by
    ext x
    rw [rectangularRightVariation_apply, show Ψ x = fderiv ℝ (⇑Φ) x (x * B) from rfl]
  have hF : ContMDiff I 𝓘(ℝ, ℂ) ∞ (F Φ) :=
    (realGodementSection (t + 1) μ c ds f.val f.property S hS hRank Φ (Φ.smooth ⊤) hΦ).1
  refine ⟨?_, ?_⟩
  · funext g
    obtain ⟨L, q, hq, hL⟩ := exists_sectionTestLinear μ c f.val f.property.1.continuous g hT hRankT
    have hEq (k : H) (hk : k.val ∈ U) : F Φ (g * k) =
        determinantWeight c (((t + 1 : ℕ) : ℂ) / 2) k * L (Q k.val) := by
      rw [(hL (Q k.val)).1, orbitTest_eq Φ Q hQ k hk]
      exact congrFun (sectionValue_rightTranslate μ c f.val Φ k) g
    have hd := rightDerivative_compactTestOrbit hT L q hq (fun φ => (hL φ).2) hU h₁ hUnit Q Φ hΦT
      hQ c B g hF hEq
    rw [hd, show L ΨT = F ΨT.val g from (hL ΨT).1, hΨ]
    rfl
  · obtain ⟨hW, hGrowth⟩ := regular_additiveJacquetIntegral a hDom f
    change R B (C Φ) = determinantSlope (charData p w) B • C Φ + C Ψ
    rw [determinantSlope_charData]
    exact rightDerivative_godementLeadingFamily D a _ hW hGrowth p w hS hRank Φ hΦ B

/-- A continued evaluation with the compact generator formula is smooth and
intertwines the matrix right derivatives on the entire compact section span. -/
def RealGodementSpanLieStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2) (ds : List RealBlock),
    IsStrictlyDominant (realPositionExponent ds) t → ∀ w : ℂ,
    let c := charData p w
    let V := compactSectionSpan D.groupHaar c ds
    ∀ J : V →ₗ[ℂ] (H → ℂ),
      (∀ (f : principalSeries ℝ (t + 1) (realPositionCharacter ds))
        (S : Set X), IsCompact S → (∀ x ∈ S, HasFullRowRank x) →
        ∀ (Φ : 𝓢(X, ℂ)), (∀ x ∉ S, Φ x = 0) →
        ∀ F : V, F.val = sectionValue D.groupHaar c f.val Φ → ∀ g,
          J F g = godementLeadingFamily D a Φ (additiveJacquetIntegral a f.val) p g w) →
      (∀ F, ContMDiff I 𝓘(ℝ, ℂ) ∞ (J F)) ∧
      ∀ B : Y, ∃ T : V →ₗ[ℂ] V,
        ∀ F, (T F).val = R B F.val ∧ J (T F) = R B (J F)

theorem realGodementSpanLie : RealGodementSpanLieStatement (t := t) := by
  intro D a p ds hDom w c V J hJ
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  let G₀ : Set (H → ℂ) := {F | ∃ (f : G → ℂ) (S : Set X) (φ : X → ℂ),
    f ∈ principalSeries ℝ (t + 1) (realPositionCharacter ds) ∧ IsCompact S ∧
    (∀ x ∈ S, HasFullRowRank x) ∧ ContDiff ℝ ∞ φ ∧ (∀ x ∉ S, φ x = 0) ∧
    F = sectionValue μ c f φ}
  let A : Set V := (Subtype.val : V → H → ℂ) ⁻¹' G₀
  have hSpan : Submodule.span ℂ A = ⊤ := Submodule.span_span_coe_preimage
  have hFromGen {P : Submodule ℂ V} (hP : A ⊆ P) (F : V) : F ∈ P :=
    (Submodule.span_le.mpr hP) (hSpan.symm ▸ Submodule.mem_top)
  let V₀ := SmoothRightAction.smoothFunctions (t + 2)
  have hSmooth (F : V) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (J F) := by
    change J F ∈ V₀
    refine hFromGen (P := V₀.comap J) ?_ F
    intro U hU
    obtain ⟨f, S, φ, hf, hS, hRank, hφ, hZero, he⟩ := hU
    let Φ := ofCompactSupport φ hφ S hS hZero
    change ContMDiff I 𝓘(ℝ, ℂ) ∞ (J U)
    have hEq := funext (hJ ⟨f, hf⟩ S hS hRank Φ hZero U he)
    rw [hEq]
    obtain ⟨hW, hGrowth⟩ := regular_additiveJacquetIntegral a hDom ⟨f, hf⟩
    exact contMDiff_godementLeadingFamily D a _ hW hGrowth p w hS hRank Φ hZero
  refine ⟨hSmooth, fun B => ?_⟩
  let d := rightDerivativeLinearMap V
    (fun _ hF => (compactSectionSpan_le_principalSeries μ c ds hF).1) B
  have hGen (F : V) (hF : F ∈ A) : ∃ Z : V, d F = Z.val ∧ R B (J F) = J Z := by
    obtain ⟨f, S, φ, hf, hS, hRank, hφ, hZero, he⟩ := hF
    let Φ := ofCompactSupport φ hφ S hS hZero
    let Ψ := rectangularRightVariation Φ B S hS hZero
    let U : V := ⟨sectionValue μ c f Ψ.val, Submodule.subset_span
      ⟨f, S, Ψ.val, hf, hS, hRank, Ψ.val.smooth ⊤, Ψ.property, rfl⟩⟩
    let Z := determinantSlope c B • F + U
    obtain ⟨hD, hE⟩ := compactGenerator_rightDerivative D a hDom ⟨f, hf⟩ p w hS hRank Φ hZero B
    refine ⟨Z, ?_, ?_⟩
    · change R B F.val = determinantSlope c B • F.val + U.val
      rw [he]
      exact hD
    · have hJF := funext (hJ ⟨f, hf⟩ S hS hRank Φ hZero F he)
      have hJU := funext (hJ ⟨f, hf⟩ S hS hRank Ψ.val Ψ.property U rfl)
      rw [show Z = determinantSlope c B • F + U from rfl, map_add, map_smul, hJF, hJU]
      exact hE
  have hMem (F : V) : d F ∈ V := by
    refine hFromGen (P := V.comap d) ?_ F
    intro U hU
    obtain ⟨Z, hZ, _⟩ := hGen U hU
    change d U ∈ V
    rw [hZ]
    exact Z.property
  let T := d.codRestrict V hMem
  let E := (rightDerivativeLinearMap V₀ (fun _ h => h) B).comp (J.codRestrict V₀ hSmooth)
  refine ⟨T, fun F => ⟨rfl, ?_⟩⟩
  have hEq : Set.EqOn (J.comp T) E A := by
    intro U hU
    obtain ⟨Z, hZ, hZ'⟩ := hGen U hU
    have hTZ : T U = Z := Subtype.ext hZ
    change J (T U) = R B (J U)
    rw [hTZ, hZ']
  exact LinearMap.eqOn_span hEq (hSpan.symm ▸ Submodule.mem_top)

end Langlands.Global.RankinSelbergGlobal.RealGodement
