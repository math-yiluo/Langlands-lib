import Langlands.Representation.Archimedean.RealCartanAngularDifferential

/-! # Transverse coordinates for the compact Cartan trace -/

noncomputable section

open Matrix Set
open scoped Matrix.Norms.Operator ContDiff

namespace Langlands.Archimedean.RealCartanTraceCoordinates

open RealCartanAngularFrame RealCartanAngularDifferential RealCartanArgumentDifferential
  RealCartanArgumentJacobian RealCartanCompactSupport RealCartanLowerCoordinates RealCartanPeakTest
  RealLeviCartanDifferential RealLeviChart RealLeviCompactChart RealLeviBump
  RealSignedOrthogonalDifferential GramFormula RealLeviParabolicIntegration PrincipalSeriesExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {c : ℕ} (sz : Fin c → ℕ)

local notation "Mat" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "Ortho" n:max => Matrix.unitaryGroup (Fin n) ℝ

local notation "N" => ∑ i, sz i
local notation "K" => Matrix.unitaryGroup (Fin N) ℝ
local notation "M" => Matrix (Fin N) (Fin N) ℝ
local notation "G" => Langlands.GeneralLinear N ℝ
local notation "H" => LeviFrame sz
local notation "XSpace" => (Coord sz → ℝ)
local notation "ZSpace" => (WithinIndex sz → ℝ)
local notation "E" => (XSpace × ZSpace)
local notation "L" => (LowerIndex N → ℝ)

/-- The compact flag chart translated to a fixed coset. -/
def placedFrame (w : K) (κ : H) (X : XSpace) : K := compactFrame sz κ X * w

theorem continuous_placedFrame (w : K) : Continuous (fun p : H × XSpace => placedFrame sz w p.1 p.2) :=
  (continuous_compactFrame sz).mul continuous_const

@[simp]
theorem placedFrame_zero (w : K) (κ : H) : placedFrame sz w κ 0 = blockFrame sz κ * w := by
  rw [placedFrame, compactFrame_zero]

/-- At the fixed flag the left factor is the conjugate of the inverse placed orthogonal part. -/
def fixedLeftFrame (R κ : H) : H := κ * R⁻¹ * κ⁻¹

theorem continuous_fixedLeftFrame (R : H) : Continuous (fixedLeftFrame sz R) :=
  (continuous_id.mul continuous_const).mul continuous_inv

/-- Translate the angular chart to the fixed left factor. -/
def placedLeftFrame (R κ : H) (Z : ZSpace) : H := angularFrame sz Z * fixedLeftFrame sz R κ

theorem continuous_placedLeftFrame (R : H) :
    Continuous (fun p : H × ZSpace => placedLeftFrame sz R p.1 p.2) :=
  ((continuous_angularFrame sz).comp continuous_snd).mul
    ((continuous_fixedLeftFrame sz R).comp continuous_fst)

@[simp]
theorem placedLeftFrame_zero (R κ : H) : placedLeftFrame sz R κ 0 = fixedLeftFrame sz R κ := by
  rw [placedLeftFrame, angularFrame_zero, one_mul]

/-- Coordinates of the compact argument in the two transverse variables. -/
def placedArgument (g : G) (w : K) (R κ : H) (p : E) : K :=
  compactArgument g (placedFrame sz w κ p.1) (blockFrame sz (placedLeftFrame sz R κ p.2))

set_option maxHeartbeats 500000 in
theorem continuous_placedArgument (g : G) (w : K) (R : H) :
    Continuous (fun p : H × E => placedArgument sz g w R p.1 p.2) := by
  have hκ : Continuous (Prod.fst : H × E → H) := continuous_fst
  have hp₀ : Continuous (Prod.snd : H × E → E) := continuous_snd
  have hX : Continuous (Prod.fst : E → XSpace) := continuous_fst
  have h1 := (continuous_placedFrame sz w).comp (hκ.prodMk (hX.comp hp₀))
  have hZ : Continuous (Prod.snd : E → ZSpace) := continuous_snd
  have hp := hκ.prodMk (hZ.comp hp₀)
  have hl := (continuous_placedLeftFrame sz R).comp hp
  have h2 := (continuous_blockFrame sz).comp hl
  simpa only [Function.comp_def, placedArgument] using
    (continuous_compactArgument g).comp (h1.prodMk h2)

/-- The block frame map is injective, by restriction to each block. -/
theorem blockFrame_injective : Function.Injective (blockFrame sz) := by
  intro κ ρ h
  funext i
  apply Subtype.ext
  apply Units.ext
  ext a b
  have he := congrArg (fun k : K => (k : M) (pos sz i a) (pos sz i b)) h
  change blockDiagHom sz (fun j => (κ j).val.val) (pos sz i a) (pos sz i b) =
    blockDiagHom sz (fun j => (ρ j).val.val) (pos sz i a) (pos sz i b) at he
  simpa only [blockDiagHom_pos_pos_self] using he

/-- Chart coordinates on the translated block subgroup have lower part zero. -/
theorem lower_eq_zero_of_placedFrame_mem (w : K) (κ : H) (X : XSpace)
    (h : placedFrame sz w κ X ∈ range (fun ρ => blockFrame sz ρ * w)) : X = 0 := by
  obtain ⟨ρ, hρ⟩ := h
  have he : compactFrame sz κ X = blockFrame sz ρ := mul_right_cancel hρ.symm
  have hb := frameBump_compactFrame sz κ X
  rw [he, frameBump_eq_one_of_blockZero sz (blockZero_blockFrame sz ρ)] at hb
  by_contra hX
  exact (ne_of_lt (beta_lt_one hX)) hb.symm

/-- Strictly lower entries of the compact argument. -/
def projectedArgument (g : G) (w : K) (R κ : H) (p : E) : L :=
  lowerProjection N (placedArgument sz g w R κ p : M)

theorem continuous_projectedArgument (g : G) (w : K) (R : H) :
    Continuous (fun p : H × E => projectedArgument sz g w R p.1 p.2) :=
  (lowerProjection N).continuous.comp (continuous_subtype_val.comp (continuous_placedArgument sz g w R))

section Differential

private def transposeMap : M →L[ℝ] M :=
  (Matrix.transposeLinearEquiv (Fin N) (Fin N) ℝ ℝ).toLinearMap.toContinuousLinearMap

private theorem contDiff_radial (D : G) : ContDiff ℝ ∞ (fun X : XSpace =>
    signedOrthogonal (signedOrthogonal (lower sz X) * (D : M))) := by
  apply contDiff_iff_contDiffAt.mpr
  intro X
  let F (z : XSpace) := signedOrthogonal (lower sz z) * (D : M)
  have h : IsUnit (F X) := (Unitary.toUnits (signedOrthogonalPart (lowerGL sz X)) * D).isUnit
  have hf : ContDiff ℝ ∞ F := (contDiff_signedOrthogonal_lower sz).mul contDiff_const
  have hO : ContDiffAt ℝ ∞ (signedOrthogonal : M → M) (F X) := contDiffAt_signedOrthogonal h
  show ContDiffAt ℝ ∞ (signedOrthogonal ∘ F) X
  exact hO.comp X hf.contDiffAt

private def jointArgument (D : G) (p : (M × M) × E) : L :=
  lowerProjection N (conjugationCLM p.1.2ᵀ
    (conjugationCLM p.1.1 (signedOrthogonal
      (signedOrthogonal (lower sz p.2.1) * (D : M)))ᵀ *
      (angularMatrix sz p.2.2 : M)ᵀ * signedOrthogonal (lower sz p.2.1)))

private theorem contDiff_jointArgument (D : G) (hsize : ∀ i, sz i = 1 ∨ sz i = 2) :
    ContDiff ℝ ∞ (jointArgument sz D) := by
  let B (p : (M × M) × E) := p.1.1
  let W (p : (M × M) × E) := p.1.2
  let X (p : (M × M) × E) := p.2.1
  let Z (p : (M × M) × E) := p.2.2
  let T := transposeMap sz
  have hB : ContDiff ℝ ∞ B := contDiff_fst.fst
  have hW : ContDiff ℝ ∞ W := contDiff_fst.snd
  have hX : ContDiff ℝ ∞ X := contDiff_snd.fst
  have hZ : ContDiff ℝ ∞ Z := contDiff_snd.snd
  have hF := T.contDiff.comp ((contDiff_radial sz D).comp hX)
  have hA := T.contDiff.comp ((realCartanAngularDifferential c sz hsize).1.comp hZ)
  have hL := (contDiff_signedOrthogonal_lower sz).comp hX
  exact (lowerProjection N).contDiff.comp
    (((T.contDiff.comp hW).mul ((((hB.mul hF).mul (T.contDiff.comp hB)).mul hA).mul hL)).mul hW)

private theorem projectedArgument_eq_jointArgument (g D : G) (w : K) (R κ : H)
    (d : Fin N → ℝ) (hD : (D : M) = diagonal d)
    (hw : Unitary.toUnits w * g = D * Unitary.toUnits (blockFrame sz R * w))
    (hκ : Unitary.toUnits (blockFrame sz κ) * D = D * Unitary.toUnits (blockFrame sz κ)) (p : E) :
    projectedArgument sz g w R κ p = jointArgument sz D
      ((((blockFrame sz (fixedLeftFrame sz R κ) : K) : M), ((blockFrame sz κ * w : K) : M)), p) := by
  simp only [projectedArgument, placedArgument, placedFrame, compactFrame_eq_mul_blockFrame,
    placedLeftFrame, fixedLeftFrame, map_mul, map_inv]
  rw [← angularMatrix]
  rw [compactArgument_eq_localArgumentMatrix sz d g D hD w (blockFrame sz κ) (blockFrame sz R) hw hκ]
  change lowerProjection N (localArgumentMatrix sz d _ _ _ p) = _
  unfold jointArgument localArgumentMatrix
  rw [hD]
  rfl

/-- The projected argument has a jointly continuous family of transverse derivatives. -/
def RealCartanTraceCoordinatesStatement : Prop :=
  ∀ (c : ℕ) (sz : Fin c → ℕ) (g D : Langlands.GeneralLinear (∑ i, sz i) ℝ)
    (w : Matrix.unitaryGroup (Fin (∑ i, sz i)) ℝ) (R : LeviFrame sz)
    (d : Fin (∑ i, sz i) → ℝ),
    (∀ i, sz i = 1 ∨ sz i = 2) → (∀ i, 0 < d i) → (D : Mat (∑ i, sz i)) = diagonal d →
    Unitary.toUnits w * g = D * Unitary.toUnits (blockFrame sz R * w) →
    (∀ κ, Unitary.toUnits (blockFrame sz κ) * D = D * Unitary.toUnits (blockFrame sz κ)) →
    let T := (Coord sz → ℝ) × (WithinIndex sz → ℝ)
    let Y := LowerIndex (∑ i, sz i) → ℝ
    ∃ A : LeviFrame sz × T → T →L[ℝ] Y, Continuous A ∧
      (∀ κ z, HasFDerivAt (projectedArgument sz g w R κ) (A (κ, z)) z) ∧
      ∀ κ, projectedArgument sz g w R κ 0 = 0 ∧ A (κ, 0) =
        argumentDerivative sz d (blockFrame sz (fixedLeftFrame sz R κ) : Mat (∑ i, sz i))
          ((blockFrame sz κ * w : Ortho (∑ i, sz i)) : Mat (∑ i, sz i)) (interiorSkew sz)

set_option maxHeartbeats 500000 in
theorem realCartanTraceCoordinates : RealCartanTraceCoordinatesStatement := by
  intro c sz g D w R d hsize hd hD hw hκ T Y
  let n := ∑ i, sz i
  let J := jointArgument sz D
  have hJ : ContDiff ℝ ∞ J := contDiff_jointArgument sz D hsize
  let B (κ : LeviFrame sz) := (blockFrame sz (fixedLeftFrame sz R κ) : Mat n)
  let W (κ : LeviFrame sz) := ((blockFrame sz κ * w : Ortho n) : Mat n)
  let F (p : LeviFrame sz × T) := ((B p.1, W p.1), p.2)
  let I := ContinuousLinearMap.inr ℝ (Mat n × Mat n) T
  have hB : Continuous B := continuous_subtype_val.comp
    ((continuous_blockFrame sz).comp (continuous_fixedLeftFrame sz R))
  have hW : Continuous W := continuous_subtype_val.comp ((continuous_blockFrame sz).mul continuous_const)
  have hF : Continuous F := ((hB.prodMk hW).comp continuous_fst).prodMk continuous_snd
  let A (p : LeviFrame sz × T) := (fderiv ℝ J (F p)).comp I
  have hA : Continuous A := ((hJ.continuous_fderiv (by simp)).comp hF).clm_comp continuous_const
  refine ⟨A, hA, ?_, ?_⟩
  · intro κ z
    have he : projectedArgument sz g w R κ = fun p => J ((B κ, W κ), p) :=
      funext (projectedArgument_eq_jointArgument sz g D w R κ d hD hw (hκ κ))
    rw [he]
    exact (hJ.differentiable (by simp) (F (κ, z))).hasFDerivAt.comp z
      ((hasFDerivAt_const (c := (B κ, W κ)) z).prodMk (hasFDerivAt_id z))
  · intro κ
    have ha := realCartanAngularDifferential c sz hsize
    have h := realCartanArgumentDifferential sz d g D w (blockFrame sz κ) (blockFrame sz R)
      (angularMatrix sz) (interiorSkew sz) hd hD hw (hκ κ) (angularMatrix_zero sz)
      ha.1.contDiffAt ha.2 (interiorSkew_transpose sz)
    have he : projectedArgument sz g w R κ = fun p =>
        lowerProjection (∑ i, sz i)
          (compactArgument g (signedOrthogonalPart (lowerGL sz p.1) * blockFrame sz κ * w)
            (angularMatrix sz p.2 * (blockFrame sz κ * (blockFrame sz R)⁻¹ * (blockFrame sz κ)⁻¹)) :
              Mat n) := by
      funext p
      simp only [projectedArgument, placedArgument, placedFrame, compactFrame_eq_mul_blockFrame,
        placedLeftFrame, fixedLeftFrame, map_mul, map_inv, angularMatrix]
    rw [he]
    refine ⟨h.1, ?_⟩
    have hD₀ : HasFDerivAt (projectedArgument sz g w R κ) (A (κ, 0)) 0 := by
      rw [show projectedArgument sz g w R κ = fun p => J ((B κ, W κ), p) from
        funext (projectedArgument_eq_jointArgument sz g D w R κ d hD hw (hκ κ))]
      exact (hJ.differentiable (by simp) (F (κ, 0))).hasFDerivAt.comp 0
        ((hasFDerivAt_const (c := (B κ, W κ)) (0 : T)).prodMk (hasFDerivAt_id 0))
    rw [he] at hD₀
    simpa only [fixedLeftFrame, map_mul, map_inv] using hD₀.unique h.2.2

end Differential

end Langlands.Archimedean.RealCartanTraceCoordinates
