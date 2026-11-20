import Langlands.Representation.Archimedean.RealLeviCartanDifferential
import Langlands.Representation.Archimedean.RealCartanPeakTest

/-! # Differential of the compact argument at a fixed block flag -/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator ContDiff

namespace Langlands.Archimedean.RealCartanArgumentDifferential

open GramFormula PrincipalSeriesExtension RealLeviChart RealLeviCartanDifferential
  RealLeviCompactChart RealCartanCompactSupport RealCartanPeakTest

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "Mat" k:max => Matrix (Fin k) (Fin k) ℝ
local notation "K" k:max => Matrix.unitaryGroup (Fin k) ℝ
local notation "G" k:max => Langlands.GeneralLinear k ℝ

section Matrix

variable {n : ℕ}

private def transposeCLM : Mat n →L[ℝ] Mat n :=
  (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toLinearMap.toContinuousLinearMap

/-- The linear operation `A ↦ q * A * qᵀ`. -/
def conjugationCLM (q : Mat n) : Mat n →L[ℝ] Mat n :=
  ({ toFun := fun A => q * A * qᵀ
     map_add' := fun _ _ => by rw [Matrix.mul_add, Matrix.add_mul]
     map_smul' := fun _ _ => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
   } : Mat n →ₗ[ℝ] Mat n).toContinuousLinearMap

@[simp]
theorem conjugationCLM_apply (q A : Mat n) : conjugationCLM q A = q * A * qᵀ := rfl

private theorem val_inv (u : K n) : ((u⁻¹ : K n) : Mat n) = (u : Mat n)ᵀ := by
  change star (u : Mat n) = (u : Mat n)ᵀ
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

private theorem signedOrthogonal_diagonal_pos (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    signedOrthogonal (diagonal d) = 1 := by
  have h := signedOrthogonal_mul (b := diagonal d) (κ := (1 : Mat n))
    (blockTriangular_diagonal d) (fun i => by simpa using (hd i).ne') (by simp)
  simpa [signReal, hd] using h

private theorem hasFDerivAt_mul_of_one {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f g : P → Mat n} {F H : P →L[ℝ] Mat n}
    (hf : HasFDerivAt f F 0) (hg : HasFDerivAt g H 0) (hf₀ : f 0 = 1) (hg₀ : g 0 = 1) :
    HasFDerivAt (fun p => f p * g p) (F + H) 0 := by
  refine (hf.mul' hg).congr_fderiv ?_
  rw [hf₀, hg₀, MulOpposite.op_one, one_smul, one_smul, add_comm]

end Matrix

section Local

variable {c : ℕ} (sz : Fin c → ℕ)
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

local notation "N" => ∑ i, sz i
local notation "XSpace" => (Coord sz → ℝ)

private def radialPart (d : Fin N → ℝ) (X : XSpace) : Mat N :=
  signedOrthogonal (signedOrthogonal (lower sz X) * diagonal d)

private theorem radialPart_zero (d : Fin N → ℝ) (hd : ∀ i, 0 < d i) :
    radialPart sz d 0 = 1 := by
  rw [radialPart, signedOrthogonal_lower_zero, one_mul, signedOrthogonal_diagonal_pos d hd]

/-- The compact argument in a chart centered at a fixed flag. The parameters
`W` and `B` are orthogonal matrices, and `a` varies the left compact factor
from the identity before it is translated to the fixed factor `B`. -/
def localArgumentMatrix (d : Fin N → ℝ) (B W : Mat N) (a : P → Mat N)
    (p : XSpace × P) : Mat N :=
  conjugationCLM Wᵀ
    (conjugationCLM B (radialPart sz d p.1)ᵀ * (a p.2)ᵀ *
      signedOrthogonal (lower sz p.1))

/-- In lower entries the differential is the difference of the two
transverse variations and the variation of the left compact factor,
transported by the fixed frame. -/
def argumentDerivative (d : Fin N → ℝ) (B W : Mat N) (A : P →L[ℝ] Mat N) :
    (XSpace × P) →L[ℝ] (LowerIndex N → ℝ) :=
  let X := ContinuousLinearMap.fst ℝ XSpace P
  let Z := ContinuousLinearMap.snd ℝ XSpace P
  (lowerProjection N).comp ((conjugationCLM Wᵀ).comp
    ((transverseSkew sz).comp X -
      (conjugationCLM B).comp ((transverseSkew sz).comp ((radialScale sz d).comp X)) -
      A.comp Z))

theorem contDiffAt_localArgumentMatrix (d : Fin N → ℝ) (hd : ∀ i, 0 < d i)
    (B W : Mat N) {a : P → Mat N} (ha : ContDiffAt ℝ ∞ a 0) :
    ContDiffAt ℝ ∞ (localArgumentMatrix sz d B W a) 0 := by
  let T : Mat N →L[ℝ] Mat N := transposeCLM
  let X := ContinuousLinearMap.fst ℝ XSpace P
  let Z := ContinuousLinearMap.snd ℝ XSpace P
  have hR : ContDiffAt ℝ ∞ (radialPart sz d) 0 := (realLeviCartanDifferential sz d hd).1
  have h1 : ContDiffAt ℝ ∞ (fun p : XSpace × P =>
      conjugationCLM B (radialPart sz d p.1)ᵀ) 0 :=
    ((conjugationCLM B).comp T).contDiff.contDiffAt.comp 0
      (hR.comp 0 X.contDiff.contDiffAt)
  have h2 : ContDiffAt ℝ ∞ (fun p : XSpace × P => (a p.2)ᵀ) 0 :=
    T.contDiff.contDiffAt.comp 0 (ha.comp 0 Z.contDiff.contDiffAt)
  have h3 : ContDiffAt ℝ ∞ (fun p : XSpace × P => signedOrthogonal (lower sz p.1)) 0 :=
    (contDiff_signedOrthogonal_lower sz).contDiffAt.comp 0 X.contDiff.contDiffAt
  exact (conjugationCLM Wᵀ).contDiff.contDiffAt.comp 0 ((h1.mul h2).mul h3)

set_option maxHeartbeats 400000 in
theorem hasFDerivAt_projected_localArgumentMatrix (d : Fin N → ℝ) (hd : ∀ i, 0 < d i)
    (B W : Mat N) (hB : B * Bᵀ = 1)
    {a : P → Mat N} {A : P →L[ℝ] Mat N}
    (ha : HasFDerivAt a A 0) (ha₀ : a 0 = 1) (haSkew : ∀ z, (A z)ᵀ = -(A z)) :
    HasFDerivAt (fun p => lowerProjection N (localArgumentMatrix sz d B W a p))
      (argumentDerivative sz d B W A) 0 := by
  let T : Mat N →L[ℝ] Mat N := transposeCLM
  let X := ContinuousLinearMap.fst ℝ XSpace P
  let Z := ContinuousLinearMap.snd ℝ XSpace P
  let D := (transverseSkew sz).comp ((radialScale sz d).comp X)
  let F (p : XSpace × P) := conjugationCLM B (radialPart sz d p.1)ᵀ
  let H (p : XSpace × P) := (a p.2)ᵀ
  let L (p : XSpace × P) := signedOrthogonal (lower sz p.1)
  have hF₀ : F 0 = 1 := by simp [F, radialPart_zero sz d hd, hB]
  have hH₀ : H 0 = 1 := by simp [H, ha₀]
  have hL₀ : L 0 = 1 := by simp [L]
  have hF : HasFDerivAt F (-((conjugationCLM B).comp D)) 0 := by
    have hr := (realLeviCartanDifferential sz d hd).2
    have h := ((conjugationCLM B).comp T).hasFDerivAt.comp 0 (hr.comp 0 X.hasFDerivAt)
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro p
    change conjugationCLM B (transverseSkew sz (radialScale sz d p.1))ᵀ =
      -(conjugationCLM B (transverseSkew sz (radialScale sz d p.1)))
    rw [transverseSkew_transpose, map_neg]
  have hH : HasFDerivAt H (-(A.comp Z)) 0 := by
    refine (T.hasFDerivAt.comp 0 (ha.comp 0 Z.hasFDerivAt)).congr_fderiv ?_
    exact ContinuousLinearMap.ext fun p => haSkew p.2
  have hL : HasFDerivAt L ((transverseSkew sz).comp X) 0 := by
    have hbefore : HasFDerivAt (fun Y : XSpace => signedOrthogonal (lower sz Y))
        (transverseSkew sz) (X (0 : XSpace × P)) := by
      rw [map_zero]
      exact hasFDerivAt_signedOrthogonal_lower sz
    exact hbefore.comp 0 X.hasFDerivAt
  have h := hasFDerivAt_mul_of_one (hasFDerivAt_mul_of_one hF hH hF₀ hH₀) hL
    (by simp [hF₀, hH₀]) hL₀
  let out := (lowerProjection N).comp (conjugationCLM Wᵀ)
  refine (out.hasFDerivAt.comp 0 h).congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro p
  change out (-conjugationCLM B (D p) + -(A p.2) + transverseSkew sz p.1) =
    out (transverseSkew sz p.1 - conjugationCLM B (D p) - A p.2)
  congr 1
  abel

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The compact test argument over a translated opposed chart is given by
`localArgumentMatrix`, with fixed factor `k * R⁻¹ * k⁻¹` and frame `k * w`. -/
theorem compactArgument_eq_localArgumentMatrix (d : Fin N → ℝ)
    (g D : G N) (hD : (D : Mat N) = diagonal d) (w k R : K N)
    (hw : Unitary.toUnits w * g = D * Unitary.toUnits (R * w))
    (hk : Unitary.toUnits k * D = D * Unitary.toUnits k)
    (a : P → K N) (p : XSpace × P) :
    (compactArgument g (signedOrthogonalPart (lowerGL sz p.1) * k * w)
        (a p.2 * (k * R⁻¹ * k⁻¹)) : Mat N) =
      localArgumentMatrix sz d ((k * R⁻¹ * k⁻¹ : K N) : Mat N) ((k * w : K N) : Mat N)
        (fun z => (a z : Mat N)) p := by
  let l := signedOrthogonalPart (lowerGL sz p.1)
  let r := signedOrthogonalPart (Unitary.toUnits l * D)
  let B := k * R⁻¹ * k⁻¹
  let W := k * w
  have hY : Unitary.toUnits (l * k * w) * g =
      (Unitary.toUnits l * D) * Unitary.toUnits (k * R * w) := calc
    _ = Unitary.toUnits l * (Unitary.toUnits k * (Unitary.toUnits w * g)) := by
      simp only [map_mul, mul_assoc]
    _ = Unitary.toUnits l * ((Unitary.toUnits k * D) * Unitary.toUnits (R * w)) := by
      rw [hw, mul_assoc (Unitary.toUnits k)]
    _ = _ := by
      rw [hk]
      simp only [map_mul, mul_assoc]
  have hκ : signedOrthogonalPart (Unitary.toUnits (l * k * w) * g) = r * (k * R * w) := by
    rw [hY, orthogonalPart_mul_right]
  have he : compactArgument g (l * k * w) (a p.2 * B) =
      W⁻¹ * (B * r⁻¹ * B⁻¹ * (a p.2)⁻¹ * l) * W := by
    rw [compactArgument, hκ]
    dsimp only [W, B]
    group
  have hl : (l : Mat N) = signedOrthogonal (lower sz p.1) := rfl
  have hr : (r : Mat N) = radialPart sz d p.1 := by
    change signedOrthogonal ((l : Mat N) * (D : Mat N)) = _
    rw [hl, hD]
    rfl
  change (compactArgument g (l * k * w) (a p.2 * B) : Mat N) =
    localArgumentMatrix sz d (B : Mat N) (W : Mat N) (fun z => (a z : Mat N)) p
  rw [he]
  simp only [localArgumentMatrix, conjugationCLM_apply, Submonoid.coe_mul, val_inv,
    transpose_transpose, hl, hr]

/-- The derivative of the projected compact test argument at a fixed flag
of a positive diagonal times a block orthogonal Cartan element. -/
def RealCartanArgumentDifferentialStatement (c : ℕ) (sz : Fin c → ℕ) (P : Type*)
    [NormedAddCommGroup P] [NormedSpace ℝ P] : Prop :=
  ∀ (d : Fin (∑ i, sz i) → ℝ) (g D : G (∑ i, sz i)) (w k R : K (∑ i, sz i))
    (a : P → K (∑ i, sz i)) (A : P →L[ℝ] Mat (∑ i, sz i)),
    let n := ∑ i, sz i
    let B := k * R⁻¹ * k⁻¹
    let F (p : (Coord sz → ℝ) × P) :=
      lowerProjection n (compactArgument g (signedOrthogonalPart (lowerGL sz p.1) * k * w)
        (a p.2 * B) : Mat n)
    (∀ i, 0 < d i) → (D : Mat n) = diagonal d →
    Unitary.toUnits w * g = D * Unitary.toUnits (R * w) →
    Unitary.toUnits k * D = D * Unitary.toUnits k →
    a 0 = 1 → ContDiffAt ℝ ∞ (fun z => (a z : Mat n)) 0 →
    HasFDerivAt (fun z => (a z : Mat n)) A 0 → (∀ z, (A z)ᵀ = -(A z)) →
    F 0 = 0 ∧ ContDiffAt ℝ ∞ F 0 ∧ HasFDerivAt F
      (argumentDerivative sz d (B : Mat n) ((k * w : K n) : Mat n) A) 0

theorem realCartanArgumentDifferential : RealCartanArgumentDifferentialStatement c sz P := by
  intro d g D w k R a A n B F hd hD hw hk ha₀ hac ha haSkew
  have hB : (B : Mat n) * (B : Mat n)ᵀ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.mem_unitaryGroup_iff.mp B.2)
  have h0 : (a 0 : Mat n) = 1 := congrArg Subtype.val ha₀
  have hW : (((k * w : K n) : Mat n)ᵀ * ((k * w : K n) : Mat n)) = 1 := by
    apply mul_eq_one_comm.mp
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.mem_unitaryGroup_iff.mp (k * w).2)
  have he : F = fun p => lowerProjection n
      (localArgumentMatrix sz d (B : Mat n) ((k * w : K n) : Mat n)
        (fun z => (a z : Mat n)) p) :=
    funext fun p => congrArg (lowerProjection n)
      (compactArgument_eq_localArgumentMatrix sz d g D hD w k R hw hk a p)
  rw [he]
  refine ⟨?_, (lowerProjection n).contDiff.contDiffAt.comp 0
      (contDiffAt_localArgumentMatrix sz d hd _ _ hac),
    hasFDerivAt_projected_localArgumentMatrix sz d hd _ _ hB ha h0 haSkew⟩
  simp only [localArgumentMatrix, Prod.fst_zero, Prod.snd_zero, radialPart_zero sz d hd,
    h0, signedOrthogonal_lower_zero, Matrix.transpose_one, Matrix.mul_one,
    conjugationCLM_apply, hB, Matrix.transpose_transpose, hW, lowerProjection_one]

end Local

end Langlands.Archimedean.RealCartanArgumentDifferential
