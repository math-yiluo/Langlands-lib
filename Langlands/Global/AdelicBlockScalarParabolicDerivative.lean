import Langlands.Global.AdelicBlockScalarLieAction

/-! # The scalar section derivative along an infinite parabolic curve -/

noncomputable section

open scoped Classical ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Automorphic GeneralLinear AdelicBlockParabolic AdelicBlockDeterminantCharacter
open PrimitiveAdelicHeight ArchimedeanGL NumberField

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable (S : ∀ i, OperatorRealization F (B.size i))

local notation "W" => smoothCompactFiniteSections F B S
local notation "C" => coefficientValues F B S
local notation "A" => ArchimedeanMatrix F n
local notation "e" => archimedeanGLCoordinates F n

/-- An infinite adelic curve with the specified right matrix tangent evaluates
the genuine scalar section differential on each fixed finite slice. -/
theorem hasDerivAt_smoothScalarSection_curve
    (f : W) (d : FiniteAdelicGL F n) (b : InfiniteAdelicGL F n)
    (X : RealLieAlgebra F n) {γ : ℝ → InfiniteAdelicGL F n} (h₀ : γ 0 = b)
    (hγ : HasDerivAt (fun t => (e (γ t)).val) ((e b).val * realLieAlgebraToMatrix F n X) 0) :
    HasDerivAt (fun t => f.val.val.val (AdelicGL.pair F n (γ t) d))
      ((sectionDifferential F B S X f).val.val.val (AdelicGL.pair F n b d)) 0 := by
  let s := smoothScalarSlice F B S d f
  have hs := (coordinateExtension_contDiffAt F n s (e b)).differentiableAt (by simp)
  have h := hs.hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (congrArg (fun x => (e x).val) h₀).symm
  have hderiv :
      (sectionDifferential F B S X f).val.val.val (AdelicGL.pair F n b d) =
        fderiv ℝ (coordinateExtension F n s) (e b).val
          ((e b).val * realLieAlgebraToMatrix F n X) := by
    rw [← smoothScalarSlice_apply F B S, smoothScalarSlice_sectionDifferential,
      smoothDifferential_apply]
  rw [hderiv]
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t => by
    change f.val.val.val (AdelicGL.pair F n (γ t) d) = coordinateExtension F n s (e (γ t)).val
    rw [coordinateExtension_apply, ContinuousMulEquiv.symm_apply_apply]
    rfl

/-- The scalar Levi coefficient at an actual compact argument. -/
def normalizedCoefficient (f : W) (k : standardCompact F n) : C :=
  ⟨normalizedSlice F B f.val.val.val k, f.val.val.property.2 k⟩

private theorem projection_ofInfinite (p : Infinite F B) :
    B.leviProjection (Adeles F) (ofInfinite F B p) =
      leviPair F B (B.leviProjection (InfiniteAdeles F) p) 1 := by
  change B.leviProjection (Adeles F) (pair F B p 1) = _
  rw [leviProjection_pair, map_one]

/-- At a compact argument with infinite component one, differentiation along
an infinite parabolic curve is the half-character term plus the actual block
Lie differential of the scalar coefficient. -/
theorem normalizedCoefficient_differential_parabolic
    (f : W) (l : FiniteAdelicGL.standardIntegral F n)
    (X : RealLieAlgebra F n) (p : ℝ → Infinite F B) (hp₀ : p 0 = 1)
    (hp : HasDerivAt (fun t => (e (p t).val).val) (realLieAlgebraToMatrix F n X) 0)
    (a : ℂ) (ha : HasDerivAt (fun t => archimedeanHalfExtension F B (e (p t).val).val) a 0) :
    normalizedCoefficient F B S (sectionDifferential F B S X f) (compactPair F 1 l) =
      a • normalizedCoefficient F B S f (compactPair F 1 l) +
        coefficientDifferential F B S (realLieAlgebraToMatrix F n X)
          (normalizedCoefficient F B S f (compactPair F 1 l)) := by
  apply Subtype.ext
  funext m
  let c := normalizedCoefficient F B S f (compactPair F 1 l)
  let s := B.leviEmbedding (InfiniteAdeles F) (leviInfinite F B m)
  let b := B.leviEmbedding (FiniteAdeles F) (leviFinite F B m)
  let d := b * l.val
  let β (t : ℝ) := (e (p t).val).val
  let M := infiniteLeviMatrix F B m
  have hβ₀ : β 0 = 1 := by
    simp only [β, hp₀, OneMemClass.coe_one, map_one, Units.val_one]
  have hpair : AdelicGL.pair F n s b = B.leviEmbedding (Adeles F) m := by
    have h := AdelicBlockParabolic.pair_projections F B (B.leviInParabolic (Adeles F) m)
    rw [infinite_leviInParabolic, finite_leviInParabolic] at h
    exact congrArg Subtype.val h
  have hpoint (t : ℝ) :
      AdelicGL.pair F n (s * (p t).val) d =
        B.leviEmbedding (Adeles F) m * (ofInfinite F B (p t)).val * (compactPair F 1 l).val := by
    rw [← hpair]
    change AdelicGL.pair F n (s * (p t).val) (b * l.val) =
      AdelicGL.pair F n s b * AdelicGL.pair F n (p t).val 1 * AdelicGL.pair F n 1 l.val
    rw [AdelicGL.pair_mul, AdelicGL.pair_mul, mul_one, mul_one]
  have hbase :
      AdelicGL.pair F n s d = B.leviEmbedding (Adeles F) m * (compactPair F 1 l).val := by
    simpa only [hp₀, OneMemClass.coe_one, map_one, mul_one] using hpoint 0
  have hcurve :
      HasDerivAt (fun t => (e (s * (p t).val)).val)
        ((e s).val * realLieAlgebraToMatrix F n X) 0 := by
    simpa only [map_mul, Units.val_mul] using hp.const_mul (e s).val
  have hLeft := (hasDerivAt_smoothScalarSection_curve F B S f d s X
    (by rw [hp₀]; exact mul_one _) hcurve).const_mul (leviHalfCharacter F B m : ℂ)⁻¹
  change HasDerivAt
    (fun t => (leviHalfCharacter F B m : ℂ)⁻¹ *
      f.val.val.val (AdelicGL.pair F n (s * (p t).val) d)) _ 0 at hLeft
  rw [hbase] at hLeft
  have hC := coefficientExtension_hasDerivAt F B S m c hβ₀ hp
  have hC₀ : coefficientExtension F B S (leviFinite F B m) c (M * β 0) = c.val m := by
    have h := coefficientExtension_levi_mul_parabolic F B S m c (p 0)
    have h1 : leviPair F B (1 : InfiniteLevi F B) (1 : FiniteLevi F B) = 1 := by
      simpa only [map_one] using leviPair_projections F B (1 : FullLevi F B)
    simpa only [M, β, hp₀, OneMemClass.coe_one, map_one, Units.val_one, h1, mul_one] using h
  have ha₀ : archimedeanHalfExtension F B (β 0) = 1 := by
    change archimedeanHalfExtension F B (e (p 0).val).val = 1
    rw [archimedeanHalfExtension_parabolic, hp₀, map_one, map_one, Units.val_one]
  have hRight := ha.mul hC
  change HasDerivAt
    (fun t => archimedeanHalfExtension F B (β t) *
      coefficientExtension F B S (leviFinite F B m) c (M * β t))
    (a * coefficientExtension F B S (leviFinite F B m) c (M * β 0) +
      archimedeanHalfExtension F B (β 0) *
        (coefficientDifferential F B S (realLieAlgebraToMatrix F n X) c).val m) 0 at hRight
  rw [hC₀, ha₀, one_mul] at hRight
  have hEq (t : ℝ) :
      (leviHalfCharacter F B m : ℂ)⁻¹ * f.val.val.val (AdelicGL.pair F n (s * (p t).val) d) =
      archimedeanHalfExtension F B (β t) *
        coefficientExtension F B S (leviFinite F B m) c (M * β t) := by
    rw [hpoint]
    let q := B.leviInParabolic (Adeles F) m
    change (leviHalfCharacter F B m : ℂ)⁻¹ *
      f.val.val.val ((q * ofInfinite F B (p t)).val * (compactPair F 1 l).val) = _
    rw [scalarSection_apply_mul F B C f.val.val, map_mul (parabolicHalfCharacter F B), Units.val_mul,
      parabolicHalfCharacter_section, ← archimedeanHalfExtension_parabolic,
      map_mul (B.leviProjection (Adeles F)), B.leviProjection_section, projection_ofInfinite]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
    change archimedeanHalfExtension F B (β t) *
      c.val (m * leviPair F B (B.leviProjection (InfiniteAdeles F) (p t)) 1) = _
    rw [coefficientExtension_levi_mul_parabolic]
  exact hLeft.unique (hRight.congr_of_eventuallyEq (Filter.Eventually.of_forall hEq))

end Langlands.Global.AdelicBlockScalarSections
