import Langlands.Representation.Archimedean.SmoothHarishChandraModuleStatement
import Langlands.Representation.Archimedean.SmoothHilbertDualHarishChandraStatement
import Langlands.Representation.Archimedean.SmoothHilbertTransposePairingStatement
import Langlands.Representation.Archimedean.BanachOrbitSmoothing

/-! # Smooth Hilbert inverse-transpose pairings from Casselman–Wallach extension -/

noncomputable section

universe uH
open MeasureTheory
open scoped TensorProduct Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors

attribute [local instance 100] LieRing.ofAssociativeRing

section Pairing

variable (F : Type) [RCLike F] (n : ℕ)
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (R : Langlands.GeneralLinear n F →* (H →L[ℂ] H))

local notation "GL" => Langlands.GeneralLinear n F
local notation "θ" => Langlands.GeneralLinear.inverseTranspose n F
local notation "𝓜" => matrixModel F n
local notation "S" => inverseTransposeDualRepresentation F n R
local notation "D" => DerivativeSmoothVectors 𝓜 R
local notation "Dθ" => DerivativeSmoothVectors 𝓜 (inverseTransposeDualRepresentation F n R)
local notation "ε" => derivativeCLM 𝓜 R []
local notation "εθ" => derivativeCLM 𝓜 (inverseTransposeDualRepresentation F n R) []

/-- The complex bilinear form attached to a continuous linear map `T` from the genuine
smooth vectors into the genuine smooth vectors of the inverse-transpose twisted continuous
dual: `B(y, x)` evaluates the functional underlying `T x` on the vector underlying `y`. -/
def smoothDualTwistPairing (T : D →L[ℂ] Dθ) : D →ₗ[ℂ] D →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun y x => εθ (T x) (ε y))
    (fun y₁ y₂ x => by rw [map_add, map_add])
    (fun c y x => by rw [map_smul, map_smul, smul_eq_mul])
    (fun y x₁ x₂ => by rw [map_add, map_add, add_apply])
    (fun c y x => by rw [map_smul, map_smul, smul_apply, smul_eq_mul])

@[simp]
theorem smoothDualTwistPairing_apply (T : D →L[ℂ] Dθ) (y x : D) :
    smoothDualTwistPairing F n R T y x = εθ (T x) (ε y) :=
  rfl

/-- The inverse-transpose twisted continuous dual of a jointly continuous representation
on a complete Hilbert space is jointly continuous. -/
theorem isContinuousRepresentation_inverseTransposeDual [CompleteSpace H]
    (hR : IsContinuousRepresentation R) :
    IsContinuousRepresentation (inverseTransposeDualRepresentation F n R) := by
  have h : Continuous (fun p : GL × StrongDual ℂ H => continuousDualRepresentation R p.1 p.2) :=
    isContinuousRepresentation_continuousDual (A := Matrix (Fin n) (Fin n) F) R hR
  have hp : Continuous (fun p : GL × StrongDual ℂ H => (θ p.1, p.2)) :=
    ((Langlands.GeneralLinear.continuous_inverseTranspose n F).comp continuous_fst).prodMk
      continuous_snd
  exact h.comp hp

/-- Separate continuity and inverse-transpose invariance of the attached form, for every
continuous equivariant `T`. -/
theorem isSmoothHilbertTransposePairing_smoothDualTwistPairing (T : D →L[ℂ] Dθ)
    (hT : ∀ (g : GL) (y : D), T (representation 𝓜 R g y) =
      representation 𝓜 (inverseTransposeDualRepresentation F n R) g (T y)) :
    IsSmoothHilbertTransposePairing F n R (smoothDualTwistPairing F n R T) := by
  refine ⟨fun x => ?_, fun y => ?_, fun g y x => ?_⟩
  · exact (εθ (T x)).continuous.comp (ε).continuous
  · exact (ContinuousLinearMap.apply ℂ ℂ (ε y)).continuous.comp ((εθ).continuous.comp T.continuous)
  · rw [smoothDualTwistPairing_apply, smoothDualTwistPairing_apply, hT]
    change continuousDualRepresentation R (θ (θ g)) (εθ (T x)) (R g (ε y)) = εθ (T x) (ε y)
    rw [Langlands.GeneralLinear.inverseTranspose_involutive, continuousDualRepresentation_apply,
      ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]

omit [InnerProductSpace ℂ H] in
/-- The empty word, sending a genuine smooth vector to its value, is injective. -/
theorem derivativeCLM_nil_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R' : GL →* (E →L[ℂ] E)) :
    Function.Injective (derivativeCLM 𝓜 R' []) := by
  intro a b h
  apply (toSmooth 𝓜 R').injective
  apply Subtype.ext
  simpa only [derivativeCLM_apply, iteratedLieDerivative_nil] using h

/-- The genuine smooth vectors of a jointly continuous representation on a complete space
are norm dense. -/
theorem denseRange_derivativeCLM_nil {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (R' : GL →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R') :
    DenseRange (derivativeCLM 𝓜 R' []) := by
  let : MeasurableSpace GL := borel GL
  let : BorelSpace GL := ⟨rfl⟩
  let : LocallyCompactSpace GL := Units.isOpenEmbedding_val.locallyCompactSpace
  have h := dense_smoothVectors_units R' (Measure.haar : Measure GL) hR
  have hc : derivativeCLM 𝓜 R' [] = fun v => ((toSmooth 𝓜 R' v : smoothVectors 𝓜 R') : E) := by
    funext v
    simp only [derivativeCLM_apply, iteratedLieDerivative_nil]
  rw [hc]
  exact h.denseRange_val.comp (toSmooth 𝓜 R').surjective.denseRange continuous_subtype_val

/-- The attached form is nonzero as soon as `T` is nonzero. -/
theorem smoothDualTwistPairing_ne_zero [CompleteSpace H] (hR : IsContinuousRepresentation R)
    (T : D →L[ℂ] Dθ) (x : D) (hx : T x ≠ 0) : smoothDualTwistPairing F n R T ≠ 0 := by
  have hL : εθ (T x) ≠ 0 := fun h =>
    hx (derivativeCLM_nil_injective F n _ (h.trans (map_zero _).symm))
  have hy : ∃ y : D, εθ (T x) (ε y) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hL
    have he : (fun v : H => εθ (T x) v) = fun _ => (0 : ℂ) :=
      (denseRange_derivativeCLM_nil F n R hR).equalizer (εθ (T x)).continuous continuous_const
        (funext hcon)
    ext v
    exact congrFun he v
  obtain ⟨y, hy⟩ := hy
  intro hB
  apply hy
  rw [← smoothDualTwistPairing_apply, hB]
  rfl

end Pairing

/-- **Reduction.** The real smooth Hilbert inverse-transpose pairing follows from the
Casselman–Wallach extension statement, the Harish-Chandra module statement for
compact-finite smooth Hilbert vectors, and the inverse-transpose dual Harish-Chandra
intertwiner statement. -/
theorem realSmoothHilbertTransposePairing_of_casselmanWallach
    (hCW : RealSmoothCasselmanWallachExtensionStatement.{uH, uH, uH})
    (hHC : RealSmoothHilbertHarishChandraModuleStatement.{uH})
    (hD : RealSmoothHilbertDualHarishChandraStatement.{uH}) :
    RealSmoothHilbertTransposePairingStatement.{uH} := by
  intro r H _ _ _ R hR
  obtain ⟨ρ, π, hGK, hirr, hadm, hcompat⟩ := hHC r H R hR
  obtain ⟨f, hf0, hf⟩ := hD r H R ρ π hR hGK hirr hadm hcompat
  have hS := isContinuousRepresentation_inverseTransposeDual ℝ (r + 1) R hR.1
  obtain ⟨T, hT, hTf⟩ := hCW r (smoothHilbertKFinite ℝ (r + 1) R) ρ π H R (StrongDual ℂ H)
    (inverseTransposeDualRepresentation ℝ (r + 1) R) (LinearEquiv.refl ℂ _) f hirr hadm hR.1 hS
    hcompat hf
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hf0 (LinearMap.ext hcon)
  refine ⟨smoothDualTwistPairing ℝ (r + 1) R T,
    isSmoothHilbertTransposePairing_smoothDualTwistPairing ℝ (r + 1) R T hT,
    smoothDualTwistPairing_ne_zero ℝ (r + 1) R hR.1 T v ?_⟩
  have h : T (v : DerivativeSmoothVectors (matrixModel ℝ (r + 1)) R) = f v := hTf v
  rw [h]
  exact hv

end Langlands.Archimedean
