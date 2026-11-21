import Langlands.Global.RankinSelberg.ComplexLocalAnalyticRightJet
import Langlands.Global.RankinSelberg.ComplexLocalCompactDerivatives
import Langlands.Global.RankinSelberg.ComplexLocalCompactProjectionCoordinates
import Langlands.Representation.Archimedean.ComplexDuality.UnitaryHaar

/-! # Compatibility of the complex Whittaker map with compact averaging -/

noncomputable section

open MeasureTheory
open Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean
open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

variable {r : ℕ}

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "I" => matrixModel ℂ n
local notation "E[" ds "]" => complexStandardKFinite n ds
local notation "R" => rightDerivative I

private def standardDerivative (ds : List ComplexCharacterData) (Y : M) : E[ds] →ₗ[ℂ] E[ds] :=
  complexStandardLie n ds (1 ⊗ₜ[ℝ] Y)

private def restrictCompact (ds : List ComplexCharacterData) : E[ds] →ₗ[ℂ] (Kc → ℂ) where
  toFun f k := (f : G → ℂ) k.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem restrictCompact_injective (ds : List ComplexCharacterData) :
    Function.Injective (restrictCompact (r := r) ds) := by
  intro f g h
  apply Subtype.ext
  exact ComplexPrincipalSeriesExtension.eq_of_eqOn_unitary f.2.1 g.2.1
    (fun k hk => congrFun h ⟨k, hk⟩)

private theorem smooth_standardVector {ds : List ComplexCharacterData} (f : E[ds]) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (f : G → ℂ) :=
  ((mem_principalSeries_iff ℂ n (complexPositionCharacter ds) _).mp f.2.1).1

private def compactAverageMap {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ν : Measure Kc) [IsFiniteMeasure ν] (κ : C(Kc, ℂ)) (j : C(Kc, G))
    (L : V →ₗ[ℂ] (G → ℂ)) (hL : ∀ f, Continuous (L f)) :
    V →ₗ[ℂ] (G → ℂ) where
  toFun f := complexCompactAverage ν κ j (L f)
  map_add' a b := by
    funext g
    have hi (f : V) : Integrable (fun k => κ k * L f (j k * g)) ν :=
      (κ.continuous.mul ((hL f).comp (j.continuous.mul continuous_const))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    simp only [complexCompactAverage, map_add, Pi.add_apply, mul_add, integral_add (hi a) (hi b)]
  map_smul' c a := by
    funext g
    simp only [complexCompactAverage, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp only [mul_left_comm (κ _), integral_const_mul]

private theorem compactProjection_whittaker_at_one
    {ds : List ComplexCharacterData} {a : ℂˣ}
    (ν : Measure Kc) [IsFiniteMeasure ν] (κ : C(Kc, ℂ))
    (B : E[ds] →ₗ[ℂ] (G → ℂ)) (hB : IsComplexWhittakerIntertwiner r ds a B)
    (f p : E[ds])
    (hp : ∀ k : Kc, (p : G → ℂ) k.val = ∫ l, κ l * (f : G → ℂ) (k.val * l.val) ∂ν)
    (x : G) :
    B p x = ∫ k, κ k * B f (x * k.val) ∂ν := by
  let kU (k : Kc) : Matrix.unitaryGroup (Fin n) ℂ := ⟨k.val.val, k.2⟩
  let orbit (k : Kc) := complexStandardRep n ds (kU k) f
  have hOrbit (k : Kc) : (orbit k : G → ℂ) =
      Whittaker.rightTranslation ℂ G k.val f := by
    have hk : Unitary.toUnits (kU k) = k.val := Units.ext rfl
    rw [show (orbit k : G → ℂ) = (complexStandardRep n ds (kU k) f : G → ℂ) from rfl,
      principalSeriesRep_apply_coe, hk]
  let V := FiniteVectors.orbitSpan (complexStandardRep n ds) f
  let : Module.Finite ℂ V := (isComplexGKModule_complexStandardModule n ds).1 f
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range orbit)) := by
    apply Submodule.finiteDimensional_of_le (S₂ := V)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact FiniteVectors.action_mem_orbitSpan (complexStandardRep n ds) (kU k) f
  let ρ := restrictCompact (r := r) ds
  have hcont (u : Kc) : Continuous fun k => ρ (orbit k) u := by
    have heq : (fun k => ρ (orbit k) u) = fun k : Kc => (f : G → ℂ) (u.val * k.val) := by
      funext k
      change (orbit k : G → ℂ) u.val = _
      rw [hOrbit]
      rfl
    rw [heq]
    exact (smooth_standardVector f).continuous.comp (continuous_const.mul continuous_subtype_val)
  obtain ⟨p', hp'⟩ := exists_compact_average_vector ν κ κ.continuous ρ
    (restrictCompact_injective ds) orbit hfin hcont
  have hpeq : p = p' := by
    apply restrictCompact_injective (r := r) ds
    funext u
    have he := hp' ((LinearMap.proj u).comp ρ)
    change (p' : G → ℂ) u.val = ∫ k, κ k * (orbit k : G → ℂ) u.val ∂ν at he
    change (p : G → ℂ) u.val = (p' : G → ℂ) u.val
    rw [hp, he]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun k => ?_
    change κ k * (f : G → ℂ) (u.val * k.val) = κ k * (orbit k : G → ℂ) u.val
    rw [hOrbit]
    rfl
  rw [hpeq]
  have h := hp' ((LinearMap.proj x).comp B)
  change B p' x = ∫ k, κ k * B (orbit k) x ∂ν at h
  rw [h]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun k => ?_
  change κ k * B (orbit k) x = κ k * B f (x * k.val)
  rw [hB.2.2.2.1 k f (orbit k) (hOrbit k)]
  rfl

variable (r) in
/-- Real analyticity of smooth standard Lie intertwiners and connectedness
of the unit domain imply the Whittaker compatibility of compact projection. -/
def ComplexLocalCompactWhittakerAveragingStatement : Prop :=
  IsPreconnected {Y : M | IsUnit Y} →
  (∀ (ds : List ComplexCharacterData) (A : E[ds] →ₗ[ℂ] (G → ℂ)),
    (∀ f, ContMDiff I 𝓘(ℝ, ℂ) ∞ (A f)) →
    (∀ Y f, A (complexStandardLie n ds (1 ⊗ₜ[ℝ] Y) f) = R Y (A f)) →
    ∀ f, AnalyticOnNhd ℝ (unitsExtension (A f)) {Y : M | IsUnit Y}) →
  ∀ (ds : List ComplexCharacterData) (a : ℂˣ) (ν : Measure Kc), ν.IsHaarMeasure →
  ∀ (κ : C(Kc, ℂ)), HasFiniteCompactConvolutionKernel κ →
  ∀ (B : E[ds] →ₗ[ℂ] (G → ℂ)), IsComplexWhittakerIntertwiner r ds a B →
  ∀ (p : E[ds] → G → E[ds]),
    (∀ f g (k : Kc), (p f g : G → ℂ) k.val = ∫ l, κ l * (f : G → ℂ) (k.val * l.val * g) ∂ν) →
    ∀ f g x, B (p f g) x = ∫ k, κ k * B f (x * k.val * g) ∂ν

theorem complexLocalCompactWhittakerAveraging : ComplexLocalCompactWhittakerAveragingStatement r := by
  intro hConn hAn ds a ν hν κ hκ B hB p hp f g x
  let : ν.IsHaarMeasure := hν
  let ρ := restrictCompact (r := r) ds
  let ℓ := (LinearMap.proj x).comp B
  have hcontinuous (v : E[ds]) (y : G) : Continuous fun k : Kc => (v : G → ℂ) (k.val * y) :=
    (smooth_standardVector v).continuous.comp (continuous_subtype_val.mul continuous_const)
  obtain ⟨wgt, hwgt, hCoord⟩ := exists_compact_projection_weight ν (unitaryCompact ℂ n).subtype κ
    κ.continuous hκ ρ (restrictCompact_injective ds) (fun v => (v : G → ℂ)) hcontinuous p hp ℓ
  let wx : C(Kc, ℂ) := ⟨wgt, hwgt⟩
  let jx : C(Kc, G) := ⟨fun k => x * k.val, continuous_const.mul continuous_subtype_val⟩
  let j₁ : C(Kc, G) := ⟨Subtype.val, continuous_subtype_val⟩
  let S : E[ds] →ₗ[ℂ] (G → ℂ) := (E[ds]).subtype
  let L := compactAverageMap ν κ jx B (fun v => (hB.2.1 v).continuous)
  let T := compactAverageMap ν wx j₁ S (fun v => (smooth_standardVector v).continuous)
  let A := L - T
  have hL (v : E[ds]) := complexLocalCompactDerivatives Kc ν κ jx (B v) (hB.2.1 v)
  have hT (v : E[ds]) := complexLocalCompactDerivatives Kc ν wx j₁ (S v) (smooth_standardVector v)
  have hSm (v : E[ds]) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (A v) := (hL v).1.sub (hT v).1
  have hDiff (Y : M) (v : E[ds]) : R Y (A v) = A (standardDerivative ds Y v) := by
    let w := standardDerivative ds Y v
    have hStd : S w = R Y (S v) :=
      principalSeriesLie_one_tmul_apply_coe ℂ n _ Y v
    have hBw : B w = R Y (B v) := hB.2.2.2.2 Y v w hStd
    have hl : R Y (L v) = L w := by
      change R Y (complexCompactAverage ν κ jx (B v)) = complexCompactAverage ν κ jx (B w)
      rw [(hL v).2 Y, hBw]
    have ht : R Y (T v) = T w := by
      change R Y (complexCompactAverage ν wx j₁ (S v)) = complexCompactAverage ν wx j₁ (S w)
      rw [(hT v).2 Y, hStd]
    have hLv : ContMDiff I 𝓘(ℝ, ℂ) ∞ (L v) := (hL v).1
    have hTv : ContMDiff I 𝓘(ℝ, ℂ) ∞ (T v) := (hT v).1
    have hneg : ContMDiff I 𝓘(ℝ, ℂ) ∞ ((-1 : ℂ) • T v) :=
      (((-1 : ℂ) • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hTv
    change R Y (L v - T v) = L w - T w
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (T v),
      rightDerivative_add hLv hneg, rightDerivative_smul hTv, hl, ht, neg_one_smul, ← sub_eq_add_neg]
  have hCoord' (v : E[ds]) (y : G) : T v y = B (p v y) x := (hCoord v y).symm
  have h0 (v : E[ds]) : A v 1 = 0 := by
    change L v 1 - T v 1 = 0
    rw [hCoord']
    apply sub_eq_zero.mpr
    have hv := compactProjection_whittaker_at_one ν κ B hB v (p v 1)
      (fun k => by simpa only [mul_one] using hp v 1 k) x
    change (∫ k, κ k * B v (x * k.val * 1) ∂ν) = _
    simpa only [mul_one] using hv.symm
  have hAz := complexLocalAnalyticRightJet hConn E[ds] A (fun Y v => standardDerivative ds Y v) 1
    hSm (hAn ds A hSm fun Y v => (hDiff Y v).symm) hDiff h0 f g
  change L f g - T f g = 0 at hAz
  rw [← hCoord']
  exact (sub_eq_zero.mp hAz).symm

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
