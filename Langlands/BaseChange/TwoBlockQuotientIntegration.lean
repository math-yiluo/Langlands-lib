import Langlands.Analysis.Local.QuotientPositiveLifting
import Langlands.BaseChange.OrbitalIntegral
import Langlands.BaseChange.TwoBlockLeviQuotient
import Langlands.Group.GL.ParabolicQuotient
import Langlands.Representation.Unramified.TwoBlockSphericalIntegration

/-! Two-block parabolic integration on the actual compatible left quotients. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure _root_.Topology Langlands.GeneralLinear
open Langlands.GodementJacquet.TwoBlock Langlands.RankinSelberg Langlands.RankinSelberg.TwoBlockJacquet
open Langlands.QuotientIntegration Langlands.Unramified
open scoped NNReal

universe u

private theorem exists_compact_quotientLift {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) [MeasurableSpace H] [BorelSpace H]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular] [μH.IsMulRightInvariant]
    (f : LeftQuotient H → ℂ) (hf : Continuous f) (hf₀ : HasCompactSupport f) :
    ∃ ψ : G → ℂ, Continuous ψ ∧ HasCompactSupport ψ ∧ quotientAverage H μH ψ = f := by
  obtain ⟨b, _, hb⟩ := realQuotientCompactNormalization H hH μH (tsupport f) hf₀
  let ψ : G → ℂ := fun g => f (leftQuotientMap H g) * (b g : ℂ)
  refine ⟨ψ, (hf.comp continuous_quotient_mk').mul (Complex.continuous_ofReal.comp b.continuous),
    (b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_left, ?_⟩
  funext q
  rw [quotientAverage_pullback_mul, quotientAverage_ofReal]
  by_cases hq : q ∈ tsupport f
  · induction q using Quotient.inductionOn with
    | h g => rw [quotientAverageReal_mk, hb g hq, Complex.ofReal_one, mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel
attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

local instance twoBlockQuotientFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance twoBlockQuotientFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance twoBlockQuotientFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance twoBlockQuotientFieldSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance twoBlockQuotientGlLocallyCompact (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier n
local instance twoBlockQuotientGlSecondCountable (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_secondCountableTopology F.Carrier n
local instance twoBlockQuotientGlSigmaCompact (n : ℕ) : SigmaCompactSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_sigmaCompactSpace F.Carrier n
local instance twoBlockQuotientRectSigmaCompact (a b : ℕ) :
    SigmaCompactSpace (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (SigmaCompactSpace (Fin a → Fin b → F.Carrier))

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local notation "B" => succBlockShape m h
local notation "M" => BlockShape.Levi B F.Carrier
local notation "G" => GeneralLinear (t + 1) F.Carrier
local notation "Rect" => Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier
local notation "K" => sphericalOpenSubgroup F t
local notation "μG" => sphericalHaar F t
local notation "μM" => Measure.pi (fun i : Fin 2 => generalLinearHaar F.Carrier (m i))

private theorem isClosedEmbedding_parabolicPoint :
    IsClosedEmbedding (parabolicPoint (R := F.Carrier) h) := by
  let e : M × Rect ≃ₜ (B).parabolic F.Carrier :=
    { toFun := fun z => ⟨parabolicPoint h z, parabolicPoint_mem h z⟩
      invFun := parabolicCoord h
      left_inv := parabolicCoord_parabolicPoint h
      right_inv := fun g => Subtype.ext (parabolicPoint_parabolicCoord h g)
      continuous_toFun := (continuous_parabolicPoint h F.Carrier).subtype_mk _
      continuous_invFun := continuous_parabolicCoord h F.Carrier }
  exact ((B).isClosed_parabolic F.Carrier).isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding

set_option maxHeartbeats 2000000 in
/-- Parabolic integration on the left quotient with the exact relative subgroup
Haar scalar. Both quotient measures use the ambient volume-one spherical normalization. -/
theorem integral_twoBlock_leviRadicalQuotientPoint
    (A : Subgroup M) (H : Subgroup G) (e : A ≃ₜ* H)
    (he : ∀ a : A, (e a).val = (B).leviEmbedding F.Carrier a.val)
    (hA : IsClosed (A : Set M)) (hH : IsClosed (H : Set G))
    (μA : Measure A) [μA.IsMulRightInvariant] (μH : Measure H) [μH.IsHaarMeasure]
    [μH.IsMulRightInvariant] (c : ℝ≥0) (hc : c ≠ 0) (hscale : μH = c • Measure.map e μA)
    (νA : Measure (LeftQuotient A)) (νH : Measure (LeftQuotient H))
    (hνA : IsCompatible A μM μA νA) (hνH : IsCompatible H μG μH νH)
    (dx : Measure Rect) [dx.IsAddHaarMeasure]
    (hdx : dx {x | ∀ i j, x i j ∈ (ValuativeRel.valuation F.Carrier).integer} = 1)
    (f : LeftQuotient H → ℂ) (hf : Continuous f) (hf₀ : HasCompactSupport f)
    (hInv : ∀ q (k : K), f (rightTranslate H k.val q) = f q) :
    (∫ q, f q ∂νH) = ((c : ℝ) : ℂ)⁻¹ *
      ∫ q, ∫ x, f (leviRadicalQuotientPoint h A H e he (q, x)) ∂dx ∂νA := by
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : SecondCountableTopology H := IsEmbedding.subtypeVal.secondCountableTopology
  let : μH.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μH
  let : LocallyCompactSpace (LeftQuotient A) := leftQuotient_locallyCompactSpace A
  let : SecondCountableTopology (LeftQuotient A) :=
    (leftQuotient_isOpenQuotientMap A).secondCountableTopology
  let : νA.Regular := hνA.regular
  obtain ⟨ψ, hψ, hψ₀, hLift⟩ := exists_compact_quotientLift H hH μH f hf hf₀
  let cℂ : ℂ := (c : ℝ)
  have hcℂ : cℂ ≠ 0 := by
    change ((c : ℝ) : ℂ) ≠ 0
    exact_mod_cast hc
  have hPK (g : G) : ∃ (q : (B).parabolic F.Carrier) (k : K), g = q.val * k.val := by
    obtain ⟨q, k, hk, heq⟩ := SphericalProduct.exists_parabolic_mul_spherical F B g
    exact ⟨q, ⟨k, hk⟩, heq⟩
  have hInt := integral_parabolic F h dx K (sphericalOpenSubgroup_isCompact F t) hPK
    (hψ.integrable_of_hasCompactSupport hψ₀ (μ := generalLinearHaar F.Carrier t))
  rw [← sphericalHaar_eq_generalLinearHaar, parabolicMeasure_preimage_spherical F h dx hdx,
    ENNReal.toReal_one, one_smul] at hInt
  let fP : LeftQuotient A × Rect → ℂ := f ∘ leviRadicalQuotientPoint h A H e he
  have hfc : Continuous fP := hf.comp (continuous_leviRadicalQuotientPoint h A H e he)
  have hfs : HasCompactSupport fP :=
    hasCompactSupport_comp_leviRadicalQuotientPoint h A H e he hH hA hf₀
  have hfi := hfc.integrable_of_hasCompactSupport hfs (μ := νA.prod dx)
  have hSlice (x : Rect) (k : G) (hk : k ∈ K) :
      (∫ L, ψ (parabolicPoint h (L, x) * k) ∂μM) =
        ∫ q, cℂ⁻¹ * fP (q, x) ∂νA := by
    let ψx : M → ℂ := fun L => ψ (parabolicPoint h (L, x) * k)
    have hMap : IsClosedEmbedding (fun L : M => parabolicPoint h (L, x) * k) := by
      have hEmb := ((B).isClosed_leviSubgroup F.Carrier).isClosedEmbedding_subtypeVal.comp
        ((B).leviEquivContinuous F.Carrier).toHomeomorph.isClosedEmbedding
      have hRight := (Homeomorph.mulRight (upperRadical h F.Carrier x * k)).isClosedEmbedding.comp hEmb
      change IsClosedEmbedding (fun L : M => (B).leviEmbedding F.Carrier L *
        (upperRadical h F.Carrier x * k)) at hRight
      simpa only [parabolicPoint, mul_assoc] using hRight
    change (∫ L, ψx L ∂μM) = _
    rw [← hνA.integral_formula ψx (hψ.comp hMap.continuous) (hψ₀.comp_isClosedEmbedding hMap)]
    apply integral_congr_ae (ae_of_all _ _)
    intro q
    induction q using Quotient.inductionOn with
    | h L =>
      let g := parabolicPoint h (L, x) * k
      have hFiber : (∫ b : H, ψ (b.val * g) ∂μH) = cℂ *
          ∫ a : A, ψ (parabolicPoint h (a.val * L, x) * k) ∂μA := by
        rw [hscale, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
        congr 1
        change (∫ b : H, ψ (b.val * g) ∂Measure.map e.toHomeomorph.toMeasurableEquiv μA) = _
        rw [integral_map_equiv]
        apply integral_congr_ae (ae_of_all _ _)
        intro a
        rw [parabolicPoint_left_levi, ← he a]
        exact congrArg ψ (mul_assoc _ _ _).symm
      have hfg := congrFun hLift (leftQuotientMap H g)
      change (∫ b : H, ψ (b.val * g) ∂μH) = f (leftQuotientMap H g) at hfg
      rw [hFiber] at hfg
      change (∫ a : A, ψ (parabolicPoint h (a.val * L, x) * k) ∂μA) =
        cℂ⁻¹ * f (leftQuotientMap H (parabolicPoint h (L, x)))
      rw [← hInv _ ⟨k, hk⟩]
      change _ = cℂ⁻¹ * f (leftQuotientMap H g)
      rw [← hfg, ← mul_assoc, inv_mul_cancel₀ hcℂ, one_mul]
  have hK : Set.EqOn
      (fun k : G => ∫ z, ψ (parabolicPoint h z * k) ∂parabolicMeasure F h dx)
      (fun _ => cℂ⁻¹ * ∫ q, ∫ x, fP (q, x) ∂dx ∂νA) K := by
    intro k hk
    have hEmb : IsClosedEmbedding (fun z : M × Rect => parabolicPoint h z * k) :=
      (Homeomorph.mulRight k).isClosedEmbedding.comp (isClosedEmbedding_parabolicPoint F h)
    have hψi : Integrable (fun z : M × Rect => ψ (parabolicPoint h z * k)) ((μM).prod dx) :=
      (hψ.comp hEmb.continuous).integrable_of_hasCompactSupport (hψ₀.comp_isClosedEmbedding hEmb)
    change (∫ z : M × Rect, ψ (parabolicPoint h z * k) ∂((μM).prod dx)) =
      cℂ⁻¹ * ∫ q, ∫ x, fP (q, x) ∂dx ∂νA
    rw [integral_prod_symm _ hψi]
    simp_rw [hSlice _ k hk, integral_const_mul]
    rw [← integral_prod_symm _ hfi, integral_prod _ hfi]
  rw [setIntegral_congr_fun (K).isOpen.measurableSet hK, setIntegral_const,
    sphericalHaar_real_self, one_smul] at hInt
  calc
    _ = ∫ g, ψ g ∂μG := by
      rw [← hLift, hνH.integral_formula ψ hψ hψ₀]
    _ = _ := hInt.symm

end Langlands.BaseChange
