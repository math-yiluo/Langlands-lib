import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Global.RankinSelberg.RealIwasawa
import Langlands.Analysis.Local.QuotientAutomorphismProof

/-! # The real Weil integral formula for absolutely integrable functions -/

noncomputable section

open Langlands.GeneralLinear Langlands.QuotientIntegration
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.Global.RankinSelbergGlobal.RealIwasawa
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Matrix.Norms.Operator CompactlySupported

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

private local instance (t : ℕ) : MeasurableSpace (Langlands.GeneralLinear (t + 1) ℝ) := borel _
private local instance (t : ℕ) : BorelSpace (Langlands.GeneralLinear (t + 1) ℝ) := ⟨rfl⟩
private local instance (t : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (t + 1) ℝ) := borel _
private local instance (t : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (t + 1) ℝ) := ⟨rfl⟩
private local instance (t : ℕ) : MeasurableSpace (LeftUnipotentQuotient t ℝ) := borel _
private local instance (t : ℕ) : BorelSpace (LeftUnipotentQuotient t ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "N" => GeneralLinear.upperUnipotent (t + 1) ℝ
local notation "Q" => LeftUnipotentQuotient t ℝ

/-- The canonical real Iwasawa representative, obtained by removing the left
unipotent coordinate. -/
def quotientRepresentative (t : ℕ) : LeftUnipotentQuotient t ℝ → Langlands.GeneralLinear (t + 1) ℝ :=
  descend (GeneralLinear.upperUnipotent (t + 1) ℝ) (fun g => (npart g).val⁻¹ * g) <| by
    intro u g
    rw [npart_unipotent_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left]

@[simp] theorem quotientRepresentative_mk (g : G) :
    quotientRepresentative t (Quotient.mk _ g) = (npart g).val⁻¹ * g := rfl

private theorem continuous_quotientRepresentative : Continuous (quotientRepresentative t) := by
  unfold quotientRepresentative descend
  exact ((continuous_subtype_val.comp continuous_npart).inv.mul continuous_id).quotient_lift _

private theorem quotientRepresentative_npart (q : Q) : npart (quotientRepresentative t q) = 1 := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [quotientRepresentative_mk, ← Subgroup.coe_inv, npart_unipotent_mul, inv_mul_cancel]

private theorem quotientRepresentative_class (q : Q) : Quotient.mk _ (quotientRepresentative t q) = q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [quotientRepresentative_mk]
    apply Quotient.sound
    change QuotientGroup.rightRel N ((npart g).val⁻¹ * g) g
    rw [QuotientGroup.rightRel_apply, mul_inv_rev, inv_inv, mul_inv_cancel_left]
    exact (npart g).property

/-- The product of the upper unipotent group and its real quotient parametrizes
the group, with inverse given by the unipotent coordinate and quotient class. -/
def unipotentQuotientHomeomorph (t : ℕ) :
    (GeneralLinear.upperUnipotent (t + 1) ℝ × LeftUnipotentQuotient t ℝ) ≃ₜ
      Langlands.GeneralLinear (t + 1) ℝ where
  toFun p := p.1.val * quotientRepresentative t p.2
  invFun g := (npart g, Quotient.mk _ g)
  left_inv p := by
    rcases p with ⟨u, q⟩
    apply Prod.ext
    · change npart (u.val * quotientRepresentative t q) = u
      rw [npart_unipotent_mul, quotientRepresentative_npart, mul_one]
    · change Quotient.mk _ (u.val * quotientRepresentative t q) = q
      refine Eq.trans ?_ (quotientRepresentative_class q)
      apply Quotient.sound
      change QuotientGroup.rightRel (GeneralLinear.upperUnipotent (t + 1) ℝ)
        (u.val * quotientRepresentative t q) (quotientRepresentative t q)
      rw [QuotientGroup.rightRel_apply, mul_inv_rev, mul_inv_cancel_left]
      exact (u⁻¹ : GeneralLinear.upperUnipotent (t + 1) ℝ).property
  right_inv g := by
    change (npart g).val * quotientRepresentative t (Quotient.mk _ g) = g
    rw [quotientRepresentative_mk, mul_inv_cancel_left]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul
    (continuous_quotientRepresentative.comp continuous_snd)
  continuous_invFun := continuous_npart.prodMk continuous_quotient_mk'

/-- The actual compatible quotient measure and subgroup Haar give the ambient
Haar measure under the real Iwasawa product homeomorphism. -/
theorem measurePreserving_unipotentQuotient (D : RealQuotientMeasureData t) :
    MeasurePreserving (unipotentQuotientHomeomorph t)
      (D.unipotentHaar.prod D.measure) D.groupHaar := by
  have hN : IsClosed (N : Set G) := UpperUnipotent.isClosed
  let _ : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (t + 1) → ℝ))
  let _ : LocallyCompactSpace G := Units.isOpenEmbedding_val.locallyCompactSpace
  let _ : SecondCountableTopology G := Units.isOpenEmbedding_val.isInducing.secondCountableTopology
  let _ : PseudoMetrizableSpace G := Units.isOpenEmbedding_val.isInducing.pseudoMetrizableSpace
  let _ : LocallyCompactSpace N := hN.locallyCompactSpace
  let _ : SigmaCompactSpace N := hN.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  let _ : LocallyCompactSpace Q := leftQuotient_locallyCompactSpace N
  let _ : T2Space Q := leftQuotient_t2Space N hN
  let _ : SigmaCompactSpace Q := by
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr (Quotient.mk_surjective (s := QuotientGroup.rightRel N))]
    exact isSigmaCompact_range continuous_quotient_mk'
  let := D.groupHaar_isHaar
  let := D.unipotentHaar_isHaar
  let := D.unipotentHaar_rightInvariant
  let := D.compatible.regular
  let _ : D.groupHaar.Regular := Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure D.groupHaar
  let e := unipotentQuotientHomeomorph t
  let μ := D.unipotentHaar.prod D.measure
  let _ : IsFiniteMeasureOnCompacts μ := inferInstanceAs
    (IsFiniteMeasureOnCompacts (D.unipotentHaar.prod D.measure))
  let _ : IsFiniteMeasureOnCompacts (μ.map e) := IsFiniteMeasureOnCompacts.map μ e
  let _ : (μ.map e).Regular := Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (μ.map e)
  refine ⟨e.continuous.measurable, ?_⟩
  change μ.map e = D.groupHaar
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let F : N × Q → ℝ := f ∘ e
  have hF : Integrable F μ := (f.continuous.comp e.continuous).integrable_of_hasCompactSupport
    (f.hasCompactSupport.comp_homeomorph e)
  have hOrbit (q : Q) : (∫ u : N, F (u, q) ∂D.unipotentHaar) =
      quotientAverageReal N D.unipotentHaar f q := by
    conv_rhs => rw [← quotientRepresentative_class q]
    rw [quotientAverageReal_mk]
    rfl
  calc
    _ = ∫ p, F p ∂μ := integral_map_equiv e.toMeasurableEquiv f
    _ = ∫ q, ∫ u, F (u, q) ∂D.unipotentHaar ∂D.measure := integral_prod_symm _ hF
    _ = ∫ q, quotientAverageReal N D.unipotentHaar f q ∂D.measure :=
      integral_congr_ae (Filter.Eventually.of_forall hOrbit)
    _ = _ := D.compatible.integral_quotientAverageReal f f.continuous f.hasCompactSupport

/-- The compatible real Weil formula for every integrable complex-valued
function, including absolute integrability of almost all subgroup fibers. -/
def RealGodementWeilStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (f : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    Integrable f D.groupHaar →
    let H := GeneralLinear.upperUnipotent (t + 1) ℝ
    letI := D.unipotentHaar_rightInvariant
    (∀ᵐ q : LeftUnipotentQuotient t ℝ ∂D.measure,
      ∀ g : Langlands.GeneralLinear (t + 1) ℝ, Quotient.mk (QuotientGroup.rightRel H) g = q →
        Integrable (fun u : H => f (u.val * g)) D.unipotentHaar) ∧
      Integrable (quotientAverage H D.unipotentHaar f) D.measure ∧
      (∫ q, quotientAverage H D.unipotentHaar f q ∂D.measure) = ∫ g, f g ∂D.groupHaar

theorem realGodementWeil : RealGodementWeilStatement := by
  intro t D f hf H
  let _ : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (t + 1) → ℝ))
  let _ : LocallyCompactSpace (Langlands.GeneralLinear (t + 1) ℝ) :=
    Units.isOpenEmbedding_val.locallyCompactSpace
  let _ : SecondCountableTopology (Langlands.GeneralLinear (t + 1) ℝ) :=
    Units.isOpenEmbedding_val.isInducing.secondCountableTopology
  have hH : IsClosed (H : Set (Langlands.GeneralLinear (t + 1) ℝ)) := UpperUnipotent.isClosed
  let _ : SigmaCompactSpace H := hH.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  let _ : SigmaCompactSpace (LeftUnipotentQuotient t ℝ) := by
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr (Quotient.mk_surjective (s := QuotientGroup.rightRel H))]
    exact isSigmaCompact_range continuous_quotient_mk'
  let := D.unipotentHaar_isHaar
  let := D.unipotentHaar_rightInvariant
  let := D.compatible.regular
  let e := unipotentQuotientHomeomorph t
  have hmp := measurePreserving_unipotentQuotient D
  have hF : Integrable (f ∘ e) (D.unipotentHaar.prod D.measure) :=
    hmp.integrable_comp_of_integrable hf
  have hOrbit (q : LeftUnipotentQuotient t ℝ) :
      (∫ u : H, f (e (u, q)) ∂D.unipotentHaar) = quotientAverage H D.unipotentHaar f q := by
    conv_rhs => rw [← quotientRepresentative_class q]
    rw [quotientAverage_mk]
    rfl
  refine ⟨?_, hF.integral_prod_right.congr (Filter.Eventually.of_forall hOrbit), ?_⟩
  · filter_upwards [hF.prod_left_ae] with q hq
    intro g hg
    have h' := (measurePreserving_mul_right D.unipotentHaar (npart g)).integrable_comp_of_integrable hq
    rw [← hg] at h'
    refine h'.congr (Filter.Eventually.of_forall fun u => ?_)
    change f ((u * npart g).val * quotientRepresentative t (Quotient.mk _ g)) = f (u.val * g)
    rw [quotientRepresentative_mk, Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left]
  · calc
      _ = ∫ q, ∫ u, f (e (u, q)) ∂D.unipotentHaar ∂D.measure :=
        integral_congr_ae (Filter.Eventually.of_forall fun q => (hOrbit q).symm)
      _ = ∫ p, f (e p) ∂D.unipotentHaar.prod D.measure := (integral_prod_symm _ hF).symm
      _ = _ := hmp.integral_comp e.toMeasurableEquiv.measurableEmbedding f

end Langlands.Global.RankinSelbergGlobal.RealGodement
