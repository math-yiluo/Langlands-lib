import Langlands.Representation.RankinSelberg.AdjacentRankJointShell
import Langlands.Representation.RankinSelberg.UnipotentQuotient

/-! The actual quotient shear and fixed-shell Fubini step in JPSS Section 6.3. -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G)

/-- Right translation of the actual left quotient is jointly continuous. -/
theorem continuous_rightTranslate_joint :
    Continuous (fun z : LeftQuotient H × G => rightTranslate H z.2 z.1) := by
  apply ((leftQuotient_isOpenQuotientMap H).prodMap
    (IsOpenQuotientMap.id (X := G))).isQuotientMap.continuous_iff.mpr
  change Continuous (fun z : G × G => leftQuotientMap H (z.1 * z.2))
  exact (leftQuotient_isOpenQuotientMap H).continuous.comp (continuous_fst.mul continuous_snd)

/-- The genuine quotient shear `(H g, h) ↦ (H (g h), h)`. -/
def rightQuotientShear : LeftQuotient H × G ≃ₜ LeftQuotient H × G where
  toFun z := (rightTranslate H z.2 z.1, z.2)
  invFun z := (rightTranslate H z.2⁻¹ z.1, z.2)
  left_inv := by
    rintro ⟨q, h⟩
    change (rightTranslate H h⁻¹ (rightTranslate H h q), h) = (q, h)
    rw [rightTranslate_mul, mul_inv_cancel, rightTranslate_one]
  right_inv := by
    rintro ⟨q, h⟩
    change (rightTranslate H h (rightTranslate H h⁻¹ q), h) = (q, h)
    rw [rightTranslate_mul, inv_mul_cancel, rightTranslate_one]
  continuous_toFun := (continuous_rightTranslate_joint H).prodMk continuous_snd
  continuous_invFun :=
    ((continuous_rightTranslate_joint H).comp
      (continuous_fst.prodMk continuous_snd.inv)).prodMk continuous_snd

@[simp] theorem rightQuotientShear_mk (g h : G) :
    rightQuotientShear H (Quotient.mk _ g, h) = (Quotient.mk _ (g * h), h) := rfl

@[simp] theorem rightQuotientShear_symm_mk (g h : G) :
    (rightQuotientShear H).symm (Quotient.mk _ g, h) =
      (Quotient.mk _ (g * h⁻¹), h) := rfl

section Measure

variable [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  [SecondCountableTopology G] [SecondCountableTopology (LeftQuotient H)]
  (ν : Measure (LeftQuotient H)) (η : Measure G) [SFinite ν] [SFinite η]
  (hinv : ∀ h : G, MeasurePreserving (rightTranslate H h) ν ν)

include hinv

omit [SecondCountableTopology G] in
/-- The quotient shear preserves the supplied product measure exactly.
No normalization of either measure occurs. -/
theorem measurePreserving_rightQuotientShear :
    MeasurePreserving (rightQuotientShear H) (ν.prod η) (ν.prod η) := by
  have hgm : Measurable (Function.uncurry
      fun (h : G) (q : LeftQuotient H) => rightTranslate H h q) :=
    ((continuous_rightTranslate_joint H).comp continuous_swap).measurable
  have hskew : MeasurePreserving
      (fun z : G × LeftQuotient H => (z.1, rightTranslate H z.1 z.2))
      (η.prod ν) (η.prod ν) :=
    (MeasurePreserving.id η).skew_product hgm
      (Filter.Eventually.of_forall fun h => (hinv h).map_eq)
  have hswap₁ : MeasurePreserving (Prod.swap : LeftQuotient H × G → G × LeftQuotient H)
      (ν.prod η) (η.prod ν) := Measure.measurePreserving_swap
  have hswap₂ : MeasurePreserving (Prod.swap : G × LeftQuotient H → LeftQuotient H × G)
      (η.prod ν) (ν.prod η) := Measure.measurePreserving_swap
  exact hswap₂.comp (hskew.comp hswap₁)

/-- Inverse shear also preserves the same product measure. -/
theorem measurePreserving_rightQuotientShear_symm :
    MeasurePreserving (rightQuotientShear H).symm (ν.prod η) (ν.prod η) :=
  MeasurePreserving.symm (rightQuotientShear H).toMeasurableEquiv
    (measurePreserving_rightQuotientShear H ν η hinv)

/-- Absolute convergence is equivalent before and after inverse shear. -/
theorem integrable_comp_rightQuotientShear_symm_iff
    (f : LeftQuotient H × G → ℂ) :
    Integrable (fun z => f ((rightQuotientShear H).symm z)) (ν.prod η) ↔
      Integrable f (ν.prod η) :=
  (measurePreserving_rightQuotientShear_symm H ν η hinv).integrable_comp_emb
    (rightQuotientShear H).symm.toMeasurableEquiv.measurableEmbedding

/-- The inverse shear introduces no scalar in the integral. -/
theorem integral_comp_rightQuotientShear_symm
    (f : LeftQuotient H × G → ℂ) :
    (∫ z, f ((rightQuotientShear H).symm z) ∂ν.prod η) =
      ∫ z, f z ∂ν.prod η :=
  (measurePreserving_rightQuotientShear_symm H ν η hinv).integral_comp
    (rightQuotientShear H).symm.toMeasurableEquiv.measurableEmbedding f

end Measure
end Langlands.QuotientIntegration

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance quotientShearFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance quotientShearValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance quotientShearLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance quotientShearFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance quotientShearGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance quotientShearGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance quotientShearUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := borel _
local instance quotientShearUnipotentBorel (r : ℕ) :
    BorelSpace (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance quotientShearQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
local instance quotientShearQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩
local instance quotientShearGroupSecondCountable (r : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (r + 1)
local instance quotientShearGroupSigmaCompact (r : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (r + 1)
local instance quotientShearQuotientSecondCountable (r : ℕ) :
    SecondCountableTopology (LeftUnipotentQuotient r F.Carrier) :=
  TopologicalSpace.Quotient.secondCountableTopology
    (leftQuotient_isOpenQuotientMap
      (GeneralLinear.upperUnipotent (r + 1) F.Carrier)).isOpenMap
local instance quotientShearQuotientLocallyCompact (r : ℕ) :
    LocallyCompactSpace (LeftUnipotentQuotient r F.Carrier) :=
  leftQuotient_locallyCompactSpace _

/-- The genuine kernel before the change `g ↦ g h`, defined by inverse shear. -/
def adjacentRankBeforeShearKernel {r : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (a : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (m : ℤ) :
    LeftUnipotentQuotient r F.Carrier × Langlands.GeneralLinear (r + 1) F.Carrier → ℂ :=
  adjacentRankJointShellKernel F ψ W W' Φ φ a m ∘
    (rightQuotientShear (GeneralLinear.upperUnipotent (r + 1) F.Carrier)).symm

@[simp] theorem adjacentRankBeforeShearKernel_mk {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (a : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (m : ℤ)
    (g h : Langlands.GeneralLinear (r + 1) F.Carrier) :
    adjacentRankBeforeShearKernel F ψ W W' Φ φ a m (Quotient.mk _ g, h) =
      if F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) = m
      then W.val (g * h⁻¹) * W'.val g * φ (lastRow (g * h⁻¹)) * Φ h.val * a h
      else 0 := by
  simp only [adjacentRankBeforeShearKernel, Function.comp_apply,
    rightQuotientShear_symm_mk, adjacentRankJointShellKernel_mk, inv_mul_cancel_right]
  rw [map_mul, Units.val_mul,
    F.canonicalTopologicalData.ord_mul
      (GeneralLinear.determinant g).ne_zero (GeneralLinear.determinant h⁻¹).ne_zero,
    map_inv, Units.val_inv_eq_inv_val, F.canonicalTopologicalData.ord_inv]
  simp only [add_assoc, neg_add_cancel, add_zero]

/-- Absolute convergence of both kernels, both iterated integrals and their
exact equality for every supplied compatible quotient measure. -/
theorem adjacentRankShell_shear_fubini {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (W' : InverseWhittakerFunctions ψ r) (hW' : Continuous W'.val)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (a : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (ha : Continuous a) (m : ℤ)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (GeneralLinear.upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν) :
    let η := generalLinearHaar F.Carrier r
    let before := adjacentRankBeforeShearKernel F ψ W.val W' Φ φ a m
    let after := adjacentRankJointShellKernel F ψ W.val W' Φ φ a m
    Integrable before (ν.prod η) ∧ Integrable after (ν.prod η) ∧
      Integrable (fun q => ∫ h, before (q, h) ∂η) ν ∧
      Integrable (fun q => ∫ h, after (q, h) ∂η) ν ∧
      Integrable (fun h => ∫ q, after (q, h) ∂ν) η ∧
      (∫ q, ∫ h, before (q, h) ∂η ∂ν) = ∫ q, ∫ h, after (q, h) ∂η ∂ν ∧
      (∫ q, ∫ h, after (q, h) ∂η ∂ν) = ∫ h, ∫ q, after (q, h) ∂ν ∂η := by
  dsimp only
  let := hν.regular
  have hi := integrable_adjacentRankJointShellKernel F ψ σ hσ ℓ W W' hW'
    Φ φ a ha m ν (generalLinearHaar F.Carrier r)
  have hb : Integrable (adjacentRankBeforeShearKernel F ψ W.val W' Φ φ a m)
      (ν.prod (generalLinearHaar F.Carrier r)) :=
    (integrable_comp_rightQuotientShear_symm_iff _ ν
      (generalLinearHaar F.Carrier r) hν.right_invariant _).mpr hi
  refine ⟨hb, hi, hb.integral_prod_left, hi.integral_prod_left, hi.integral_prod_right, ?_, ?_⟩
  · rw [← integral_prod _ hb, ← integral_prod _ hi]
    exact integral_comp_rightQuotientShear_symm _ ν
      (generalLinearHaar F.Carrier r) hν.right_invariant _
  · rw [← integral_prod _ hi, ← integral_prod_symm _ hi]

end Langlands.RankinSelberg.Padic
