import Langlands.Representation.Archimedean.AdmissibleCompactFiniteClosure
import Langlands.Representation.Archimedean.GKModuleQuotient
import Langlands.Representation.Archimedean.RealPrincipalSeriesCompactAverages
import Langlands.Representation.Archimedean.RealLeviBlockHaar
import Langlands.Representation.Archimedean.RealSmoothGKImageClosure
import Langlands.Representation.Archimedean.SmoothIntertwiner

/-! # Transfer of compactly weighted real group translates -/

noncomputable section

open MeasureTheory
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors

universe uV uE₁ uE₂

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

local notation:max "G" rank:max => Langlands.GeneralLinear rank ℝ
local notation:max "K" rank:max => unitaryCompact ℝ rank
local notation:max "O" rank:max => Matrix.unitaryGroup (Fin rank) ℝ
local notation:max "M" rank:max => Matrix (Fin rank) (Fin rank) ℝ
local notation:max "L" rank:max => ℂ ⊗[ℝ] (M rank)
local notation:max "I" rank:max => matrixModel ℝ rank
local notation:max "D" rank:max R:max => DerivativeSmoothVectors (I rank) R
local notation:max "ε" rank:max R:max => derivativeCLM (I rank) R []

section Product

variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  (R₁ : G n →* (E₁ →L[ℂ] E₁)) (R₂ : G n →* (E₂ →L[ℂ] E₂))

private def diagonalAction : G n →* ((E₁ × E₂) →L[ℂ] (E₁ × E₂)) where
  toFun g := (R₁ g).prodMap (R₂ g)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro v
    change (R₁ (1 : G n) v.1, R₂ (1 : G n) v.2) = v
    simp only [map_one, one_apply_eq_self]
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [map_mul, mul_apply_eq_comp, ContinuousLinearMap.coe_prodMap', Prod.map]

local notation "R₁₂" => diagonalAction R₁ R₂

private theorem isContinuousRepresentation_diagonalAction
    (hR₁ : IsContinuousRepresentation R₁) (hR₂ : IsContinuousRepresentation R₂) :
    IsContinuousRepresentation R₁₂ := by
  exact (hR₁.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
    (hR₂.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

private theorem isSmoothVector_prod (v₁ : D n R₁) (v₂ : D n R₂) :
    IsSmoothVector I n R₁₂ (ε n R₁ v₁, ε n R₂ v₂) := by
  exact (toSmooth I n R₁ v₁).prop.prodMk_space (toSmooth I n R₂ v₂).prop

private def pairSmooth (v₁ : D n R₁) (v₂ : D n R₂) : D n R₁₂ :=
  (toSmooth I n R₁₂).symm ⟨(ε n R₁ v₁, ε n R₂ v₂), isSmoothVector_prod R₁ R₂ v₁ v₂⟩

private theorem pairSmooth_operator (X : M n) (v₁ : D n R₁) (v₂ : D n R₂) :
    operator I n R₁₂ X (pairSmooth R₁ R₂ v₁ v₂) =
      pairSmooth R₁ R₂ (operator I n R₁ X v₁) (operator I n R₂ X v₂) := by
  apply (toSmooth I n R₁₂).injective
  apply Subtype.ext
  apply Prod.ext
  · exact (SmoothIntertwiner.lieDerivative_map I n R₁₂ R₁
      (ContinuousLinearMap.fst ℂ E₁ E₂) (fun _ _ => rfl) X
      (isSmoothVector_prod R₁ R₂ v₁ v₂)).symm
  · exact (SmoothIntertwiner.lieDerivative_map I n R₁₂ R₂
      (ContinuousLinearMap.snd ℂ E₁ E₂) (fun _ _ => rfl) X
      (isSmoothVector_prod R₁ R₂ v₁ v₂)).symm

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (e : V →ₗ[ℂ] D n R₁) (f : V →ₗ[ℂ] D n R₂)

private def pairSmoothLinearMap : V →ₗ[ℂ] D n R₁₂ where
  toFun v := pairSmooth R₁ R₂ (e v) (f v)
  map_add' v w := by
    apply (toSmooth I n R₁₂).injective
    apply Subtype.ext
    change (ε n R₁ (e (v + w)), ε n R₂ (f (v + w))) =
      (ε n R₁ (e v) + ε n R₁ (e w), ε n R₂ (f v) + ε n R₂ (f w))
    simp only [map_add]
  map_smul' c v := by
    apply (toSmooth I n R₁₂).injective
    apply Subtype.ext
    change (ε n R₁ (e (c • v)), ε n R₂ (f (c • v))) =
      (c • ε n R₁ (e v), c • ε n R₂ (f v))
    simp only [map_smul]

private theorem isSmoothGKIntertwiner_pairSmoothLinearMap
    {ρ : Representation ℂ O n V} {π : L n →ₗ⁅ℂ⁆ Module.End ℂ V}
    (he : IsSmoothGKIntertwiner ℝ n R₁ ρ π e) (hf : IsSmoothGKIntertwiner ℝ n R₂ ρ π f) :
    IsSmoothGKIntertwiner ℝ n R₁₂ ρ π (pairSmoothLinearMap R₁ R₂ e f) := by
  constructor
  · intro k v
    apply (toSmooth I n R₁₂).injective
    apply Subtype.ext
    change (ε n R₁ (e (ρ k v)), ε n R₂ (f (ρ k v))) =
      (R₁ (Unitary.toUnits k) (ε n R₁ (e v)), R₂ (Unitary.toUnits k) (ε n R₂ (f v)))
    rw [he.1, hf.1]
    rfl
  · intro X v
    change pairSmooth R₁ R₂ (e (π (1 ⊗ₜ[ℝ] X) v)) (f (π (1 ⊗ₜ[ℝ] X) v)) =
      operator I n R₁₂ X (pairSmooth R₁ R₂ (e v) (f v))
    rw [he.2, hf.2, pairSmooth_operator]

end Product

/-- A compact average of a group translate with a weight in a finite left-translation
type can be lifted to an algebraic vector with both prescribed underlying values. -/
def RealSmoothCompactWeightedTransferStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ O n V) (π : L n →ₗ⁅ℂ⁆ Module.End ℂ V)
    (E₁ : Type uE₁) [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    (R₁ : G n →* (E₁ →L[ℂ] E₁)) (e : V →ₗ[ℂ] D n R₁)
    (E₂ : Type uE₂) [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [CompleteSpace E₂]
    (R₂ : G n →* (E₂ →L[ℂ] E₂)) (f : V →ₗ[ℂ] D n R₂)
    [MeasurableSpace K n] [BorelSpace K n] (μ : Measure K n)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant],
    IsRealGKModule n ρ π → IsAdmissibleGKModule ρ →
    Function.Injective e → IsContinuousRepresentation R₁ → IsContinuousRepresentation R₂ →
    IsSmoothGKIntertwiner ℝ n R₁ ρ π e → IsSmoothGKIntertwiner ℝ n R₂ ρ π f →
    ∀ {d : ℕ} (τ : K n →* Matrix (Fin d) (Fin d) ℂ) (F : (Fin d → ℂ) →ₗ[ℂ] C(K n, ℂ)),
      (∀ (k x : K n) (a : Fin d → ℂ), F (τ k *ᵥ a) x = F a (k⁻¹ * x)) →
      ∀ (u : Fin d → ℂ) (g : G n) (v : V), ∃ z : V,
        ε n R₁ (e z) = ∫ k : K n, F u k • R₁ ((k : G n) * g) (ε n R₁ (e v)) ∂μ ∧
        ε n R₂ (f z) = ∫ k : K n, F u k • R₂ ((k : G n) * g) (ε n R₂ (f v)) ∂μ

/-- The diagonal action puts the two integrals in the closure of the same algebraic
graph. The weight makes the pair compact-finite, so compact admissibility puts it in
the graph itself. -/
theorem realSmoothCompactWeightedTransfer : RealSmoothCompactWeightedTransferStatement.{uV, uE₁, uE₂} := by
  intro n V _ _ ρ π E₁ _ _ _ R₁ e E₂ _ _ _ R₂ f _ _ μ _ _ hGK hadm heinj hR₁ hR₂ he hf d τ F hF u g v
  let R := diagonalAction R₁ R₂
  let hR : IsContinuousRepresentation R := isContinuousRepresentation_diagonalAction R₁ R₂ hR₁ hR₂
  let p := pairSmoothLinearMap R₁ R₂ e f
  have hp := isSmoothGKIntertwiner_pairSmoothLinearMap R₁ R₂ e f he hf
  let P := (ε n R).toLinearMap.comp p
  let C := P.range.topologicalClosure
  have hC := realSmoothGKImageClosure n V ρ π E₁ R₁ e (E₁ × E₂) R p hGK hadm heinj he hR hp
  let c := RealPrincipalSeriesHilbert.orthogonalCompactEquiv n
  let σ : Representation ℂ (K n) V := ρ.comp c.symm.toMonoidHom
  have hP (k : K n) (x : V) : P (σ k x) = normCompactRepresentation K n R k (P x) := by
    have hk : Unitary.toUnits (c.symm k) = (k : G n) :=
      congrArg Subtype.val (c.apply_symm_apply k)
    exact congrArg (ε n R) ((hp.1 (c.symm k) x).trans (by rw [hk]))
  let W : Subrepresentation (normCompactRepresentation K n R) :=
    { toSubmodule := P.range
      apply_mem_toSubmodule := by
        rintro k _ ⟨x, rfl⟩
        exact ⟨σ k x, hP k x⟩ }
  have hfin (x : V) : FiniteVectors.IsFiniteVector σ x := by
    let : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ x) := hGK.1 x
    apply Submodule.finiteDimensional_of_le (S₂ := FiniteVectors.orbitSpan ρ x)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact FiniteVectors.action_mem_orbitSpan ρ (c.symm k) x
  have hc : Continuous c.symm := RealPrincipalSeriesHilbert.continuous_orthogonalCompactEquiv_symm
  have hcont (x : V) (ℓ : V →ₗ[ℂ] ℂ) : Continuous (fun k : K n => ℓ (σ k x)) :=
    (hGK.2.1 x ℓ).comp hc
  have hadmσ : IsAdmissibleGKModule σ := by
    intro l η hη
    let η' := η.comp c.toMonoidHom
    have hη' : Continuous η' := hη.comp RealPrincipalSeriesHilbert.continuous_orthogonalCompactEquiv
    have hEq : gkIntertwiners σ l η = gkIntertwiners ρ l η' := by
      ext T
      constructor
      · intro hT k x
        have h := hT (c k) x
        change T (η (c k) *ᵥ x) = ρ (c.symm (c k)) (T x) at h
        rwa [c.symm_apply_apply] at h
      · intro hT k x
        have h := hT (c.symm k) x
        change T (η (c (c.symm k)) *ᵥ x) = ρ (c.symm k) (T x) at h
        rwa [c.apply_symm_apply] at h
    rw [hEq]
    exact hadm l η' hη'
  let T : σ.IntertwiningMap (normCompactRepresentation K n R) :=
    P.intertwiningMap_of_isIntertwiningMap _ _ hP
  let A : σ.IntertwiningMap W.toRepresentation :=
    (P.codRestrict W.toSubmodule (fun x => ⟨x, rfl⟩)).intertwiningMap_of_isIntertwiningMap _ _
      (fun k x => Subtype.ext (hP k x))
  have hA : Function.Surjective A := by
    intro y
    obtain ⟨x, hx⟩ := y.prop
    exact ⟨x, Subtype.ext hx⟩
  have hW : ∀ x ∈ W.toSubmodule, FiniteVectors.IsFiniteVector (normCompactRepresentation K n R) x := by
    rintro _ ⟨x, rfl⟩
    exact (hfin x).map T
  let j : C(K n, G n) := ⟨Subtype.val, continuous_subtype_val⟩
  let q := compactWeightedOrbit μ R hR j (F u) (R g (P v))
  have hqfin : FiniteVectors.IsFiniteVector (normCompactRepresentation K n R) q :=
    isFiniteVector_compactWeightedOrbit K n μ R hR τ F hF u (R g (P v))
  let b (k : K n) : E₁ × E₂ := F u k • R (k : G n) (R g (P v))
  have hb : Integrable b μ := integrable_compactWeightedOrbit μ R hR j (F u) _
  have hg : R g (P v) ∈ C := hC g _ (Submodule.le_topologicalClosure _ ⟨v, rfl⟩)
  have hqC : q ∈ W.toSubmodule.topologicalClosure := by
    let : IsClosed (C : Set (E₁ × E₂)) := Submodule.isClosed_topologicalClosure _
    apply (Submodule.Quotient.mk_eq_zero C).mp
    change C.mkQL (∫ k : K n, b k ∂μ) = 0
    rw [← C.mkQL.integral_comp_comm hb]
    exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun k =>
      (Submodule.Quotient.mk_eq_zero C).mpr (C.smul_mem (F u k) (hC _ _ hg)))
  have hq := admissibleCompactFiniteClosure K n μ R W hR
    (hadmσ.of_surjective hfin hcont A hA) hW hqC hqfin
  obtain ⟨z, hz⟩ := hq
  let p₁ := ContinuousLinearMap.fst ℂ E₁ E₂
  let p₂ := ContinuousLinearMap.snd ℂ E₁ E₂
  refine ⟨z, ?_, ?_⟩
  · change p₁ (P z) = _
    rw [hz]
    change p₁ (∫ k : K n, b k ∂μ) = _
    rw [← p₁.integral_comp_comm hb]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun k => ?_
    change F u k • R₁ (k : G n) (R₁ g (ε n R₁ (e v))) =
      F u k • R₁ ((k : G n) * g) (ε n R₁ (e v))
    rw [map_mul, mul_apply_eq_comp]
  · change p₂ (P z) = _
    rw [hz]
    change p₂ (∫ k : K n, b k ∂μ) = _
    rw [← p₂.integral_comp_comm hb]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun k => ?_
    change F u k • R₂ (k : G n) (R₂ g (ε n R₂ (f v))) =
      F u k • R₂ ((k : G n) * g) (ε n R₂ (f v))
    rw [map_mul, mul_apply_eq_comp]

section MatrixOrthogonal

attribute [local instance] RealLeviBlockHaar.secondCountableTopology_O

/-- The same weighted transfer in matrix orthogonal coordinates and their normalized
Haar measure. -/
theorem realSmoothCompactWeightedTransfer_orthogonal
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (O n) V) (π : L n →ₗ⁅ℂ⁆ Module.End ℂ V)
    {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    (R₁ : G n →* (E₁ →L[ℂ] E₁)) (e : V →ₗ[ℂ] D n R₁)
    {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [CompleteSpace E₂]
    (R₂ : G n →* (E₂ →L[ℂ] E₂)) (f : V →ₗ[ℂ] D n R₂)
    [MeasurableSpace (O n)] [BorelSpace (O n)] [MeasurableMul (O n)]
    (μ : Measure (O n)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (hGK : IsRealGKModule n ρ π) (hadm : IsAdmissibleGKModule ρ)
    (heinj : Function.Injective e)
    (hR₁ : IsContinuousRepresentation R₁) (hR₂ : IsContinuousRepresentation R₂)
    (he : IsSmoothGKIntertwiner ℝ n R₁ ρ π e) (hf : IsSmoothGKIntertwiner ℝ n R₂ ρ π f)
    {d : ℕ} (τ : O n →* Matrix (Fin d) (Fin d) ℂ) (F : (Fin d → ℂ) →ₗ[ℂ] C(O n, ℂ))
    (hF : ∀ (k x : O n) (a : Fin d → ℂ), F (τ k *ᵥ a) x = F a (k⁻¹ * x))
    (a : Fin d → ℂ) (g : G n) (v : V) :
    ∃ z : V,
      ε n R₁ (e z) = ∫ k : O n, F a k • R₁ (Unitary.toUnits k * g) (ε n R₁ (e v)) ∂μ ∧
      ε n R₂ (f z) = ∫ k : O n, F a k • R₂ (Unitary.toUnits k * g) (ε n R₂ (f v)) ∂μ := by
  let : MeasurableSpace (K n) := borel (K n)
  let : BorelSpace (K n) := ⟨rfl⟩
  let c := RealPrincipalSeriesHilbert.orthogonalCompactEquiv n
  have hc : Continuous c := RealPrincipalSeriesHilbert.continuous_orthogonalCompactEquiv
  have hci : Continuous c.symm := RealPrincipalSeriesHilbert.continuous_orthogonalCompactEquiv_symm
  let ν := μ.map c
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hc.measurable.aemeasurable).2
    inferInstance
  let : ν.IsMulLeftInvariant :=
    isMulLeftInvariant_map (μ := μ) c.toMonoidHom.toMulHom hc.measurable c.surjective
  let τ' := τ.comp c.symm.toMonoidHom
  let F' := (ContinuousMap.compCLM ℂ ℂ (⟨c.symm, hci⟩ : C(K n, O n))).toLinearMap.comp F
  have hF' (k x : K n) (b : Fin d → ℂ) : F' (τ' k *ᵥ b) x = F' b (k⁻¹ * x) := by
    change F (τ (c.symm k) *ᵥ b) (c.symm x) = F b (c.symm (k⁻¹ * x))
    rw [map_mul, map_inv]
    exact hF _ _ _
  obtain ⟨z, hz₁, hz₂⟩ := realSmoothCompactWeightedTransfer n V ρ π E₁ R₁ e E₂ R₂ f ν
    hGK hadm heinj hR₁ hR₂ he hf τ' F' hF' a g v
  refine ⟨z, ?_, ?_⟩
  · let b (k : K n) := F' a k • R₁ ((k : G n) * g) (ε n R₁ (e v))
    have hbC : Continuous b := (F' a).continuous.smul (hR₁.comp
      ((continuous_subtype_val.mul continuous_const).prodMk continuous_const))
    have hb : Integrable b ν := hbC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    change ε n R₁ (e z) = ∫ k : O n, _ ∂μ
    rw [hz₁]
    change (∫ k : K n, b k ∂μ.map c) = _
    rw [integral_map hc.measurable.aemeasurable hb.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    change F a (c.symm (c k)) • R₁ (Unitary.toUnits k * g) (ε n R₁ (e v)) = _
    rw [MulEquiv.symm_apply_apply]
  · let b (k : K n) := F' a k • R₂ ((k : G n) * g) (ε n R₂ (f v))
    have hbC : Continuous b := (F' a).continuous.smul (hR₂.comp
      ((continuous_subtype_val.mul continuous_const).prodMk continuous_const))
    have hb : Integrable b ν := hbC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    change ε n R₂ (f z) = ∫ k : O n, _ ∂μ
    rw [hz₂]
    change (∫ k : K n, b k ∂μ.map c) = _
    rw [integral_map hc.measurable.aemeasurable hb.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    change F a (c.symm (c k)) • R₂ (Unitary.toUnits k * g) (ε n R₂ (f v)) = _
    rw [MulEquiv.symm_apply_apply]

end MatrixOrthogonal

end Langlands.Archimedean
