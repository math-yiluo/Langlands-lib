import Langlands.BaseChange.OrbitalIntegral
import Langlands.Group.GL.Padic
import Langlands.TraceFormula.TwistedOrbitalConjugation
import Langlands.Weil.Local.ExtensionResidue
import Mathlib.Topology.Algebra.Group.Matrix

/-! # Changing representatives in base-change concordance -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.QuotientIntegration Langlands.TraceFormula

universe u v

theorem continuous_baseChange_padic {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier] (n : ℕ) :
    @Continuous _ _ (F.canonicalGeneralLinearTopology n) (E.canonicalGeneralLinearTopology n)
      (baseChange F.Carrier E.Carrier n) := by
  let := F.canonicalNormedField
  let := E.canonicalNormedField
  exact (Langlands.Weil.Local.extension_isometry F E
    (IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier)).continuous.generalLinearGroup_map

section Algebra

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {l n : ℕ}

/-- Norm membership is invariant under ordinary conjugation. -/
theorem isNorm_conj_iff (hσ : σ ^ l = 1) (a γ : GeneralLinear n F) :
    IsNorm σ l (a⁻¹ * γ * a) ↔ IsNorm σ l γ := by
  have step {g : GeneralLinear n F} (h : IsNorm σ l g) (y : GeneralLinear n F) :
      IsNorm σ l (y⁻¹ * g * y) := by
    obtain ⟨δ, hδ⟩ := h
    exact ⟨δ, by simpa only [inv_one, one_mul, map_one, mul_one] using hδ.twistedConj hσ 1 y⟩
  refine ⟨fun h => ?_, fun h => step h a⟩
  simpa only [inv_inv, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left,
    inv_mul_cancel, one_mul] using step h a⁻¹

private theorem normalized_cyclicNorm_eq (hσ : σ ^ l = 1)
    {δ : GeneralLinear n E} {γ : GeneralLinear n F} {x : GeneralLinear n E}
    (hx : x⁻¹ * cyclicNorm σ l δ * x = baseChange F E n γ) (a : GeneralLinear n F) :
    cyclicNorm σ l (twistedConj (entrywiseAut σ n) (x * baseChange F E n a) δ) =
      baseChange F E n (twistedConj (MonoidHom.id (GeneralLinear n F)) a γ) := by
  rw [twistedConj_apply, twistedConj_apply, MonoidHom.id_apply,
    cyclicNorm_twistedConj, hσ, entrywiseAut_one_apply, map_mul, map_mul, map_inv, ← hx]
  group

end Algebra

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

section Measures

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
variable {σ : E ≃ₐ[F] E} {l n : ℕ}
variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]

private theorem isAssociatedMeasure_normalized
    (hσ : σ ^ l = 1) (hbase : Measurable (baseChange F E n))
    {δ : GeneralLinear n E} {γ : GeneralLinear n F} {x : GeneralLinear n E}
    (hx : x⁻¹ * cyclicNorm σ l δ * x = baseChange F E n γ)
    {μδ : Measure (sigmaCentralizer σ n δ)} {μγ : Measure (glCentralizer γ)}
    (hμ : Measure.map (fun c : sigmaCentralizer σ n δ => x⁻¹ * c.val * x) μδ =
      Measure.map (fun c : glCentralizer γ => baseChange F E n c.val) μγ)
    (a : GeneralLinear n F) :
    let t := x * baseChange F E n a
    IsAssociatedMeasure σ l (twistedConj (entrywiseAut σ n) t δ)
      (twistedConj (MonoidHom.id (GeneralLinear n F)) a γ)
      (Measure.map (twistedCentralizerConj (entrywiseAut σ n) t δ) μδ)
      (Measure.map (twistedCentralizerConj (MonoidHom.id (GeneralLinear n F)) a γ) μγ) := by
  dsimp only
  refine ⟨1, ?_, ?_⟩
  · simpa only [inv_one, one_mul, mul_one] using normalized_cyclicNorm_eq hσ hx a
  · let z := baseChange F E n a
    let eδ := twistedCentralizerConj (entrywiseAut σ n) (x * z) δ
    let eγ := twistedCentralizerConj (MonoidHom.id (GeneralLinear n F)) a γ
    simp only [inv_one, one_mul, mul_one]
    change Measure.map Subtype.val (Measure.map eδ μδ) =
      Measure.map (fun c => baseChange F E n c.val) (Measure.map eγ μγ)
    have heδ : Measurable (eδ : _ → _) := eδ.continuous.measurable
    have heγ : Measurable (eγ : _ → _) := eγ.continuous.measurable
    have hz : Measurable (fun g : GeneralLinear n E => z⁻¹ * g * z) :=
      ((continuous_const.mul continuous_id).mul continuous_const).measurable
    have hxc : Measurable (fun c : sigmaCentralizer σ n δ => x⁻¹ * c.val * x) :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    have hbγ : Measurable (fun c : glCentralizer γ => baseChange F E n c.val) :=
      hbase.comp measurable_subtype_coe
    have hbγ' : Measurable (fun c : glCentralizer
        (twistedConj (MonoidHom.id (GeneralLinear n F)) a γ) => baseChange F E n c.val) :=
      hbase.comp measurable_subtype_coe
    have hδ : Subtype.val ∘ eδ =
        (fun g : GeneralLinear n E => z⁻¹ * g * z) ∘
          (fun c : sigmaCentralizer σ n δ => x⁻¹ * c.val * x) := by
      funext c
      change (x * z)⁻¹ * c.val * (x * z) = z⁻¹ * (x⁻¹ * c.val * x) * z
      group
    have hγ : (fun c => baseChange F E n c.val) ∘ eγ =
        (fun g : GeneralLinear n E => z⁻¹ * g * z) ∘
          (fun c : glCentralizer γ => baseChange F E n c.val) := by
      funext c
      change baseChange F E n (a⁻¹ * c.val * a) =
        z⁻¹ * baseChange F E n c.val * z
      rw [map_mul, map_mul, map_inv]
    rw [Measure.map_map measurable_subtype_coe heδ, Measure.map_map hbγ' heγ, hδ, hγ,
      ← Measure.map_map hz hxc, hμ, Measure.map_map hz hbγ]

variable [MeasurableMul (GeneralLinear n F)] [MeasurableMul (GeneralLinear n E)]

/-- To check concordance at any associated pair, one may replace the ordinary element
by a specified conjugate and check at twisted representatives with exact norm equality. -/
theorem concordAt_of_conj_of_cyclicNorm_eq
    (hσ : σ ^ l = 1) (hbase : Measurable (baseChange F E n))
    {μF : Measure (GeneralLinear n F)} [μF.IsMulLeftInvariant]
    {μE : Measure (GeneralLinear n E)} [μE.IsMulLeftInvariant]
    {φ : GeneralLinear n E → ℂ} {f : GeneralLinear n F → ℂ}
    (δ : GeneralLinear n E) (γ a : GeneralLinear n F)
    (h : ∀ δ', cyclicNorm σ l δ' = baseChange F E n (a⁻¹ * γ * a) →
      ConcordAt σ l μF μE φ f δ' (a⁻¹ * γ * a)) :
    ConcordAt σ l μF μE φ f δ γ := by
  intro μδ _ _ μγ _ _ νδ νγ hδ hγ hassoc
  obtain ⟨x, hx, hμ⟩ := hassoc
  let t := x * baseChange F E n a
  let δ' := twistedConj (entrywiseAut σ n) t δ
  let γ' := twistedConj (MonoidHom.id (GeneralLinear n F)) a γ
  let μδ' := Measure.map (twistedCentralizerConj (entrywiseAut σ n) t δ) μδ
  let μγ' := Measure.map (twistedCentralizerConj (MonoidHom.id (GeneralLinear n F)) a γ) μγ
  let νδ' := Measure.map (twistedQuotientConj (entrywiseAut σ n) t δ) νδ
  let νγ' := Measure.map (twistedQuotientConj (MonoidHom.id (GeneralLinear n F)) a γ) νγ
  have hHaarδ' : μδ'.IsHaarMeasure :=
    (twistedCentralizerConj (entrywiseAut σ n) t δ).isHaarMeasure_map μδ
  have hHaarγ' : μγ'.IsHaarMeasure :=
    (twistedCentralizerConj (MonoidHom.id (GeneralLinear n F)) a γ).isHaarMeasure_map μγ
  have hRightδ' : μδ'.IsMulRightInvariant :=
    map_twistedCentralizerConj_isMulRightInvariant (entrywiseAut σ n) t δ μδ
  have hRightγ' : μγ'.IsMulRightInvariant :=
    map_twistedCentralizerConj_isMulRightInvariant (MonoidHom.id (GeneralLinear n F)) a γ μγ
  have hδ' : IsCompatible (sigmaCentralizer σ n δ') μE μδ' νδ' :=
    isCompatible_twistedQuotientConj (entrywiseAut σ n) t δ μδ μE νδ hδ
  have hγ' : IsCompatible (glCentralizer γ') μF μγ' νγ' :=
    isCompatible_twistedQuotientConj (MonoidHom.id (GeneralLinear n F)) a γ μγ μF νγ hγ
  have hNormalized := h δ' (normalized_cyclicNorm_eq hσ hx a)
  calc
    sigmaOrbitalIntegral σ n δ νδ φ = sigmaOrbitalIntegral σ n δ' νδ' φ :=
      (twistedOrbitalIntegral_twistedQuotientConj (entrywiseAut σ n) t δ νδ φ).symm
    _ = orbitalIntegral γ' νγ' f :=
      @hNormalized μδ' hHaarδ' hRightδ' μγ' hHaarγ' hRightγ' νδ' νγ' hδ' hγ'
        (isAssociatedMeasure_normalized hσ hbase hx hμ a)
    _ = orbitalIntegral γ νγ f :=
      twistedOrbitalIntegral_twistedQuotientConj (MonoidHom.id (GeneralLinear n F)) a γ νγ f

omit [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [MeasurableMul (GeneralLinear n E)] in
/-- Vanishing for all compatible quotient measures is unchanged on replacing the
ordinary element by a conjugate. -/
theorem orbitalIntegral_eq_zero_of_conj {μF : Measure (GeneralLinear n F)}
    [μF.IsMulLeftInvariant] (f : GeneralLinear n F → ℂ) (γ a : GeneralLinear n F)
    (h : ∀ (μ' : Measure (glCentralizer (a⁻¹ * γ * a))) [μ'.IsHaarMeasure]
      [μ'.IsMulRightInvariant] (ν' : Measure (LeftQuotient (glCentralizer (a⁻¹ * γ * a)))),
      IsCompatible (glCentralizer (a⁻¹ * γ * a)) μF μ' ν' →
        orbitalIntegral (a⁻¹ * γ * a) ν' f = 0)
    (μ : Measure (glCentralizer γ)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (glCentralizer γ)))
    (hν : IsCompatible (glCentralizer γ) μF μ ν) :
    orbitalIntegral γ ν f = 0 := by
  let θ := MonoidHom.id (GeneralLinear n F)
  have hHaar : (Measure.map (twistedCentralizerConj θ a γ) μ).IsHaarMeasure :=
    (twistedCentralizerConj θ a γ).isHaarMeasure_map μ
  have hRight := map_twistedCentralizerConj_isMulRightInvariant θ a γ μ
  have hcompat := isCompatible_twistedQuotientConj θ a γ μ μF ν hν
  exact (twistedOrbitalIntegral_twistedQuotientConj θ a γ ν f).symm.trans
    (@h _ hHaar hRight _ hcompat)

end Measures

end Langlands.BaseChange
