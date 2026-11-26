import Langlands.TraceFormula.PositiveQuotientTwistedTraceComparisonStatement
import Langlands.Analysis.OperatorTraceProof

/-! # Proof of the twisted positive-quotient trace comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions Langlands.QuotientIntegration
open Langlands.Analysis Langlands.Analysis.OperatorIdeals
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

private theorem pullback_congr {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μX : Measure X} {μY : Measure Y} {r s : X → Y} (hr : MeasurePreserving r μX μY)
    (hs : MeasurePreserving s μX μY) (h : r = s) (v : Lp ℂ 2 μY) :
    Lp.compMeasurePreserving r hr v = Lp.compMeasurePreserving s hs v := by
  subst s
  rfl

/-- Pullback along a measure-preserving equivalence, with inverse pullback along its inverse. -/
private def pullbackEquiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μX : Measure X} {μY : Measure Y} (j : X ≃ᵐ Y) (hj : MeasurePreserving j μX μY) :
    Lp ℂ 2 μY ≃ₗᵢ[ℂ] Lp ℂ 2 μX := by
  let hj' := MeasurePreserving.symm j hj
  refine LinearIsometryEquiv.ofLinearIsometry (Lp.compMeasurePreservingₗᵢ ℂ j hj)
    (Lp.compMeasurePreservingₗᵢ ℂ j.symm hj').toLinearMap
    (LinearMap.ext fun w => ?_) (LinearMap.ext fun v => ?_)
  · change Lp.compMeasurePreserving j hj (Lp.compMeasurePreserving j.symm hj' w) = w
    rw [← Lp.compMeasurePreserving_comp_apply,
      pullback_congr _ (MeasurePreserving.id _) j.symm_comp_self]
    exact Lp.compMeasurePreserving_id_apply w
  · change Lp.compMeasurePreserving j.symm hj' (Lp.compMeasurePreserving j hj v) = v
    rw [← Lp.compMeasurePreserving_comp_apply,
      pullback_congr _ (MeasurePreserving.id _) j.self_comp_symm]
    exact Lp.compMeasurePreserving_id_apply v

private theorem traceComparison_of_intertwines {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : E ≃ₗᵢ[ℂ] H) (A : E →L[ℂ] E) (B : H →L[ℂ] H)
    (hU : ∀ v, U (A v) = B (U v)) :
    (IsTraceClass A ↔ IsTraceClass B) ∧
      (IsTraceClass A → operatorTrace A = operatorTrace B) := by
  let C := U.toLinearIsometry.toContinuousLinearMap
  let D := U.symm.toLinearIsometry.toContinuousLinearMap
  have hB : (C.comp A).comp D = B := by
    apply ContinuousLinearMap.ext
    intro w
    change U (A (U.symm w)) = B w
    rw [hU, U.apply_symm_apply]
  have hA : (D.comp B).comp C = A := by
    apply ContinuousLinearMap.ext
    intro v
    change U.symm (B (U v)) = A v
    rw [← hU, U.symm_apply_apply]
  have hDC : A.comp (D.comp C) = A := by
    apply ContinuousLinearMap.ext
    intro v
    change A (U.symm (U v)) = A v
    rw [U.symm_apply_apply]
  have forward (h : IsTraceClass A) :
      IsTraceClass B ∧ operatorTrace A = operatorTrace B := by
    obtain ⟨hClass, _, hTrace⟩ := operatorTraceCyclicity E H A C D h
    rw [hB] at hClass hTrace
    rw [hDC] at hTrace
    exact ⟨hClass, hTrace.symm⟩
  refine ⟨⟨fun h => (forward h).1, ?_⟩, fun h => (forward h).2⟩
  intro h
  rw [← hA]
  exact (operatorTraceCyclicity H E B D C h).1

private theorem adelicAut_mem_positiveRationalSubgroup_iff
    (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (τ : Aut G) (hfix : i ≫ τ.asIso.hom = i) (x : AdelicGroupPoints F G) :
    adelicAut F τ x ∈ positiveRationalSubgroup F G T i ↔
      x ∈ positiveRationalSubgroup F G T i := by
  have map_mem (k : G ⟶ G) (hk : i ≫ k = i) :
      positiveRationalSubgroup F G T i ≤
        (positiveRationalSubgroup F G T i).comap (AdelicGroupPoints.map F G G k).toMonoidHom := by
    change imageSubgroup F T G i ⊔ rationalSubgroup F G ≤ _
    apply sup_le
    · rintro _ ⟨a, ha, rfl⟩
      change AdelicGroupPoints.map F G G k (AdelicGroupPoints.map F T.toGrp G i a) ∈
        positiveRationalSubgroup F G T i
      rw [map_comp_apply, hk]
      exact imageSubgroup_le_positiveRationalSubgroup F G T i ⟨a, ha, rfl⟩
    · rintro _ ⟨q, rfl⟩
      change AdelicGroupPoints.map F G G k (rational F G q) ∈ positiveRationalSubgroup F G T i
      exact rationalSubgroup_le_positiveRationalSubgroup F G T i
        ⟨G.affinePointsTarget k (CommAlgCat.of F F) q,
          DFunLike.congr_fun (rational_naturality F G k) q⟩
  have hfixInv : i ≫ τ.asIso.inv = i := by
    calc
      i ≫ τ.asIso.inv = (i ≫ τ.asIso.hom) ≫ τ.asIso.inv :=
        congrArg (fun k => k ≫ τ.asIso.inv) hfix.symm
      _ = i := by rw [Category.assoc, τ.asIso.hom_inv_id, Category.comp_id]
  constructor
  · intro hx
    have h := map_mem τ.asIso.inv hfixInv hx
    change (adelicAut F τ).symm (adelicAut F τ x) ∈ positiveRationalSubgroup F G T i at h
    rwa [ContinuousMulEquiv.symm_apply_apply] at h
  · intro hx
    exact map_mem τ.asIso.hom hfix hx

/-- A finite-order automorphism fixing the central split torus induces the positive-quotient
twist. The two twisted integrated operators are trace class together, and in that case their
traces agree. -/
theorem positiveQuotientTwistedTraceComparison :
    PositiveQuotientTwistedTraceComparisonStatement.{u} := by
  intro F _ _ G _ _ T i hi _ I _ e hc _ τ hτ hfix
  let ΓP := positiveRationalSubgroup F G T i
  let ΓN := rationalNormOneSubgroup F G
  let νP := positiveRationalQuotientHaarMeasure F G T i
  let νN := normOneRationalQuotientHaarMeasure F G
  let j := positiveQuotientMeasurableEquiv F G T i hi I e hc
  let hj : MeasurePreserving j νN νP := measurePreserving_positiveQuotient F G T i hi I e hc
  let hΘ := adelicAut_mem_positiveRationalSubgroup_iff F G T i τ hfix
  let hθ := normOneAut_mem_rationalNormOneSubgroup_iff F τ
  let positiveAut := quotientAutomorphism ΓP (adelicAut F τ) hΘ
  let normAut := rationalQuotientAut F τ
  let hθμ : MeasurePreserving normAut.symm νN νN :=
    measurePreserving_rationalQuotientAut_symm F τ hτ
  have hInv (q : NormOneRationalQuotient F G) :
      positiveAut.symm (j q) = j (normAut.symm q) := by
    -- On norm-one representatives, both maps use the same inverse adelic action.
    obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective ΓN q
    rfl
  have hΘμ : MeasurePreserving positiveAut.symm νP νP := by
    have hcomp : (positiveAut.symm : PositiveRationalQuotient F G T i → _) =
        j ∘ (normAut.symm ∘ j.symm) := by
      funext q
      obtain ⟨q, rfl⟩ := j.surjective q
      simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using hInv q
    rw [hcomp]
    exact hj.comp (hθμ.comp (MeasurePreserving.symm j hj))
  refine ⟨hΘ, hΘμ, ?_⟩
  intro f fOne hf hfOne π hπnorm hπmeas hπtr
  let U := pullbackEquiv j hj
  let twistP := twistOperator ΓP (adelicAut F τ) hΘ νP hΘμ
  let twistN := twistOperator ΓN (normOneAut F τ) hθ νN hθμ
  have hTwist (v : Lp ℂ 2 νP) : U (twistP v) = twistN (U v) := by
    change Lp.compMeasurePreserving j hj (Lp.compMeasurePreserving positiveAut.symm hΘμ v) =
      Lp.compMeasurePreserving normAut.symm hθμ (Lp.compMeasurePreserving j hj v)
    rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
    exact pullback_congr _ _ (funext hInv) v
  let μA := normalizedPositiveHaarMeasure F G T i hi I e hc
  let : SigmaFinite μA := normalizedPositiveHaarMeasure_sigmaFinite F G T i hi I e hc
  let μN : Measure (normOneSubgroup F G) := Measure.haar
  let μG : Measure (AdelicGroupPoints F G) := Measure.haar
  let d := normOneDecomposition F G T i hi I e
  let p := normOneProjection F G T i hi I e hc
  let hρ := haarQuotientMeasureRightInvariant F G T i hi I e hc
  let ρ := quotientL2RightAction F G T i νP hρ
  let hn := measurePreserving_rightTranslate_normOneRationalQuotientHaarMeasure F G
  have hrt (n : normOneSubgroup F G) (q : NormOneRationalQuotient F G) :
      rightTranslate ΓN n q = LeftCosetSpace.rightTranslate ΓN n q := by
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective ΓN q
    rfl
  have hπpull (n : normOneSubgroup F G) (w : Lp ℂ 2 νN) :
      π n w = Lp.compMeasurePreserving _ (hn n) w := by
    apply Lp.ext
    filter_upwards [hπtr n w, Lp.coeFn_compMeasurePreserving w (hn n)] with q hπ hq
    exact hπ.trans ((congrArg (fun x => w x) (hrt n q)).trans hq.symm)
  have hAction (g : AdelicGroupPoints F G) (v : Lp ℂ 2 νP) :
      U (ρ g v) = π (p g) (U v) := by
    rw [hπpull]
    change Lp.compMeasurePreserving j hj (Lp.compMeasurePreserving _ (hρ g) v) =
      Lp.compMeasurePreserving _ (hn (p g)) (Lp.compMeasurePreserving j hj v)
    rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
    apply pullback_congr
    funext q
    exact (positiveQuotientHomeomorph_rightTranslate F G T i hi I e hc g q).symm
  have hp (a : intrinsicSubgroup F T) (n : normOneSubgroup F G) : p (d (a, n)) = n := by
    change normOneProjection F G T i hi I e hc (positivePointMap F G T i a * n) = n
    rw [map_mul, normOneProjection_positivePointMap, normOneProjection_normOne, one_mul]
  let R := haarQuotientL2IntegratedAction F G T i hi I e hc μG f hf
  let P := integratedIsometricAction μN π hπnorm hπmeas fOne hfOne
  have hIntegrated (v : Lp ℂ 2 νP) : U (R v) = P (U v) := by
    let C := U.toLinearIsometry.toContinuousLinearMap
    let k : AdelicGroupPoints F G → Lp ℂ 2 νP := fun g => f g • ρ g v
    let l : AdelicGroupPoints F G → Lp ℂ 2 νN := fun g => C (k g)
    have hk : Integrable k μG :=
      haarQuotientL2ActionIntegrand_integrable F G T i hi I e hc _ f hf v
    have hd : MeasurePreserving d (μA.prod μN) μG :=
      measurePreserving_normOneDecomposition F G T i hi I e hc
    have hprod : Integrable (fun x => l (d x)) (μA.prod μN) :=
      (hd.integrable_comp_emb d.toMeasurableEquiv.measurableEmbedding).2 (C.integrable_comp hk)
    dsimp only [R, P]
    rw [haarQuotientL2IntegratedAction_apply, integratedIsometricAction_apply]
    calc
      U (∫ g, k g ∂μG) = ∫ g, l g ∂μG := (C.integral_comp_comm hk).symm
      _ = ∫ x, l (d x) ∂(μA.prod μN) := (hd.integral_comp' (f := d.toMeasurableEquiv) l).symm
      _ = ∫ n, ∫ a, l (d (a, n)) ∂μA ∂μN := integral_prod_symm _ hprod
      _ = ∫ n, fOne n • π n (U v) ∂μN := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun n => by
          calc
            (∫ a, l (d (a, n)) ∂μA) = ∫ a, f (d (a, n)) • π n (U v) ∂μA := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun a => by
                change C (f (d (a, n)) • ρ (d (a, n)) v) = _
                rw [map_smul]
                change f (d (a, n)) • U (ρ (d (a, n)) v) = _
                rw [hAction, hp]
            _ = fOne n • π n (U v) := integral_smul_const _ _
  exact traceComparison_of_intertwines U (R.comp twistP) (P.comp twistN) fun v => by
    simp only [ContinuousLinearMap.comp_apply, hIntegrated, hTwist]

end Langlands.TraceFormula
