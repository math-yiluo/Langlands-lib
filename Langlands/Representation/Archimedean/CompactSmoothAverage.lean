import Langlands.Analysis.CompactManifoldVectorIntegral
import Langlands.Representation.Archimedean.SmoothDerivativeTopology

/-! # Genuine derivatives of compact smooth orbit averages -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Topology

namespace Langlands.Archimedean.CompactSmoothAverage

universe u𝔤 uG uH uN uE uX

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace 𝔤 G]
  [LieGroup 𝓘(ℝ, 𝔤) ∞ G]
  {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold 𝓘(ℝ, H) ∞ N]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : G →* (E →L[ℂ] E))
  {v : N → E}

omit [LieGroup 𝓘(ℝ, 𝔤) ∞ G] [IsManifold 𝓘(ℝ, H) ∞ N] in
/-- Every member of a jointly smooth orbit family is a genuine smooth vector. -/
theorem isSmoothVector_family
    (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (v p.2))) (n : N) :
    IsSmoothVector 𝓘(ℝ, 𝔤) π (v n) :=
  hv.comp (contMDiff_id.prodMk contMDiff_const)

omit [LieGroup 𝓘(ℝ, 𝔤) ∞ G] [IsManifold 𝓘(ℝ, H) ∞ N] in
/-- Joint orbit smoothness includes continuity of the original family. -/
theorem continuous_family
    (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (v p.2))) : Continuous v := by
  simpa only [Function.comp_def, map_one, one_apply_eq_self, id_eq] using
    hv.continuous.comp
      ((continuous_const : Continuous (fun _ : N => (1 : G))).prodMk continuous_id)

set_option backward.isDefEq.respectTransparency false in
/-- A genuine derived operator preserves joint smoothness of an orbit family. -/
theorem contMDiff_orbit_lieDerivative
    (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (v p.2))) (X : 𝔤) :
    ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (lieDerivative 𝓘(ℝ, 𝔤) π X (v p.2))) := by
  have hf : ContMDiff ((𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)).prod 𝓘(ℝ, 𝔤)) 𝓘(ℝ, E) ∞
      (fun p : (G × N) × G => π (p.1.1 * p.2) (v p.1.2)) :=
    hv.comp (((contMDiff_fst.comp contMDiff_fst).mul contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst))
  intro p₀
  have hd := (hf.contMDiffAt (x := (p₀, (1 : G)))).mfderiv_apply (m := ∞)
    (x₀ := p₀) (fun p : G × N => fun h : G => π (p.1 * h) (v p.2))
    (fun _ : G × N => (1 : G)) (fun p : G × N => p) (fun _ : G × N => X)
    contMDiffAt_const contMDiffAt_id contMDiffAt_const (by simp)
  have hc : ∀ p : G × N,
      inTangentCoordinates 𝓘(ℝ, 𝔤) 𝓘(ℝ, E) (fun _ : G × N => (1 : G))
        (fun p : G × N => π (p.1 * 1) (v p.2))
        (fun p : G × N => mfderiv 𝓘(ℝ, 𝔤) 𝓘(ℝ, E)
          (fun h => π (p.1 * h) (v p.2)) 1) p₀ p =
        mfderiv 𝓘(ℝ, 𝔤) 𝓘(ℝ, E) (fun h => π (p.1 * h) (v p.2)) 1 := by
    intro p
    rw [inTangentCoordinates_eq]
    · rw [tangentBundleCore_coordChange_model_space]
      have hself : (tangentBundleCore 𝓘(ℝ, 𝔤) G).coordChange
          (achart 𝔤 (1 : G)) (achart 𝔤 (1 : G)) 1 =
            ContinuousLinearMap.id ℝ 𝔤 := by
        ext Y
        exact tangentCoordChange_self (mem_extChartAt_source (I := 𝓘(ℝ, 𝔤)) (1 : G))
      rw [hself, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    · exact mem_chart_source 𝔤 (1 : G)
    · simp
  simp_rw [hc] at hd
  have heq : (fun p : G × N => π p.1 (lieDerivative 𝓘(ℝ, 𝔤) π X (v p.2))) =
      (fun p : G × N => mfderiv 𝓘(ℝ, 𝔤) 𝓘(ℝ, E)
        (fun h => π (p.1 * h) (v p.2)) 1 X) := by
    funext p
    exact apply_lieDerivative 𝓘(ℝ, 𝔤) π p.1 X (isSmoothVector_family π hv p.2)
  rw [heq]
  exact hd

/-- Every genuine word derivative retains joint orbit smoothness. -/
theorem contMDiff_orbit_iteratedLieDerivative
    (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (v p.2))) (Xs : List 𝔤) :
    ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (v p.2))) := by
  induction Xs with
  | nil => exact hv
  | cons X Xs ih =>
      exact contMDiff_orbit_lieDerivative π
        (v := fun n => iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (v n)) ih X

variable [FiniteDimensional ℝ 𝔤] [CompleteSpace E]
  {X : Type uX} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] (a : C(X, ℂ)) (j : C(X, N))

omit [FiniteDimensional ℝ 𝔤] [CompleteSpace E]
    [LieGroup 𝓘(ℝ, 𝔤) ∞ G] [IsManifold 𝓘(ℝ, H) ∞ N] in
/-- The original vector-valued family is integrable along the compact restriction. -/
theorem integrable_family
    (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (v p.2))) :
    Integrable (fun x => a x • v (j x)) μ :=
  (a.continuous.smul ((continuous_family π hv).comp j.continuous)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [FiniteDimensional ℝ 𝔤]
    [LieGroup 𝓘(ℝ, 𝔤) ∞ G] [IsManifold 𝓘(ℝ, H) ∞ N] in
/-- A bounded representation operator commutes with the original compact integral. -/
theorem apply_integral
    (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (v p.2))) (g : G) :
    π g (∫ x, a x • v (j x) ∂μ) = ∫ x, a x • π g (v (j x)) ∂μ := by
  rw [← (π g).integral_comp_comm (integrable_family π μ a j hv)]
  simp only [map_smul]

/-- Compact weighted integration preserves genuine smooth vectors. -/
theorem isSmoothVector_integral
    (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (v p.2))) :
    IsSmoothVector 𝓘(ℝ, 𝔤) π (∫ x, a x • v (j x) ∂μ) := by
  have he : orbitMap π (∫ x, a x • v (j x) ∂μ) =
      (fun g => ∫ x, a x • π g (v (j x)) ∂μ) :=
    funext (apply_integral π μ a j hv)
  change ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, E) ∞ (orbitMap π _)
  rw [he]
  exact Langlands.Analysis.CompactManifoldVectorIntegral.contMDiff_weightedIntegral μ a j hv

set_option backward.isDefEq.respectTransparency false in
/-- Genuine differentiation commutes with the weighted compact integral. -/
theorem lieDerivative_integral
    (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (v p.2))) (Y : 𝔤) :
    lieDerivative 𝓘(ℝ, 𝔤) π Y (∫ x, a x • v (j x) ∂μ) =
      ∫ x, a x • lieDerivative 𝓘(ℝ, 𝔤) π Y (v (j x)) ∂μ := by
  have he : orbitMap π (∫ x, a x • v (j x) ∂μ) =
      (fun g => ∫ x, a x • π g (v (j x)) ∂μ) :=
    funext (apply_integral π μ a j hv)
  change (show 𝔤 →L[ℝ] E from mfderiv 𝓘(ℝ, 𝔤) 𝓘(ℝ, E)
    (orbitMap π (∫ x, a x • v (j x) ∂μ)) 1) Y = _
  rw [he]
  exact Langlands.Analysis.CompactManifoldVectorIntegral.mfderiv_weightedIntegral_apply
    μ a j hv 1 Y

/-- Every genuine derivative word commutes with the original weighted compact integral. -/
theorem iteratedLieDerivative_integral
    (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (v p.2))) (Xs : List 𝔤) :
    iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (∫ x, a x • v (j x) ∂μ) =
      ∫ x, a x • iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (v (j x)) ∂μ := by
  induction Xs with
  | nil => rfl
  | cons Y Xs ih =>
      simp only [iteratedLieDerivative_cons, ih]
      exact lieDerivative_integral π
        (v := fun n => iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (v n)) μ a j
        (contMDiff_orbit_iteratedLieDerivative π hv Xs) Y

omit [FiniteDimensional ℝ 𝔤] [CompleteSpace E] in
/-- Each genuine derivative word of the family is continuous in its parameter. -/
theorem continuous_iteratedLieDerivative_family
    (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (v p.2))) (Xs : List 𝔤) :
    Continuous (fun n => iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (v n)) :=
  continuous_family π (v := fun n => iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (v n))
    (contMDiff_orbit_iteratedLieDerivative π hv Xs)

variable (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
  (fun p : G × N => π p.1 (v p.2)))

omit [FiniteDimensional ℝ 𝔤] [CompleteSpace E] in
/-- A jointly smooth orbit family is continuous in the genuine derivative topology. -/
theorem continuous_derivativeFamily :
    Continuous (fun n : N => (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π).symm
      ⟨v n, isSmoothVector_family π hv n⟩) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro Xs
  simpa only [Function.comp_apply, DerivativeSmoothVectors.derivativeCoordinates_apply,
    LinearEquiv.apply_symm_apply] using continuous_iteratedLieDerivative_family π hv Xs

omit a in
/-- Compact integration is a linear map of the weight into genuine smooth vectors. -/
def weightAverageLM : C(X, ℂ) →ₗ[ℂ] DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π where
  toFun b := (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π).symm
    ⟨∫ x, b x • v (j x) ∂μ, isSmoothVector_integral π μ b j hv⟩
  map_add' b c := by
    apply (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π).injective
    apply Subtype.ext
    change (∫ x, (b + c) x • v (j x) ∂μ) =
      (∫ x, b x • v (j x) ∂μ) + (∫ x, c x • v (j x) ∂μ)
    simp only [ContinuousMap.add_apply, add_smul]
    exact integral_add (integrable_family π μ b j hv) (integrable_family π μ c j hv)
  map_smul' c b := by
    apply (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π).injective
    apply Subtype.ext
    change (∫ x, (c • b) x • v (j x) ∂μ) = c • (∫ x, b x • v (j x) ∂μ)
    simpa only [ContinuousMap.smul_apply, smul_smul, smul_eq_mul, RingHom.id_apply] using
      integral_smul c (fun x => b x • v (j x)) (μ := μ)

@[simp]
theorem derivativeCoordinates_weightAverageLM (Xs : List 𝔤) :
    DerivativeSmoothVectors.derivativeCoordinates 𝓘(ℝ, 𝔤) π
      (weightAverageLM π μ j hv a) Xs =
        ∫ x, a x • iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (v (j x)) ∂μ := by
  rw [DerivativeSmoothVectors.derivativeCoordinates_apply]
  exact iteratedLieDerivative_integral π μ a j hv Xs

omit a in
/-- Uniform approximation of compact weights gives convergence of every
genuine derivative word, hence continuity in the genuine derivative topology. -/
theorem continuous_weightAverageLM :
    Continuous (weightAverageLM π μ j hv) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro Xs
  change Continuous (fun b => DerivativeSmoothVectors.derivativeCoordinates 𝓘(ℝ, 𝔤) π
    (weightAverageLM π μ j hv b) Xs)
  simp_rw [derivativeCoordinates_weightAverageLM]
  let F : C(X, E) :=
    ⟨fun x => iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (v (j x)),
      (continuous_iteratedLieDerivative_family π hv Xs).comp j.continuous⟩
  let L : C(X, ℂ) →ₗ[ℂ] E :=
    { toFun b := ∫ x, b x • F x ∂μ
      map_add' b c := by
        simp only [ContinuousMap.add_apply, add_smul]
        exact integral_add
          ((b.continuous.smul F.continuous).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
          ((c.continuous.smul F.continuous).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
      map_smul' c b := by
        simpa only [ContinuousMap.smul_apply, smul_smul, smul_eq_mul, RingHom.id_apply] using
          integral_smul c (fun x => b x • F x) (μ := μ) }
  have hb (b : C(X, ℂ)) : ‖L b‖ ≤ (‖F‖ * μ.real Set.univ) * ‖b‖ := by
    calc
      ‖L b‖ ≤ (‖b‖ * ‖F‖) * μ.real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => by
          rw [norm_smul]
          exact mul_le_mul (b.norm_coe_le_norm x) (F.norm_coe_le_norm x)
            (norm_nonneg _) (norm_nonneg _))
      _ = (‖F‖ * μ.real Set.univ) * ‖b‖ := by ring
  exact (L.mkContinuous (‖F‖ * μ.real Set.univ) hb).continuous

omit a in
/-- The actual integral is continuous and complex linear in its compact weight. -/
def weightAverageCLM : C(X, ℂ) →L[ℂ] DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π :=
  ⟨weightAverageLM π μ j hv, continuous_weightAverageLM π μ j hv⟩

/-- The underlying vector of the continuous average is the actual Bochner integral. -/
@[simp]
theorem toSmooth_weightAverageCLM :
    (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π (weightAverageCLM π μ j hv a) : E) =
      ∫ x, a x • v (j x) ∂μ :=
  rfl

/-- Approximation by a dense set of weights takes place in the genuine
derivative topology of the averages. -/
theorem weightAverage_mem_closure_image {S : Set C(X, ℂ)} (hS : Dense S) :
    weightAverageLM π μ j hv a ∈
      closure (weightAverageLM π μ j hv '' S) :=
  mem_closure_image (continuous_weightAverageLM π μ j hv).continuousAt (hS a)

omit [FiniteDimensional ℝ 𝔤] [CompleteSpace E] in
/-- The translates of one genuine smooth vector form a jointly smooth orbit family. -/
theorem contMDiff_orbit_family {w : E} (hw : IsSmoothVector 𝓘(ℝ, 𝔤) π w) :
    ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, 𝔤)) 𝓘(ℝ, E) ∞
      (fun p : G × G => π p.1 (π p.2 w)) := by
  have h := hw.comp (contMDiff_fst.mul contMDiff_snd)
  change ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, 𝔤)) 𝓘(ℝ, E) ∞
    (fun p : G × G => π (p.1 * p.2) w) at h
  simpa only [map_mul, mul_apply_eq_comp] using h

/-- A compact weighted average of translates of a genuine smooth vector is smooth. -/
theorem isSmoothVector_orbitIntegral (r : C(X, G)) {w : E}
    (hw : IsSmoothVector 𝓘(ℝ, 𝔤) π w) :
    IsSmoothVector 𝓘(ℝ, 𝔤) π (∫ x, a x • π (r x) w ∂μ) :=
  isSmoothVector_integral π (v := fun g => π g w) μ a r (contMDiff_orbit_family π hw)

/-- Every genuine derivative word commutes with compact integration of translates. -/
theorem iteratedLieDerivative_orbitIntegral (r : C(X, G)) {w : E}
    (hw : IsSmoothVector 𝓘(ℝ, 𝔤) π w) (Xs : List 𝔤) :
    iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (∫ x, a x • π (r x) w ∂μ) =
      ∫ x, a x • iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (π (r x) w) ∂μ :=
  iteratedLieDerivative_integral π (v := fun g => π g w) μ a r
    (contMDiff_orbit_family π hw) Xs

omit a in
/-- Weighted averaging of translates of a genuine smooth vector, as a continuous
complex linear map into the genuine derivative topology. -/
def orbitAverageCLM (r : C(X, G)) {w : E} (hw : IsSmoothVector 𝓘(ℝ, 𝔤) π w) :
    C(X, ℂ) →L[ℂ] DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π :=
  weightAverageCLM π (v := fun g => π g w) μ r (contMDiff_orbit_family π hw)

/-- The underlying vector of an orbit average is the actual Bochner integral. -/
@[simp]
theorem toSmooth_orbitAverageCLM (r : C(X, G)) {w : E}
    (hw : IsSmoothVector 𝓘(ℝ, 𝔤) π w) :
    (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π (orbitAverageCLM π μ r hw a) : E) =
      ∫ x, a x • π (r x) w ∂μ :=
  rfl

/-- Every genuine derivative coordinate of an orbit average is the integral of
that derivative of the translates. -/
@[simp]
theorem derivativeCoordinates_orbitAverageCLM (r : C(X, G)) {w : E}
    (hw : IsSmoothVector 𝓘(ℝ, 𝔤) π w) (Xs : List 𝔤) :
    DerivativeSmoothVectors.derivativeCoordinates 𝓘(ℝ, 𝔤) π
      (orbitAverageCLM π μ r hw a) Xs =
        ∫ x, a x • iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (π (r x) w) ∂μ :=
  derivativeCoordinates_weightAverageLM π (v := fun g => π g w) μ a r
    (contMDiff_orbit_family π hw) Xs

/-- Approximation by a dense set of weights for averages of translates. -/
theorem orbitAverage_mem_closure_image (r : C(X, G)) {w : E}
    (hw : IsSmoothVector 𝓘(ℝ, 𝔤) π w) {S : Set C(X, ℂ)} (hS : Dense S) :
    orbitAverageCLM π μ r hw a ∈ closure (orbitAverageCLM π μ r hw '' S) :=
  mem_closure_image (orbitAverageCLM π μ r hw).continuous.continuousAt (hS a)

end Langlands.Archimedean.CompactSmoothAverage

namespace Langlands.Archimedean

universe u𝔤 uG uH uN uE uX

/-- Compact weighted averaging of a jointly smooth orbit family is a continuous
linear map into genuine smooth vectors with their full word-derivative topology. -/
def CompactSmoothAverageStatement : Prop :=
  ∀ (𝔤 : Type u𝔤) [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
    [FiniteDimensional ℝ 𝔤]
    (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace 𝔤 G]
    [LieGroup 𝓘(ℝ, 𝔤) ∞ G]
    (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (N : Type uN) [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold 𝓘(ℝ, H) ∞ N]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (π : G →* (E →L[ℂ] E)) (μ : Measure X) [IsFiniteMeasure μ]
    (j : C(X, N)) (v : N → E)
    (hv : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun p : G × N => π p.1 (v p.2))),
    (∀ Xs : List 𝔤,
      ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
        (fun p : G × N => π p.1 (iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (v p.2)))) ∧
    Continuous (fun n : N => (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π).symm
      ⟨v n, CompactSmoothAverage.isSmoothVector_family π hv n⟩) ∧
    (∀ a : C(X, ℂ), IsSmoothVector 𝓘(ℝ, 𝔤) π
      (∫ x, a x • v (j x) ∂μ)) ∧
    ∃ A : C(X, ℂ) →L[ℂ] DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π,
      (∀ a : C(X, ℂ), (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π (A a) : E) =
        ∫ x, a x • v (j x) ∂μ) ∧
      ∀ (a : C(X, ℂ)) (Xs : List 𝔤),
        DerivativeSmoothVectors.derivativeCoordinates 𝓘(ℝ, 𝔤) π (A a) Xs =
          ∫ x, a x • iteratedLieDerivative 𝓘(ℝ, 𝔤) π Xs (v (j x)) ∂μ

/-- The compact smooth averaging assertion, with the actual integral and genuine derivatives. -/
theorem compactSmoothAverage :
    CompactSmoothAverageStatement.{u𝔤,uG,uH,uN,uE,uX} := by
  intro 𝔤 _ _ _ G _ _ _ _ H _ _ N _ _ _ E _ _ _ X _ _ _ _ π μ _ j v hv
  refine ⟨CompactSmoothAverage.contMDiff_orbit_iteratedLieDerivative π hv,
    CompactSmoothAverage.continuous_derivativeFamily π hv,
    fun a => CompactSmoothAverage.isSmoothVector_integral π μ a j hv,
    CompactSmoothAverage.weightAverageCLM π μ j hv, fun a => rfl, ?_⟩
  exact fun a Xs => CompactSmoothAverage.derivativeCoordinates_weightAverageLM π μ a j hv Xs

end Langlands.Archimedean
