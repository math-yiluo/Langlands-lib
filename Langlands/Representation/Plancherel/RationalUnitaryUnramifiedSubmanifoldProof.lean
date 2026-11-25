import Langlands.Representation.Plancherel.RationalUnramifiedComplexTorusStatement
import Langlands.Representation.Plancherel.RationalUnitaryUnramifiedBasis
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # The real torus of unitary unramified characters (Renard V.3.20) -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Function Set Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped Manifold ContDiff CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

section TorusCharts

variable {κ : Type*} [Fintype κ]

/-- Real coordinates for the ambient model, with the angle coordinate first. -/
private def angleAndReal : ((κ → ℝ) × (κ → ℝ)) ≃L[ℝ] (κ → ℂ) where
  toFun p i := Complex.equivRealProdCLM.symm (p.2 i, p.1 i)
  invFun z := (fun i => (z i).im, fun i => (z i).re)
  left_inv p := by
    rcases p with ⟨t, r⟩
    simp [Complex.equivRealProdCLM_symm_apply]
  right_inv z := by
    ext i
    exact Complex.equivRealProdCLM.symm_apply_apply (z i)
  map_add' p q := by
    funext i
    exact Complex.equivRealProdCLM.symm.map_add (p.2 i, p.1 i) (q.2 i, q.1 i)
  map_smul' a p := by
    funext i
    exact Complex.equivRealProdCLM.symm.map_smul a (p.2 i, p.1 i)
  continuous_toFun := continuous_pi fun i =>
    Complex.equivRealProdCLM.symm.continuous.comp (by fun_prop)
  continuous_invFun := (continuous_pi fun _ => by fun_prop).prodMk
    (continuous_pi fun _ => by fun_prop)

private def imaginary (t : κ → ℝ) : (κ → ℂ) := angleAndReal (t, 0)

omit [Fintype κ] in
private theorem imaginary_apply (t : κ → ℝ) (i : κ) :
    imaginary t i = (t i : ℂ) * Complex.I := by
  simp [imaginary, angleAndReal, Complex.equivRealProdCLM_symm_apply]

private theorem contDiff_imaginary : ContDiff ℝ ∞ (imaginary : (κ → ℝ) → (κ → ℂ)) :=
  (angleAndReal (κ := κ)).contDiff.comp
    ((contDiff_id (E := κ → ℝ)).prodMk (contDiff_const (c := (0 : κ → ℝ))))

private def anglePart (z : κ → ℂ) : (κ → ℝ) := fun i => (z i).im

private theorem contDiff_anglePart : ContDiff ℝ ∞ (anglePart : (κ → ℂ) → (κ → ℝ)) := by
  rw [contDiff_pi]
  intro i
  exact Complex.imCLM.contDiff.comp (contDiff_apply ℝ (fun _ ↦ ℂ) i)

/-- The finite product of principal logarithms after division by the center. -/
private def logarithmChart (c : κ → ℂ) (hc : ∀ i, c i ≠ 0) : OpenPartialHomeomorph (κ → ℂ) (κ → ℂ) :=
  OpenPartialHomeomorph.pi fun i =>
    (Homeomorph.mulLeft₀ (c i) (hc i)).symm.transOpenPartialHomeomorph
      Complex.expOpenPartialHomeomorph.symm

private theorem logarithmChart_apply (c : κ → ℂ) (hc : ∀ i, c i ≠ 0) (z : κ → ℂ) (i : κ) :
    logarithmChart c hc z i = Complex.log ((c i)⁻¹ * z i) := rfl

private theorem logarithmChart_symm_apply (c : κ → ℂ) (hc : ∀ i, c i ≠ 0) (z : κ → ℂ) (i : κ) :
    (logarithmChart c hc).symm z i = c i * Complex.exp (z i) := rfl

private theorem logarithmChart_mem_source (c : κ → ℂ) (hc : ∀ i, c i ≠ 0) :
    c ∈ (logarithmChart c hc).source := by
  intro i _
  change (c i)⁻¹ * c i ∈ Complex.slitPlane
  rw [inv_mul_cancel₀ (hc i)]
  exact Complex.one_mem_slitPlane

private theorem logarithmChart_zero_mem_target (c : κ → ℂ) (hc : ∀ i, c i ≠ 0) :
    0 ∈ (logarithmChart c hc).target := by
  intro i _
  change -(Real.pi) < (0 : ℂ).im ∧ (0 : ℂ).im < Real.pi
  simp [Real.pi_pos]

private theorem contDiffOn_logarithmChart (c : κ → ℂ) (hc : ∀ i, c i ≠ 0) :
    ContDiffOn ℝ ∞ (logarithmChart c hc) (logarithmChart c hc).source := by
  rw [contDiffOn_pi]
  intro i
  simp only [logarithmChart_apply]
  have hlog : ContDiffOn ℝ ∞ Complex.log Complex.slitPlane := fun z hz =>
    ((Complex.contDiffAt_log hz).restrict_scalars ℝ).contDiffWithinAt
  exact hlog.comp ((contDiff_const.mul (contDiff_apply ℝ (fun _ ↦ ℂ) i)).contDiffOn)
    (fun _ hz => hz i (mem_univ i))

private theorem contDiff_logarithmChart_symm (c : κ → ℂ) (hc : ∀ i, c i ≠ 0) :
    ContDiff ℝ ∞ (logarithmChart c hc).symm := by
  rw [contDiff_pi]
  intro i
  simp only [logarithmChart_symm_apply]
  exact contDiff_const.mul ((Complex.contDiff_exp (𝕜 := ℝ)).comp (contDiff_apply ℝ (fun _ ↦ ℂ) i))

variable {U : Type*} [Group U] [TopologicalSpace U]
variable (coord : U →* (κ → ℂ)) (hcoord : IsEmbedding coord) (hnorm : ∀ x i, ‖coord x i‖ = 1)
variable (phase : (κ → ℝ) → U) (hphase : ∀ t i, coord (phase t) i = Complex.exp (imaginary t i))

include hnorm in
omit [Fintype κ] [TopologicalSpace U] in
private theorem coord_ne_zero (x : U) (i : κ) : coord x i ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [hnorm]; exact one_ne_zero)

local notation "logAt(" x ")" => logarithmChart (coord x) (coord_ne_zero coord hnorm x)

include hphase in
omit [TopologicalSpace U] in
private theorem coord_mul_phase (x : U) (t : κ → ℝ) :
    coord (x * phase t) = (logAt(x)).symm (imaginary t) := by
  funext i
  rw [map_mul, Pi.mul_apply, hphase, logarithmChart_symm_apply]

omit [TopologicalSpace U] in
private theorem imaginary_logarithmChart (x y : U) :
    imaginary (anglePart (logAt(x) (coord y))) = logAt(x) (coord y) := by
  funext i
  rw [imaginary_apply]
  apply Complex.ext
  · simp [logarithmChart_apply, Complex.log_re, hnorm]
  · simp [anglePart]

/-- Restrict the logarithm chart to the unitary group and keep the angle coordinates. -/
private def unitaryAngleChart (x : U) : OpenPartialHomeomorph U (κ → ℝ) where
  toFun y := anglePart (logAt(x) (coord y))
  invFun t := x * phase t
  source := coord ⁻¹' (logAt(x)).source
  target := imaginary ⁻¹' (logAt(x)).target
  map_source' y hy := by
    rw [mem_preimage, imaginary_logarithmChart coord hnorm]
    exact (logAt(x)).map_source hy
  map_target' t ht := by
    rw [mem_preimage, coord_mul_phase coord hnorm phase hphase]
    exact (logAt(x)).map_target ht
  left_inv' y hy := hcoord.injective <| by
    rw [coord_mul_phase coord hnorm phase hphase, imaginary_logarithmChart coord hnorm]
    exact (logAt(x)).left_inv hy
  right_inv' t ht := by
    rw [coord_mul_phase coord hnorm phase hphase, (logAt(x)).right_inv ht]
    funext i
    simp [anglePart, imaginary_apply]
  open_source := (logAt(x)).open_source.preimage hcoord.continuous
  open_target := (logAt(x)).open_target.preimage contDiff_imaginary.continuous
  continuousOn_toFun := contDiff_anglePart.continuous.comp_continuousOn <|
    (logAt(x)).continuousOn.comp hcoord.continuous.continuousOn fun _ => id
  continuousOn_invFun := hcoord.isInducing.continuousOn_iff.mpr <| by
    change ContinuousOn (fun t => coord (x * phase t)) _
    simp_rw [coord_mul_phase coord hnorm phase hphase]
    exact ((contDiff_logarithmChart_symm _ _).comp contDiff_imaginary).continuous.continuousOn

local notation "angleAt" => unitaryAngleChart coord hcoord hnorm phase hphase

@[instance_reducible]
private def unitaryAngleChartedSpace : ChartedSpace (κ → ℝ) U where
  atlas := range angleAt
  chartAt := angleAt
  mem_chart_source x := logarithmChart_mem_source (coord x) _
  chart_mem_atlas x := mem_range_self x

local notation "angleSpace" => unitaryAngleChartedSpace coord hcoord hnorm phase hphase

private theorem unitaryAngleIsManifold :
    letI := angleSpace
    IsManifold 𝓘(ℝ, κ → ℝ) ∞ U := by
  let _ : ChartedSpace (κ → ℝ) U := angleSpace
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id,
    range_id, inter_univ, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    preimage_id_eq]
  change ContDiffOn ℝ ∞ (fun t => anglePart (logAt(y) (coord (x * phase t))))
    ((angleAt x).target ∩ (angleAt x).symm ⁻¹' (angleAt y).source)
  simp_rw [coord_mul_phase coord hnorm phase hphase]
  exact contDiff_anglePart.comp_contDiffOn <|
    (contDiffOn_logarithmChart _ _).comp
      (((contDiff_logarithmChart_symm _ _).comp contDiff_imaginary).contDiffOn)
      (fun t ht => by
        rw [← coord_mul_phase coord hnorm phase hphase]
        exact ht.2)

private theorem contMDiff_torusCoord :
    letI := angleSpace
    ContMDiff 𝓘(ℝ, κ → ℝ) 𝓘(ℝ, κ → ℂ) ∞ coord := by
  let _ : ChartedSpace (κ → ℝ) U := angleSpace
  have : IsManifold 𝓘(ℝ, κ → ℝ) ∞ U :=
    unitaryAngleIsManifold coord hcoord hnorm phase hphase
  rw [contMDiff_iff]
  refine ⟨hcoord.continuous, fun x y => ?_⟩
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_comp]
  change ContDiffOn ℝ ∞ (fun t => coord (x * phase t)) _
  simp_rw [coord_mul_phase coord hnorm phase hphase]
  exact ((contDiff_logarithmChart_symm _ _).comp contDiff_imaginary).contDiffOn

private theorem contMDiff_of_torusCoord
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {f : M → U} (hf : ContMDiff I 𝓘(ℝ, κ → ℂ) ∞ (coord ∘ f)) :
    letI := angleSpace
    ContMDiff I 𝓘(ℝ, κ → ℝ) ∞ f := by
  let _ : ChartedSpace (κ → ℝ) U := angleSpace
  have : IsManifold 𝓘(ℝ, κ → ℝ) ∞ U :=
    unitaryAngleIsManifold coord hcoord hnorm phase hphase
  rw [contMDiff_iff_target]
  refine ⟨hcoord.isInducing.continuous_iff.mpr hf.continuous, fun x => ?_⟩
  simp only [extChartAt_coe, extChartAt_source, modelWithCornersSelf_coe, id_comp]
  change ContMDiffOn I 𝓘(ℝ, κ → ℝ) ∞
    (fun y => anglePart (logAt(x) (coord (f y)))) ((coord ∘ f) ⁻¹' (logAt(x)).source)
  exact contDiff_anglePart.contMDiff.comp_contMDiffOn <|
    (contDiffOn_logarithmChart _ _).contMDiffOn.comp hf.contMDiffOn fun _ => id

private theorem unitaryAngleLieGroup :
    letI := angleSpace
    LieGroup 𝓘(ℝ, κ → ℝ) ∞ U := by
  let _ : ChartedSpace (κ → ℝ) U := angleSpace
  have : IsManifold 𝓘(ℝ, κ → ℝ) ∞ U :=
    unitaryAngleIsManifold coord hcoord hnorm phase hphase
  have h : ContMDiff 𝓘(ℝ, κ → ℝ) 𝓘(ℝ, κ → ℂ) ∞ coord :=
    contMDiff_torusCoord coord hcoord hnorm phase hphase
  change LieGroup 𝓘(ℝ, κ → ℝ) ∞ U
  refine { contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · apply contMDiff_of_torusCoord coord hcoord hnorm phase hphase
    apply contMDiff_pi_space.mpr
    intro i
    have h₁ := h.comp (contMDiff_fst (M := U) (N := U) (J := 𝓘(ℝ, κ → ℝ)))
    have h₂ := h.comp (contMDiff_snd (M := U) (N := U) (I := 𝓘(ℝ, κ → ℝ)))
    have hmul : ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 * p.2) := contDiff_mul
    simpa only [Function.comp_def, map_mul, Pi.mul_apply] using
      hmul.contMDiff.comp ((contMDiff_pi_space.mp h₁ i).prodMk_space
        (contMDiff_pi_space.mp h₂ i))
  · apply contMDiff_of_torusCoord coord hcoord hnorm phase hphase
    apply contMDiff_pi_space.mpr
    intro i
    have hinv (x : U) : coord x⁻¹ i = (coord x i)⁻¹ := by
      have hm := congrFun (coord.map_mul x x⁻¹) i
      rw [mul_inv_cancel, map_one, Pi.mul_apply, Pi.one_apply] at hm
      have hx := coord_ne_zero coord hnorm x i
      exact mul_left_cancel₀ hx (hm.symm.trans (mul_inv_cancel₀ hx).symm)
    simpa only [Function.comp_def, hinv, Complex.inv_eq_conj (hnorm _ _),
      Complex.conjCLE_apply] using
      Complex.conjCLE.contDiff.contMDiff.comp (contMDiff_pi_space.mp h i)

include hcoord hphase in
omit [Fintype κ] in
private theorem phase_map_add (r t : κ → ℝ) : phase (r + t) = phase r * phase t := by
  apply hcoord.injective
  funext i
  simp only [hphase, map_mul, Pi.mul_apply, ← Complex.exp_add, imaginary_apply,
    Pi.add_apply, Complex.ofReal_add, add_mul]

private theorem isLocalDiffeomorph_phase :
    letI := angleSpace
    IsLocalDiffeomorph 𝓘(ℝ, κ → ℝ) 𝓘(ℝ, κ → ℝ) ∞ phase := by
  let _ : ChartedSpace (κ → ℝ) U := angleSpace
  have : IsManifold 𝓘(ℝ, κ → ℝ) ∞ U :=
    unitaryAngleIsManifold coord hcoord hnorm phase hphase
  change IsLocalDiffeomorph 𝓘(ℝ, κ → ℝ) 𝓘(ℝ, κ → ℝ) ∞ phase
  intro t
  let x := phase t
  let trans := Homeomorph.subRight t
  let localExp := trans.transOpenPartialHomeomorph (angleAt x).symm
  have hchart : angleAt x ∈ IsManifold.maximalAtlas 𝓘(ℝ, κ → ℝ) ∞ U :=
    IsManifold.chart_mem_maximalAtlas x
  refine ⟨{ __ := localExp, contMDiffOn_toFun := ?_, contMDiffOn_invFun := ?_ }, ?_, ?_⟩
  · have hsub : ContDiff ℝ ∞ (fun s : κ → ℝ => s - t) := contDiff_id.sub contDiff_const
    exact (contMDiffOn_symm_of_mem_maximalAtlas hchart).comp
      hsub.contMDiff.contMDiffOn (fun _ hs => hs)
  · have hadd : ContDiff ℝ ∞ (fun s : κ → ℝ => s + t) := contDiff_id.add contDiff_const
    exact hadd.contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas hchart)
  · change imaginary (t - t) ∈ (logAt(x)).target
    rw [sub_self, show imaginary (0 : κ → ℝ) = 0 by
      funext i
      simp [imaginary_apply]]
    exact logarithmChart_zero_mem_target _ _
  · intro s _
    change phase s = phase t * phase (s - t)
    rw [← phase_map_add coord hcoord phase hphase, show t + (s - t) = s by abel]

private theorem unitaryAngleSmoothEmbedding {A : Type*} [TopologicalSpace A] [Nonempty A]
    {ambient : A → κ → ℂ} (hambient : IsOpenEmbedding ambient)
    {incl : U → A} (hincl : IsEmbedding incl) (hcomp : ambient ∘ incl = coord) :
    letI := angleSpace
    letI := hambient.singletonChartedSpace
    Manifold.IsSmoothEmbedding 𝓘(ℝ, κ → ℝ) 𝓘(ℝ, κ → ℂ) ∞ incl := by
  let _ : ChartedSpace (κ → ℝ) U := angleSpace
  let _ : ChartedSpace (κ → ℂ) A := hambient.singletonChartedSpace
  have : IsManifold 𝓘(ℝ, κ → ℝ) ∞ U :=
    unitaryAngleIsManifold coord hcoord hnorm phase hphase
  have : IsManifold 𝓘(ℝ, κ → ℂ) ∞ A := hambient.isManifold_singleton
  refine ⟨?_, hincl⟩
  apply Manifold.IsImmersionOfComplement.isImmersion (F := κ → ℝ)
  intro x
  let globalChart := hambient.toOpenPartialHomeomorph ambient
  let complexChart := globalChart.trans (logAt(x))
  have hglobal : globalChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, κ → ℂ) ∞ A :=
    IsManifold.chart_mem_maximalAtlas (incl x)
  have hcomplex : complexChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, κ → ℂ) ∞ A := by
    apply complexChart.mem_maximalAtlas_of_contMDiffOn
    · exact (contDiffOn_logarithmChart _ _).contMDiffOn.comp
        ((contMDiffOn_of_mem_maximalAtlas hglobal).mono inter_subset_left) inter_subset_right
    · exact (contMDiffOn_symm_of_mem_maximalAtlas hglobal).comp
        ((contDiff_logarithmChart_symm _ _).contMDiff.contMDiffOn.mono inter_subset_left)
        inter_subset_right
  have hcomp_apply (y : U) : ambient (incl y) = coord y := congrFun hcomp y
  have hsource : MapsTo incl (angleAt x).source complexChart.source := by
    intro y hy
    change incl y ∈ globalChart.source ∧ ambient (incl y) ∈ (logAt(x)).source
    refine ⟨by simp [globalChart], ?_⟩
    rw [hcomp_apply y]
    exact hy
  have hx : x ∈ (angleAt x).source := logarithmChart_mem_source _ _
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts angleAndReal (angleAt x) complexChart
    hx (hsource hx) (IsManifold.chart_mem_maximalAtlas x) hcomplex hsource ?_
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    OpenPartialHomeomorph.extend_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    id_comp, comp_id, preimage_id_eq, range_id, inter_univ]
  intro t ht
  change logAt(x) (ambient (incl (x * phase t))) = imaginary t
  rw [hcomp_apply, coord_mul_phase coord hnorm phase hphase]
  exact (logAt(x)).right_inv ht

end TorusCharts

/-- In basis coordinates, the unitary unramified subgroup is an embedded real Lie group
and the imaginary exponential is a local diffeomorphism onto it. -/
theorem rationalUnitaryUnramifiedSubmanifold :
    RationalUnitaryUnramifiedSubmanifoldStatement.{u} := by
  intro F _ _ _ _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  let _ : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro b
  let a : ℝ := -Real.log (LocalField.residueCardinality F : ℝ)
  have ha : a ≠ 0 := rationalImaginaryExponentialScale_ne_zero F
  let coord := rationalUnitaryUnramifiedBasisCoordinateHom G b
  have hcoord : IsEmbedding coord := isEmbedding_rationalUnitaryUnramifiedBasisCoordinateHom G b
  have hnorm : ∀ x i, ‖coord x i‖ = 1 := rationalUnitaryUnramifiedBasisCoordinateHom_norm G b
  let e := rationalUnitaryBasisExponential G b
  let phase := fun t : Fin (rationalImageRank G) → ℝ => e (a⁻¹ • t)
  have hphase (t : Fin (rationalImageRank G) → ℝ) (i : Fin (rationalImageRank G)) :
      coord (phase t) i = Complex.exp (imaginary t i) := by
    dsimp only [coord, phase, e]
    rw [rationalUnitaryBasisExponential_coordinates, imaginary_apply]
    change Complex.exp (((a * (a⁻¹ * t i) : ℝ) : ℂ) * Complex.I) = _
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  let chart := unitaryAngleChartedSpace coord hcoord hnorm phase hphase
  refine ⟨chart, unitaryAngleLieGroup coord hcoord hnorm phase hphase, ?_,
    e, rationalUnitaryBasisExponential_inclusion G b, ?_⟩
  · exact unitaryAngleSmoothEmbedding coord hcoord hnorm phase hphase
      (isOpenEmbedding_rationalUnramifiedBasisCoordinates G b)
      (isEmbedding_rationalUnitaryUnramifiedInclusion G) rfl
  · let scale : (Fin (rationalImageRank G) → ℝ) ≃ₘ[ℝ] (Fin (rationalImageRank G) → ℝ) :=
      { toEquiv := (Homeomorph.smulOfNeZero a ha).toEquiv
        contMDiff_toFun := (contDiff_const_smul a).contMDiff
        contMDiff_invFun := (contDiff_const_smul a⁻¹).contMDiff }
    have hcomp : phase ∘ scale = e := by
      funext t
      change e (a⁻¹ • (a • t)) = e t
      rw [inv_smul_smul₀ ha]
    rw [← hcomp]
    have hlocal := isLocalDiffeomorph_phase coord hcoord hnorm phase hphase
    intro t
    exact IsLocalDiffeomorphAt.comp 𝓘(ℝ, Fin (rationalImageRank G) → ℝ) _
      (scale.isLocalDiffeomorph t) (hlocal (scale t))

end Langlands.Plancherel
