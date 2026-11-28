import Langlands.Analysis.TraceNormalizedKernelExtreme
import Langlands.Representation.Unitary.TemperedComponentAlgebra

/-! # The unitary representation of a cone element over the left ideal

Let `𝒜 = algebra μ π hπ` be the closed `*`-algebra of the integrated test operators of a unitary
representation `π`, and `F` a cone element (`Langlands.Analysis.KernelCone.IsConeElement`) over
`𝒜`. Restricting the kernel of `F` to the indices `(x, k, w)` with `x` in the left ideal
`leftIdeal μ π hπ` gives a Hilbert space `V`, isometrically embedded in the Hilbert space of `F`.
Left multiplication by `π(g)` on the left ideal defines a unitary, jointly continuous
representation `σ` of `G` on `V`, whose integrated operators are left multiplications by `π(φ)`.
For strictly positive weights `c` and a nonzero extreme point `F` of the compact set
`coneSet Rel c e`, `σ` is topologically irreducible whenever `V ≠ 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Analysis.TemperedComponent

open Langlands.Archimedean Langlands.Analysis.KernelCone

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {π : G →* (H →L[ℂ] H)} {hπ : IsContinuousRepresentation π}
variable {κ : Type*} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
variable {Rel : Set (κ × algebra μ π hπ × κ × (W →L[ℂ] W))}
variable {F : Coord (algebra μ π hπ) κ W → ℂ}

/-- The inclusion of the left-ideal indices. -/
def inclL (i : leftIdeal μ π hπ × κ × W) : algebra μ π hπ × κ × W :=
  (⟨i.1, leftIdeal_le_algebra π hπ i.1.2⟩, i.2)

variable (hF : IsConeElement Rel F)

/-- The kernel of `F` restricted to the left-ideal indices. -/
def kernelL : PositiveKernel (leftIdeal μ π hπ × κ × W) where
  toFun i j := kernelOf F (inclL i) (inclL j)
  conj_symm' i j := (kernel hF).conj_symm' _ _
  re_nonneg' f := by
    have h := (kernel hF).re_form_self_nonneg (Finsupp.mapDomain inclL f)
    rwa [(kernel hF).form_mapDomain] at h

/-- The Hilbert space over the left ideal. -/
abbrev VL : Type _ := (kernelL hF).Space

/-- The vector of a left-ideal index. -/
def vecL' (x : leftIdeal μ π hπ) (k : κ) (w : W) : VL hF := (kernelL hF).vec (x, k, w)

/-- The isometric embedding into the Hilbert space of `F`. -/
def iotaL : VL hF →ₗᵢ[ℂ] Space hF :=
  (kernelL hF).isometryOfMap (kernel hF) inclL fun _ _ => rfl

theorem iotaL_vec (x : leftIdeal μ π hπ) (k : κ) (w : W) :
    iotaL hF (vecL' hF x k w) = vec hF ⟨x, leftIdeal_le_algebra π hπ x.2⟩ k w :=
  (kernelL hF).isometryOfMap_vec (kernel hF) _ _ _

theorem iotaL_injective : Function.Injective (iotaL hF) := (iotaL hF).injective

theorem inner_vecL' (x : leftIdeal μ π hπ) (k : κ) (w : W) (y : leftIdeal μ π hπ) (k' : κ)
    (w' : W) :
    ⟪vecL' hF x k w, vecL' hF y k' w'⟫_ℂ =
      F (k, k', star (⟨x, leftIdeal_le_algebra π hπ x.2⟩ : algebra μ π hπ) *
        ⟨y, leftIdeal_le_algebra π hπ y.2⟩, w, w') :=
  (kernelL hF).inner_vec_vec _ _

theorem extL {u v : VL hF} (h : ∀ y k' w', ⟪u, vecL' hF y k' w'⟫_ℂ = ⟪v, vecL' hF y k' w'⟫_ℂ) :
    u = v :=
  (kernelL hF).ext_inner_vec fun j => h j.1 j.2.1 j.2.2

theorem clm_extL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A B : VL hF →L[ℂ] E} (h : ∀ x k w, A (vecL' hF x k w) = B (vecL' hF x k w)) : A = B :=
  (kernelL hF).clm_ext_vec fun i => h i.1 i.2.1 i.2.2

theorem vecL'_add (x y : leftIdeal μ π hπ) (k : κ) (w : W) :
    vecL' hF (x + y) k w = vecL' hF x k w + vecL' hF y k w := by
  apply iotaL_injective hF
  rw [map_add, iotaL_vec, iotaL_vec, iotaL_vec, ← vec_add]
  rfl

theorem vecL'_smul (r : ℂ) (x : leftIdeal μ π hπ) (k : κ) (w : W) :
    vecL' hF (r • x) k w = r • vecL' hF x k w := by
  apply iotaL_injective hF
  rw [map_smul, iotaL_vec, iotaL_vec, ← vec_smul]
  rfl

theorem norm_vecL'_le (x : leftIdeal μ π hπ) (k : κ) (w : W) :
    ‖vecL' hF x k w‖ ≤ ‖x‖ * ‖vec hF 1 k w‖ := by
  rw [← (iotaL hF).norm_map, iotaL_vec]
  have h : vec hF ⟨x, leftIdeal_le_algebra π hπ x.2⟩ k w =
      rho hF ⟨x, leftIdeal_le_algebra π hπ x.2⟩ (vec hF 1 k w) := by rw [rho_vec, mul_one]
  rw [h]
  exact ((rho hF _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (norm_rho_le hF _)
    (norm_nonneg _))

/-- The bounded linear map `x ↦ vecL' x k w` on the left ideal. -/
def lambdaL (k : κ) (w : W) : leftIdeal μ π hπ →L[ℂ] VL hF :=
  LinearMap.mkContinuous
    { toFun := fun x => vecL' hF x k w
      map_add' := fun x y => vecL'_add hF x y k w
      map_smul' := fun r x => vecL'_smul hF r x k w }
    ‖vec hF 1 k w‖ fun x => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [mul_comm]
      exact norm_vecL'_le hF x k w

@[simp]
theorem lambdaL_apply (k : κ) (w : W) (x : leftIdeal μ π hπ) :
    lambdaL hF k w x = vecL' hF x k w := rfl

/-! ### The representation -/

variable (hπu : ∀ g, π g ∈ unitary (H →L[ℂ] H))
include hπu

/-- Left multiplication by `π(g)` on left-ideal indices. -/
def repIdx (g : G) (i : leftIdeal μ π hπ × κ × W) : leftIdeal μ π hπ × κ × W :=
  (⟨π g * i.1, rep_mul_mem_leftIdeal π hπ hπu g i.1.2⟩, i.2)

theorem star_rep_mul_rep (g : G) : star (π g) * π g = 1 := (Unitary.mem_iff.mp (hπu g)).1

/-- The operator `σ(g)`. -/
def sigmaOp (g : G) : VL hF →L[ℂ] VL hF :=
  ((kernelL hF).isometryOfMap (kernelL hF) (repIdx hπu g) fun i j => by
    show F (pt (inclL (repIdx hπu g i)) (inclL (repIdx hπu g j))) = F (pt (inclL i) (inclL j))
    congr 1
    simp only [pt, inclL, repIdx, Prod.mk.injEq, true_and, and_true]
    apply Subtype.ext
    change star (π g * (i.1 : H →L[ℂ] H)) * (π g * j.1) = star (i.1 : H →L[ℂ] H) * j.1
    rw [star_mul, mul_assoc, ← mul_assoc (star (π g)), star_rep_mul_rep hπu, one_mul]
    ).toContinuousLinearMap

theorem sigmaOp_vec (g : G) (x : leftIdeal μ π hπ) (k : κ) (w : W) :
    sigmaOp hF hπu g (vecL' hF x k w) =
      vecL' hF ⟨π g * x, rep_mul_mem_leftIdeal π hπ hπu g x.2⟩ k w :=
  (kernelL hF).isometryOfMap_vec (kernelL hF) _ _ _

theorem norm_sigmaOp_apply (g : G) (v : VL hF) : ‖sigmaOp hF hπu g v‖ = ‖v‖ :=
  LinearIsometry.norm_map _ v

/-- The representation `σ` of `G` on `VL hF`. -/
def sigma : G →* (VL hF →L[ℂ] VL hF) where
  toFun := sigmaOp hF hπu
  map_one' := by
    refine clm_extL hF fun x k w => ?_
    rw [sigmaOp_vec, one_apply_eq_self]
    congr 1
    exact Subtype.ext (by simp)
  map_mul' g h := by
    refine clm_extL hF fun x k w => ?_
    rw [mul_apply_eq_comp, sigmaOp_vec, sigmaOp_vec, sigmaOp_vec]
    congr 1
    exact Subtype.ext (by simp [mul_assoc])

theorem sigma_vec (g : G) (x : leftIdeal μ π hπ) (k : κ) (w : W) :
    sigma hF hπu g (vecL' hF x k w) =
      vecL' hF ⟨π g * x, rep_mul_mem_leftIdeal π hπ hπu g x.2⟩ k w :=
  sigmaOp_vec hF hπu g x k w

theorem norm_sigma_apply (g : G) (v : VL hF) : ‖sigma hF hπu g v‖ = ‖v‖ :=
  norm_sigmaOp_apply hF hπu g v

theorem norm_sigma_le (g : G) : ‖sigma hF hπu g‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [norm_sigma_apply, one_mul]

theorem sigma_mem_unitary (g : G) : sigma hF hπu g ∈ unitary (VL hF →L[ℂ] VL hF) := by
  have h1 : star (sigma hF hπu g) * sigma hF hπu g = 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
    exact (sigma hF hπu g).norm_map_iff_adjoint_comp_self.mp (norm_sigma_apply hF hπu g)
  have h2 : star (sigma hF hπu g) = sigma hF hπu g⁻¹ := by
    calc star (sigma hF hπu g) = star (sigma hF hπu g) * (sigma hF hπu g * sigma hF hπu g⁻¹) := by
          rw [← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = sigma hF hπu g⁻¹ := by rw [← mul_assoc, h1, one_mul]
  refine Unitary.mem_iff.mpr ⟨h1, ?_⟩
  rw [h2, ← map_mul, mul_inv_cancel, map_one]

theorem continuous_sigma_vec (x : leftIdeal μ π hπ) (k : κ) (w : W) :
    Continuous fun g => sigma hF hπu g (vecL' hF x k w) := by
  simp only [sigma_vec]
  have hc : Continuous fun g => (⟨π g * x, rep_mul_mem_leftIdeal π hπ hπu g x.2⟩ :
      leftIdeal μ π hπ) :=
    (continuous_rep_mul π hπ hπu x.2).subtype_mk _
  exact (lambdaL hF k w).continuous.comp hc

omit hπu in
/-- A representation by contractions that is strongly continuous on a set with dense span is
jointly continuous. -/
theorem isContinuousRepresentation_of_dense {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (σ' : G →* (E →L[ℂ] E)) (hle : ∀ g, ‖σ' g‖ ≤ 1) (S : Set E)
    (hS : Dense (Submodule.span ℂ S : Set E)) (hcont : ∀ v ∈ S, Continuous fun g => σ' g v) :
    IsContinuousRepresentation σ' := by
  have hspan : ∀ v ∈ Submodule.span ℂ S, Continuous fun g => σ' g v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hcont v hv
    | zero => simp only [map_zero]; exact continuous_const
    | add v u _ _ hv hu => simp only [map_add]; exact hv.add hu
    | smul a v _ hv => simp only [map_smul]; exact hv.const_smul a
  have hall : ∀ v : E, Continuous fun g => σ' g v := by
    intro v
    refine continuous_of_uniform_approx_of_continuous fun U hU => ?_
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
    obtain ⟨u, hu, huv⟩ := Metric.mem_closure_iff.mp (hS.closure_eq ▸ Set.mem_univ v) ε hε
    refine ⟨fun g => σ' g u, hspan u hu, fun g => hεU ?_⟩
    calc dist (σ' g v) (σ' g u) = ‖σ' g (v - u)‖ := by rw [dist_eq_norm, map_sub]
      _ ≤ ‖σ' g‖ * ‖v - u‖ := (σ' g).le_opNorm _
      _ ≤ 1 * ‖v - u‖ := mul_le_mul_of_nonneg_right (hle g) (norm_nonneg _)
      _ < ε := by rw [one_mul, ← dist_eq_norm]; exact huv
  unfold IsContinuousRepresentation
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, v₀⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun p : G × E => ‖p.2 - v₀‖) (𝓝 (g₀, v₀)) (𝓝 0) := by
    have := ((continuous_snd.sub (continuous_const (y := v₀))).norm (E := E)).tendsto (g₀, v₀)
    simpa using this
  have h2 : Tendsto (fun p : G × E => ‖σ' p.1 v₀ - σ' g₀ v₀‖) (𝓝 (g₀, v₀)) (𝓝 0) := by
    have := ((((hall v₀).comp continuous_fst).sub
      (continuous_const (y := σ' g₀ v₀))).norm (E := E)).tendsto (g₀, v₀)
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun p => ?_) (by simpa using h1.add h2)
  calc ‖σ' p.1 p.2 - σ' g₀ v₀‖ = ‖σ' p.1 (p.2 - v₀) + (σ' p.1 v₀ - σ' g₀ v₀)‖ := by
        rw [map_sub]; abel_nf
    _ ≤ ‖σ' p.1 (p.2 - v₀)‖ + ‖σ' p.1 v₀ - σ' g₀ v₀‖ := norm_add_le _ _
    _ ≤ ‖p.2 - v₀‖ + ‖σ' p.1 v₀ - σ' g₀ v₀‖ := by
        refine add_le_add_left (((σ' p.1).le_opNorm _).trans ?_) _
        simpa using mul_le_mul_of_nonneg_right (hle p.1) (norm_nonneg (p.2 - v₀))

theorem isContinuousRepresentation_sigma : IsContinuousRepresentation (sigma hF hπu) := by
  refine isContinuousRepresentation_of_dense _ (norm_sigma_le hF hπu)
    (Set.range fun i : leftIdeal μ π hπ × κ × W => vecL' hF i.1 i.2.1 i.2.2) ?_ ?_
  · exact (kernelL hF).dense_span_vec
  · rintro _ ⟨i, rfl⟩
    exact continuous_sigma_vec hF hπu i.1 i.2.1 i.2.2

/-! ### Left multiplication by the algebra -/

/-- Left multiplication by `c ∈ algebra` on left-ideal indices. -/
def mulIdx (c : algebra μ π hπ) (i : leftIdeal μ π hπ × κ × W) : leftIdeal μ π hπ × κ × W :=
  (⟨(c : H →L[ℂ] H) * i.1, algebra_mul_mem_leftIdeal π hπ hπu c.2 i.1.2⟩, i.2)

/-- The operator `ρ(c)` of left multiplication on `VL hF`. -/
def rhoL (c : algebra μ π hπ) : VL hF →L[ℂ] VL hF :=
  (kernelL hF).opOfMap (kernelL hF) (mulIdx hπu c) ‖c‖ (norm_nonneg _) fun f => by
    have e : (fun i j => (kernelL hF) (mulIdx hπu c i) (mulIdx hπu c j)) =
        fun i j => kernelOf F (lmul c (inclL i)) (lmul c (inclL j)) := rfl
    rw [e, ← kernelForm_mapDomain (fun i j => kernelOf F (lmul c i) (lmul c j))]
    refine (hF.mul_le c _).trans (le_of_eq ?_)
    rw [kernelForm_mapDomain]
    rfl

theorem rhoL_vec (c : algebra μ π hπ) (x : leftIdeal μ π hπ) (k : κ) (w : W) :
    rhoL hF hπu c (vecL' hF x k w) =
      vecL' hF ⟨(c : H →L[ℂ] H) * x, algebra_mul_mem_leftIdeal π hπ hπu c.2 x.2⟩ k w :=
  (kernelL hF).opOfMap_vec (kernelL hF) _ _ _ _ _

theorem norm_rhoL_le (c : algebra μ π hπ) : ‖rhoL hF hπu c‖ ≤ ‖c‖ :=
  (kernelL hF).opOfMap_norm_le (kernelL hF) _ _ _ _

theorem iotaL_rhoL (c : algebra μ π hπ) (v : VL hF) :
    iotaL hF (rhoL hF hπu c v) = rho hF c (iotaL hF v) := by
  have h : (iotaL hF).toContinuousLinearMap.comp (rhoL hF hπu c) =
      (rho hF c).comp (iotaL hF).toContinuousLinearMap := by
    refine clm_extL hF fun x k w => ?_
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    rw [rhoL_vec, iotaL_vec, iotaL_vec, rho_vec]
    rfl
  exact congrArg (fun A => A v) h

theorem inner_rhoL (c : algebra μ π hπ) (u v : VL hF) :
    ⟪rhoL hF hπu c u, v⟫_ℂ = ⟪u, rhoL hF hπu (star c) v⟫_ℂ := by
  rw [← (iotaL hF).inner_map_map, iotaL_rhoL, inner_rho, ← iotaL_rhoL, (iotaL hF).inner_map_map]

theorem adjoint_rhoL (c : algebra μ π hπ) :
    ContinuousLinearMap.adjoint (rhoL hF hπu c) = rhoL hF hπu (star c) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun u v => ?_).symm
  rw [inner_rhoL, star_star]

theorem rhoL_mul (c d : algebra μ π hπ) : rhoL hF hπu (c * d) = rhoL hF hπu c * rhoL hF hπu d := by
  refine clm_extL hF fun x k w => ?_
  rw [mul_apply_eq_comp, rhoL_vec, rhoL_vec, rhoL_vec]
  congr 1

theorem rhoL_add (c d : algebra μ π hπ) : rhoL hF hπu (c + d) = rhoL hF hπu c + rhoL hF hπu d := by
  refine clm_extL hF fun x k w => ?_
  rw [add_apply, rhoL_vec, rhoL_vec, rhoL_vec, ← vecL'_add]
  congr 1

theorem rhoL_smul (r : ℂ) (c : algebra μ π hπ) : rhoL hF hπu (r • c) = r • rhoL hF hπu c := by
  refine clm_extL hF fun x k w => ?_
  rw [smul_apply, rhoL_vec, rhoL_vec, ← vecL'_smul]
  congr 1

theorem rhoL_one : rhoL hF hπu 1 = 1 := by
  refine clm_extL hF fun x k w => ?_
  rw [rhoL_vec, one_apply_eq_self]
  congr 1

theorem rhoL_sub (c d : algebra μ π hπ) : rhoL hF hπu (c - d) = rhoL hF hπu c - rhoL hF hπu d := by
  refine eq_sub_of_add_eq ?_
  rw [← rhoL_add, sub_add_cancel]

/-- `c ↦ ρ(c)` as a bounded linear map. -/
def rhoLLin : algebra μ π hπ →L[ℂ] (VL hF →L[ℂ] VL hF) :=
  LinearMap.mkContinuous
    { toFun := rhoL hF hπu
      map_add' := rhoL_add hF hπu
      map_smul' := rhoL_smul hF hπu }
    1 fun c => by simpa using norm_rhoL_le hF hπu c

theorem continuous_rhoL : Continuous (rhoL hF hπu) := (rhoLLin hF hπu).continuous

/-! ### Integrated operators of `σ` -/

omit hπu in
instance completeSpace_leftIdeal : CompleteSpace (leftIdeal μ π hπ) :=
  (leftIdeal_isClosed π hπ).completeSpace_coe

theorem integrable_smul_rep_mul_subtype {x : leftIdeal μ π hπ} {φ : G → ℂ}
    (hφ : IsTestFunction φ) :
    Integrable (fun g => φ g • (⟨π g * x, rep_mul_mem_leftIdeal π hπ hπu g x.2⟩ :
      leftIdeal μ π hπ)) μ := by
  have hc : Continuous fun g => (⟨π g * x, rep_mul_mem_leftIdeal π hπ hπu g x.2⟩ :
      leftIdeal μ π hπ) :=
    (continuous_rep_mul π hπ hπu x.2).subtype_mk _
  refine (integrable_smul_rep_mul π hπ hπu x.2 hφ).norm.mono'
    (hφ.1.aestronglyMeasurable.smul hc.aestronglyMeasurable)
    (Eventually.of_forall fun g => le_of_eq rfl)

/-- The integrated operators of `σ` are left multiplications by the `π(φ)`. -/
theorem testOp_sigma_vec (φ : G → ℂ) (hφ : IsTestFunction φ) (x : leftIdeal μ π hπ) (k : κ)
    (w : W) :
    testOp μ (sigma hF hπu) (isContinuousRepresentation_sigma hF hπu) φ hφ (vecL' hF x k w) =
      vecL' hF ⟨testOp μ π hπ φ hφ * x,
        algebra_mul_mem_leftIdeal π hπ hπu (testOp_mem_algebra π hπ φ hφ) x.2⟩ k w := by
  rw [testOp_apply]
  have h1 : (fun g => φ g • sigma hF hπu g (vecL' hF x k w)) = fun g =>
      lambdaL hF k w (φ g • (⟨π g * x, rep_mul_mem_leftIdeal π hπ hπu g x.2⟩ :
        leftIdeal μ π hπ)) := by
    funext g; rw [sigma_vec, map_smul, lambdaL_apply]
  rw [h1]
  refine (ContinuousLinearMap.integral_comp_comm (𝕜 := ℂ) (E := leftIdeal μ π hπ)
    (Fₗ := VL hF) (lambdaL hF k w) (integrable_smul_rep_mul_subtype hπu (x := x) hφ)).trans ?_
  rw [lambdaL_apply]
  congr 1
  apply Subtype.ext
  have h := ContinuousLinearMap.integral_comp_comm (𝕜 := ℂ) (E := leftIdeal μ π hπ)
    (Fₗ := H →L[ℂ] H) (leftIdeal μ π hπ).subtypeL
    (integrable_smul_rep_mul_subtype hπu (x := x) hφ)
  change (leftIdeal μ π hπ).subtypeL _ = _
  refine h.symm.trans ?_
  change ∫ g, φ g • (π g * (x : H →L[ℂ] H)) ∂μ = testOp μ π hπ φ hφ * x
  rw [testOp_mul_eq_integral π hπ hπu x.2]

theorem testOp_sigma_eq_rhoL (φ : G → ℂ) (hφ : IsTestFunction φ) :
    testOp μ (sigma hF hπu) (isContinuousRepresentation_sigma hF hπu) φ hφ =
      rhoL hF hπu ⟨testOp μ π hπ φ hφ, testOp_mem_algebra π hπ φ hφ⟩ := by
  refine clm_extL hF fun x k w => ?_
  rw [testOp_sigma_vec, rhoL_vec]

/-! ### Irreducibility at extreme points -/

/-- The orthogonal projection onto a closed `σ(G)`-invariant subspace commutes with `σ(G)`. -/
theorem starProjection_sigma (M : Submodule ℂ (VL hF)) [M.HasOrthogonalProjection]
    (hMinv : ∀ (g : G), ∀ v ∈ M, sigma hF hπu g v ∈ M) (g : G) (v : VL hF) :
    M.starProjection (sigma hF hπu g v) = sigma hF hπu g (M.starProjection v) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hMinv g _ (M.starProjection_apply_mem v)) fun w hw => ?_
  have hu := sigma_mem_unitary hF hπu g
  have hstar : star (sigma hF hπu g) = sigma hF hπu g⁻¹ := by
    calc star (sigma hF hπu g)
        = star (sigma hF hπu g) * (sigma hF hπu g * sigma hF hπu g⁻¹) := by
          rw [← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = sigma hF hπu g⁻¹ := by rw [← mul_assoc, (Unitary.mem_iff.mp hu).1, one_mul]
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    hstar]
  exact Submodule.inner_right_of_mem_orthogonal (hMinv g⁻¹ w hw)
    (M.sub_starProjection_mem_orthogonal v) |> fun h => by rwa [inner_eq_zero_symm] at h

theorem commute_starProjection_rhoL (M : Submodule ℂ (VL hF)) [M.HasOrthogonalProjection]
    (hMinv : ∀ (g : G), ∀ v ∈ M, sigma hF hπu g v ∈ M) (c : algebra μ π hπ) :
    Commute M.starProjection (rhoL hF hπu c) := by
  set P := M.starProjection
  have hPs : IsSelfAdjoint P := isSelfAdjoint_starProjection M
  let T : StarSubalgebra ℂ (H →L[ℂ] H) :=
    { carrier := {a | ∃ h : a ∈ algebra μ π hπ, Commute P (rhoL hF hπu ⟨a, h⟩)}
      mul_mem' := by
        rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
        refine ⟨(algebra μ π hπ).mul_mem ha hb, ?_⟩
        have : (⟨a * b, (algebra μ π hπ).mul_mem ha hb⟩ : algebra μ π hπ) = ⟨a, ha⟩ * ⟨b, hb⟩ :=
          rfl
        rw [this, rhoL_mul]
        exact hca.mul_right hcb
      add_mem' := by
        rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
        refine ⟨(algebra μ π hπ).add_mem ha hb, ?_⟩
        have : (⟨a + b, (algebra μ π hπ).add_mem ha hb⟩ : algebra μ π hπ) = ⟨a, ha⟩ + ⟨b, hb⟩ :=
          rfl
        rw [this, rhoL_add]
        exact hca.add_right hcb
      algebraMap_mem' := fun r => by
        refine ⟨(algebra μ π hπ).algebraMap_mem r, ?_⟩
        have : (⟨algebraMap ℂ (H →L[ℂ] H) r, (algebra μ π hπ).algebraMap_mem r⟩ :
            algebra μ π hπ) = r • 1 := by
          apply Subtype.ext; simp [Algebra.algebraMap_eq_smul_one]
        rw [this, rhoL_smul, rhoL_one]
        exact (Commute.one_right P).smul_right r
      star_mem' := by
        rintro a ⟨ha, hca⟩
        refine ⟨star_mem ha, ?_⟩
        have : (⟨star a, star_mem ha⟩ : algebra μ π hπ) = star ⟨a, ha⟩ := rfl
        rw [this, ← adjoint_rhoL, ← ContinuousLinearMap.star_eq_adjoint]
        have h2 := hca.star_star
        rwa [hPs.star_eq] at h2 }
  have hgen : testOps μ π hπ ⊆ T := by
    rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨testOp_mem_algebra π hπ φ hφ, ?_⟩
    rw [← testOp_sigma_eq_rhoL]
    have h := intertwiner_comp_testOp (μ := μ) (sigma hF hπu)
      (isContinuousRepresentation_sigma hF hπu) (sigma hF hπu)
      (isContinuousRepresentation_sigma hF hπu) P
      (fun g v => starProjection_sigma hF hπu M hMinv g v) φ hφ
    exact h
  have hTclosed : IsClosed (T : Set (H →L[ℂ] H)) := by
    have e : (T : Set (H →L[ℂ] H)) =
        Subtype.val '' {c : algebra μ π hπ | P * rhoL hF hπu c = rhoL hF hπu c * P} := by
      ext a
      constructor
      · rintro ⟨ha, hca⟩; exact ⟨⟨a, ha⟩, hca.eq, rfl⟩
      · rintro ⟨c, hc, rfl⟩; exact ⟨c.2, hc⟩
    rw [e]
    refine (algebra_isClosed π hπ).isClosedEmbedding_subtypeVal.isClosedMap _ ?_
    have hl : Continuous fun A : VL hF →L[ℂ] VL hF => P * A :=
      (ContinuousLinearMap.compL ℂ (VL hF) (VL hF) (VL hF) P).continuous
    have hr : Continuous fun A : VL hF →L[ℂ] VL hF => A * P :=
      ((ContinuousLinearMap.compL ℂ (VL hF) (VL hF) (VL hF)).flip P).continuous
    exact isClosed_eq (hl.comp (continuous_rhoL hF hπu)) (hr.comp (continuous_rhoL hF hπu))
  have hle : algebra μ π hπ ≤ T :=
    StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le hgen) hTclosed
  obtain ⟨_, hcomm⟩ := hle c.2
  exact hcomm

omit hπu in
/-- Conjugating a star projection by an isometric embedding gives a star projection. -/
theorem isStarProjection_conj {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    (ι : E →L[ℂ] E') (hιι : ∀ u, ContinuousLinearMap.adjoint ι (ι u) = u) {P : E →L[ℂ] E}
    (hP : IsStarProjection P) :
    IsStarProjection (ι.comp (P.comp (ContinuousLinearMap.adjoint ι))) := by
  have hPP : ∀ u, P (P u) = P u := fun u => congrArg (fun A => A u) hP.isIdempotentElem.eq
  have hPadj : ContinuousLinearMap.adjoint P = P := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hP.isSelfAdjoint.star_eq
  refine ⟨?_, ?_⟩
  · change _ * _ = _
    ext v
    simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply, hιι, hPP]
  · rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
    refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun u v => ?_).symm
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_right P,
      hPadj, ContinuousLinearMap.adjoint_inner_left]

theorem adjoint_iotaL_rho (a : algebra μ π hπ) (u : Space hF) :
    ContinuousLinearMap.adjoint (iotaL hF).toContinuousLinearMap (rho hF a u) =
      rhoL hF hπu a (ContinuousLinearMap.adjoint (iotaL hF).toContinuousLinearMap u) := by
  refine ext_inner_right ℂ fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_rhoL, ContinuousLinearMap.adjoint_inner_left]
  change _ = ⟪u, iotaL hF (rhoL hF hπu (star a) v)⟫_ℂ
  rw [iotaL_rhoL, ← inner_rho]
  rfl

omit hπu in
theorem adjoint_iotaL_iotaL (u : VL hF) :
    ContinuousLinearMap.adjoint (iotaL hF).toContinuousLinearMap
      ((iotaL hF).toContinuousLinearMap u) = u :=
  congrArg (fun A => A u) (iotaL hF).adjoint_comp_self

omit hπu in
/-- The conjugate `ι P ι^*` of a projection onto a closed `σ(G)`-invariant subspace. -/
def conjProj (M : Submodule ℂ (VL hF)) [M.HasOrthogonalProjection] : Space hF →L[ℂ] Space hF :=
  (iotaL hF).toContinuousLinearMap.comp (M.starProjection.comp
    (ContinuousLinearMap.adjoint (iotaL hF).toContinuousLinearMap))

omit hπu in
theorem isStarProjection_conjProj (M : Submodule ℂ (VL hF)) [M.HasOrthogonalProjection] :
    IsStarProjection (conjProj hF M) :=
  isStarProjection_conj _ (adjoint_iotaL_iotaL hF) isStarProjection_starProjection

theorem commute_conjProj (M : Submodule ℂ (VL hF)) [M.HasOrthogonalProjection]
    (hMinv : ∀ (g : G), ∀ v ∈ M, sigma hF hπu g v ∈ M) (a : algebra μ π hπ) :
    Commute (conjProj hF M) (rho hF a) := by
  have hPa : ∀ u, M.starProjection (rhoL hF hπu a u) = rhoL hF hπu a (M.starProjection u) :=
    fun u => congrArg (fun A => A u) (commute_starProjection_rhoL hF hπu M hMinv a).eq
  change _ * _ = _ * _
  ext v
  simp only [conjProj, mul_apply_eq_comp, ContinuousLinearMap.comp_apply]
  rw [adjoint_iotaL_rho hF hπu, hPa]
  exact iotaL_rhoL hF hπu a _

omit hπu in
theorem starProjection_eq_conjProj (M : Submodule ℂ (VL hF)) [M.HasOrthogonalProjection]
    (u : VL hF) :
    M.starProjection u = ContinuousLinearMap.adjoint (iotaL hF).toContinuousLinearMap
      (conjProj hF M ((iotaL hF).toContinuousLinearMap u)) := by
  simp only [conjProj, ContinuousLinearMap.comp_apply]
  rw [adjoint_iotaL_iotaL, adjoint_iotaL_iotaL]

/-- For strictly positive weights `c` and a nonzero extreme point `F` of `coneSet Rel c e`, `σ` is
topologically irreducible as soon as its space `VL hF` is nontrivial. -/
theorem isTopologicallyIrreducible_sigma {β : Type*} {c : κ → ℝ} {e : HilbertBasis β ℂ W}
    (hc : ∀ k, 0 < c k) (hext : F ∈ (coneSet Rel c e).extremePoints ℝ) (hne : F ≠ 0)
    (hV : Nontrivial (VL hF)) : IsTopologicallyIrreducible (sigma hF hπu) := by
  refine ⟨hV, fun M hMc hMinv => ?_⟩
  have : CompleteSpace M := hMc.completeSpace_coe
  rcases eq_zero_or_one_of_extreme hc hext hne hF (isStarProjection_conjProj hF M)
    (commute_conjProj hF hπu M hMinv) with h0 | h1
  · left
    refine (Submodule.eq_bot_iff M).mpr fun v hv => ?_
    have h := (Submodule.starProjection_eq_self_iff (K := M)).mpr hv
    rw [← h, starProjection_eq_conjProj, h0, zero_apply, map_zero]
  · right
    refine Submodule.eq_top_iff'.mpr fun v => ?_
    have h := M.starProjection_apply_mem v
    rwa [starProjection_eq_conjProj, h1, one_apply_eq_self, adjoint_iotaL_iotaL] at h

end Langlands.Analysis.TemperedComponent
