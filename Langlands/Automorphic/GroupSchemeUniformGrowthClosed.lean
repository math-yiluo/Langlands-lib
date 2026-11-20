import Langlands.Automorphic.GroupSchemeUniformGrowthOperators
import Langlands.Geometry.Manifold.SmoothGroupUniformLimit
import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Mathlib.Topology.MetricSpace.Algebra

/-! # Closedness of the uniform-growth derivative realization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Filter Set
open scoped CategoryTheory.MonObj ENNReal Manifold ContDiff Topology TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))

attribute [local instance 100] LieRing.ofAssociativeRing

local instance : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

local notation "V" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "UEA" => AdelicEnvelopingAlgebra F G hsmooth
local notation "P" => AdelicGroupPoints F G
local notation "B" => lp (fun _ : P => ℂ) ∞
local notation "D" => adelicEnvelopingAction F G hsmooth hcalc

/-- Embed a growth vector by the coordinates defining its topology. -/
def derivativeCoordinates : V →L[ℂ] (UEA → B) :=
  ContinuousLinearMap.pi (weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L)

private abbrev weight (x : P) : ℂ :=
  (RepresentationGrowth.adelicSourceNorm F G rho x ^ R : ℝ)

include hN in
omit [IsAffine G.X.left] in
private theorem weight_ne_zero (x : P) : weight F G rho R x ≠ 0 :=
  Complex.ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x) R).ne'

include hN in
omit [IsAffine G.X.left] in
private theorem continuous_weight : Continuous (weight F G rho R) := by
  let c : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hc : 0 < c := pow_pos (by exact_mod_cast hN) _
  have hν : RepresentationGrowth.adelicSourceNorm F G rho =
      fun x => c⁻¹ * RepresentationGrowth.adelicHeight F G rho x := by
    funext x
    rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho x,
      ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have hcont : Continuous (RepresentationGrowth.adelicSourceNorm F G rho) :=
    hν.symm ▸ continuous_const.mul (RepresentationGrowth.continuous_adelicHeight F G rho hN)
  exact Complex.continuous_ofReal.comp (hcont.rpow_const fun x =>
    Or.inl (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x).ne')

include hN in
omit [IsAffine G.X.left] in
private theorem tendstoLocallyUniformly_mul_weight {Idx : Type*} {l : Filter Idx}
    {b : Idx → B} {c : B} (h : Tendsto b l (𝓝 c)) :
    TendstoLocallyUniformly (fun i x => b i x * weight F G rho R x)
      (fun x => c x * weight F G rho R x) l := by
  have hu : TendstoUniformly (fun i x => b i x) (fun x => c x) l := by
    refine Metric.tendstoUniformly_iff.mpr fun ε hε => ?_
    filter_upwards [h (Metric.ball_mem_nhds c hε)] with i hi x
    change b i ∈ Metric.ball c ε at hi
    rw [Metric.mem_ball, dist_eq_norm] at hi
    rw [dist_comm, dist_eq_norm]
    exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (b i - c) x).trans_lt hi
  have hw := continuous_weight F G rho hN R
  have hwlim : TendstoLocallyUniformly (fun _ : Idx => weight F G rho R) (weight F G rho R) l := by
    apply TendstoUniformly.tendstoLocallyUniformly
    exact Metric.tendstoUniformly_iff.mpr fun ε hε =>
      Eventually.of_forall fun _ _ => by simpa only [dist_self] using hε
  exact hu.tendstoLocallyUniformly.fun_mul₀_of_isBoundedUnder hwlim
    (fun _ => isBoundedUnder_of ⟨‖c‖, fun x => by
      rw [dist_zero_right]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero c x⟩)
    (fun x => ((hw.tendsto x).dist tendsto_const_nhds).isBoundedUnder_le)

set_option backward.isDefEq.respectTransparency true in
private theorem continuous_pair_fixed (s : FiniteAdelicGroupPoints F G) :
    Continuous (fun t : InfiniteAdelicGroupPoints F G => AdelicGroupPoints.pair F G t s) := by
  let p (t : InfiniteAdelicGroupPoints F G) := (t, s)
  have hp : Continuous p :=
    continuous_id.prodMk (continuous_const (y := s))
  change Continuous ((AdelicGroupPoints.split F G).symm ∘ p)
  exact (AdelicGroupPoints.split F G).symm.continuous.comp hp

private theorem exists_of_tendsto_coordinates {Idx : Type*} {l : Filter Idx} [l.NeBot]
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    (f : Idx → V) (b : UEA → B)
    (hb : ∀ a, Tendsto (fun i => derivativeCoordinates F G rho hsmooth hcalc hN hrho R L (f i) a)
      l (𝓝 (b a))) :
    ∃ f₀ : V, derivativeCoordinates F G rho hsmooth hcalc hN hrho R L f₀ = b := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let b₀ (i : Idx) : FinitePlotSmoothRationalFunctions F G :=
    (f i : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val
  let g (a : UEA) (x : P) : ℂ := b a x * weight F G rho R x
  let fi (i : Idx) (a : UEA) (x : P) : ℂ := evaluate F G (D a (b₀ i)).val x
  have hlim (a : UEA) : TendstoLocallyUniformly (fun i => fi i a) (g a) l := by
    have h := tendstoLocallyUniformly_mul_weight F G rho hN R (hb a)
    convert h using 1
    funext i x
    change fi i a x = fi i a x * (weight F G rho R x)⁻¹ * weight F G rho R x
    rw [mul_assoc, inv_mul_cancel₀ (weight_ne_zero F G rho hN R x), mul_one]
  have hpt (a : UEA) (x : P) : Tendsto (fun i => fi i a x) l (𝓝 (g a x)) :=
    (tendstoLocallyUniformlyOn_univ.mpr (hlim a)).tendsto_at (mem_univ x)
  have hcont (a : UEA) : Continuous (g a) :=
    (hlim a).continuous (Frequently.of_forall fun i => (D a (b₀ i)).val.property)
  have hleft (a : UEA) (γ : RationalGroupPoints F G) (x : P) :
      g a (AdelicGroupPoints.rational F G γ * x) = g a x := by
    have h (i : Idx) : fi i a (AdelicGroupPoints.rational F G γ * x) = fi i a x := by
      exact (D a (b₀ i)).val.val.property γ x
    exact tendsto_nhds_unique (hpt a _) ((funext h).symm ▸ hpt a x)
  have hright (a : UEA) (s : FiniteAdelicGroupPoints F G) (hs : s ∈ L) (x : P) :
      g a (x * AdelicGroupPoints.ofFinite F G s) = g a x := by
    have h (i : Idx) : fi i a (x * AdelicGroupPoints.ofFinite F G s) = fi i a x := by
      have hi := ((envelopingActionCLM F G rho hsmooth hcalc hN hrho R L a (f i)) :
        uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).property.1 s hs
      exact congrArg (fun f₀ : FinitePlotSmoothRationalFunctions F G => evaluate F G f₀.val x) hi
    exact tendsto_nhds_unique (hpt a _) ((funext h).symm ▸ hpt a x)
  let M := 𝓘(ℝ, smoothModel F d)
  let gen (X : GroupLieAlgebra M (InfiniteAdelicGroupPoints F G)) : UEA :=
    UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)
  have hgSlice (s : FiniteAdelicGroupPoints F G) :
      let p (t : InfiniteAdelicGroupPoints F G) := AdelicGroupPoints.pair F G t s
      (∀ a, ContMDiff M 𝓘(ℝ, ℂ) ∞ (g a ∘ p)) ∧ ∀ a X,
        groupDirectionalValue M X (g a ∘ p) = g (gen X * a) ∘ p := by
    let p (t : InfiniteAdelicGroupPoints F G) := AdelicGroupPoints.pair F G t s
    have hp : Continuous p := continuous_pair_fixed F G s
    apply contMDiff_of_tendstoLocallyUniformly_invariantDerivatives
      (E := smoothModel F d) (G := InfiniteAdelicGroupPoints F G) (l := l)
      (fun X a => gen X * a) (f := fun i a => fi i a ∘ p) (g := fun a => g a ∘ p)
    · intro i a
      exact (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (finitePlotSmoothSlice F G s
        (D a (b₀ i))).property
    · intro i a X
      funext t
      change groupDirectionalValue M X (fi i a ∘ p) t =
        evaluate F G (D (gen X * a) (b₀ i)).val (p t)
      rw [map_mul, Module.End.mul_apply]
      change _ = evaluate F G
        (finitePlotSmoothEnvelopingAction F G hsmooth hcalc
          (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) (D a (b₀ i))).val (p t)
      rw [finitePlotSmoothEnvelopingAction_real_generator]
      exact (evaluate_finitePlotSmoothDifferentialAction F G hsmooth X _ t s).symm
    · exact fun a => (hlim a).comp p hp
  let h (a : UEA) : ContinuousRationalFunctions F G :=
    ⟨⟨g a, hleft a⟩, hcont a⟩
  let L₀ : OpenSubgroup (FiniteAdelicGroupPoints F G) := ⟨L, hL⟩
  let s (a : UEA) : FinitePlotSmoothRationalFunctions F G := by
    refine ⟨h a, (mem_infinitePlotSmoothSubrepresentation F G (h a)).mpr ?_, ⟨L₀, ?_⟩⟩
    · intro p
      exact (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr ((hgSlice p).1 a)
    · intro p
      exact Subtype.ext (Subtype.ext (funext (hright a p.val p.property)))
  have hext {s₁ s₂ : FinitePlotSmoothRationalFunctions F G}
      (hEq : ∀ x, evaluate F G s₁.val x = evaluate F G s₂.val x) : s₁ = s₂ :=
    Subtype.ext (Subtype.ext (Subtype.ext (funext hEq)))
  let sl : UEA →ₗ[ℂ] FinitePlotSmoothRationalFunctions F G :=
    { toFun := s
      map_add' := fun a c => hext fun x => by
        change g (a + c) x = g a x + g c x
        have hEq (i : Idx) : fi i a x + fi i c x = fi i (a + c) x := by
          simp only [fi, map_add, LinearMap.add_apply]
          rfl
        exact tendsto_nhds_unique (hpt (a + c) x) (((hpt a x).add (hpt c x)).congr hEq)
      map_smul' := fun z a => hext fun x => by
        change g (z • a) x = z * g a x
        have hEq (i : Idx) : z * fi i a x = fi i (z • a) x := by
          simp only [fi, map_smul, LinearMap.smul_apply]
          rfl
        exact tendsto_nhds_unique (hpt (z • a) x)
          ((tendsto_const_nhds.mul (hpt a x)).congr hEq) }
  have hgen (X : GroupLieAlgebra M (InfiniteAdelicGroupPoints F G)) (a : UEA) :
      D (gen X) (sl a) = sl (gen X * a) := by
    apply hext
    intro x
    obtain ⟨⟨t, w⟩, rfl⟩ := (AdelicGroupPoints.split F G).symm.surjective x
    change evaluate F G (D (gen X) (sl a)).val (AdelicGroupPoints.pair F G t w) = _
    change evaluate F G (finitePlotSmoothEnvelopingAction F G hsmooth hcalc
      (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) (sl a)).val _ = _
    rw [finitePlotSmoothEnvelopingAction_real_generator, evaluate_finitePlotSmoothDifferentialAction]
    exact congrFun ((hgSlice w).2 a X) t
  have hgenC (Z : ℂ ⊗[ℝ] GroupLieAlgebra M (InfiniteAdelicGroupPoints F G)) (a : UEA) :
      D (UniversalEnvelopingAlgebra.ι ℂ Z) (sl a) =
        sl (UniversalEnvelopingAlgebra.ι ℂ Z * a) := by
    induction Z using TensorProduct.inductionOn with
    | tmul z X =>
      have hz : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hz, map_smul, map_smul, LinearMap.smul_apply, smul_mul_assoc, map_smul, hgen X]
    | add Z W hZ hW => simp only [map_add, LinearMap.add_apply, add_mul, hZ, hW]
  have hact (a : UEA) : ∀ c, D a (sl c) = sl (a * c) := by
    obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
      (UniversalEnvelopingAlgebra.ringCon ℂ
        (ℂ ⊗[ℝ] GroupLieAlgebra M (InfiniteAdelicGroupPoints F G))) a
    induction t using TensorAlgebra.induction with
    | algebraMap z =>
      intro c
      rw [AlgHom.commutes]
      change D (algebraMap ℂ UEA z) (sl c) = sl (algebraMap ℂ UEA z * c)
      rw [(D : UEA →ₐ[ℂ] _).commutes, Module.algebraMap_end_apply]
      simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul]
    | «ι» Z => exact hgenC Z
    | mul u v hu hv =>
      intro c
      simp only [map_mul, Module.End.mul_apply, hv, hu, mul_assoc]
    | add u v hu hv =>
      intro c
      simp only [map_add, LinearMap.add_apply, add_mul, hu, hv]
  let result : V := ⟨sl 1, fun w hw => hext fun x => hright 1 w hw x, fun a =>
    ⟨‖b a‖, fun x => by
      rw [hact, mul_one]
      change ‖b a x * weight F G rho R x‖ ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x) R)]
      exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero (b a) x)
        (Real.rpow_nonneg (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x).le _)⟩⟩
  refine ⟨result, funext fun a => Subtype.ext ?_⟩
  funext x
  change evaluate F G (D a (sl 1)).val x * (weight F G rho R x)⁻¹ = b a x
  rw [hact, mul_one]
  change (b a x * weight F G rho R x) * (weight F G rho R x)⁻¹ = b a x
  rw [mul_assoc, mul_inv_cancel₀ (weight_ne_zero F G rho hN R x), mul_one]

/-- For an open finite level, the derivative coordinates realize the actual
uniform moderate growth space as a closed subspace of the product of its Banach
coordinates. -/
theorem isClosed_range_derivativeCoordinates
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G))) :
    IsClosed (range (derivativeCoordinates F G rho hsmooth hcalc hN hrho R L)) := by
  let T := derivativeCoordinates F G rho hsmooth hcalc hN hrho R L
  apply isClosed_of_closure_subset
  intro b hb
  let l : Filter (range T) := comap Subtype.val (𝓝 b)
  let : l.NeBot := mem_closure_iff_comap_neBot.mp hb
  let f (x : range T) := Classical.choose x.property
  have hf (x : range T) : T (f x) = x.val := Classical.choose_spec x.property
  refine exists_of_tendsto_coordinates F G rho hsmooth hcalc hN hrho R L hL
    (l := l) f b (fun a => ?_)
  have ht : Tendsto (Subtype.val : range T → UEA → B) l (𝓝 b) := tendsto_comap
  simpa only [Function.comp_def, ← hf] using ((continuous_apply a).tendsto b).comp ht

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
