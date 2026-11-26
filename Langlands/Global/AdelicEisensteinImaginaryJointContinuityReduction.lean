import Langlands.Global.AdelicWavePacketSiegelDecayReduction
import Langlands.Global.AdelicEisensteinJointRootHyperplaneStatement
import Langlands.Analysis.Meromorphic.CoordinateGluing
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Joint continuity on the imaginary axis from the root-hyperplane form

`EisensteinJointRootHyperplaneStatement` (Bernstein–Lapid, Theorem 2.3 (1), (6) and the
Corollary in §8.6) clears the singularities of the continued Eisenstein series near a point
`λ₀` by a power of a product of root forms, as a function of `(λ, g)` that is continuous and
holomorphic in `λ`. At a point `λ₀` where every scalar function `λ ↦ E(λ)(g)` is holomorphic,
Cauchy's integral formula on a circle in a direction transversal to all root hyperplanes
through `λ₀` expresses `E(λ)(g)` by the cleared function on that circle, where the root forms
do not vanish. This gives joint continuity in `(λ, g)` near `λ₀`, and
`EisensteinImaginaryJointContinuityStatement` follows. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Complex Metric Set
open scoped CategoryTheory.MonObj TensorProduct Real

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Analysis

/-- A parametric interval integral of a function continuous on `s × ℝ` is continuous on `s`, for
an arbitrary topological parameter space: on the compact interval the integrand converges
uniformly. -/
theorem continuousOn_intervalIntegral_of_continuousOn {X : Type*} [TopologicalSpace X]
    {f : X → ℝ → ℂ} {s : Set X} (hf : ContinuousOn (Function.uncurry f) (s ×ˢ univ))
    (a b : ℝ) : ContinuousOn (fun x => ∫ θ in a..b, f x θ) s := by
  intro x₀ hx₀
  have hcont : ∀ x ∈ s, Continuous (f x) := fun x hx => continuousOn_univ.1
    (hf.comp (Continuous.prodMk_right x).continuousOn fun θ _ => ⟨hx, mem_univ θ⟩)
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hL : 0 ≤ |b - a| := abs_nonneg _
  have hδ : 0 < ε / (|b - a| + 1) := div_pos hε (by linarith)
  obtain ⟨v, hv, hvε⟩ := (isCompact_uIcc (a := a) (b := b)).mem_uniformity_of_prod
    (hf.mono (prod_mono subset_rfl (subset_univ _))) hx₀ (Metric.dist_mem_uniformity hδ)
  filter_upwards [hv, self_mem_nhdsWithin] with x hxv hxs
  rw [dist_eq_norm, ← intervalIntegral.integral_sub ((hcont x hxs).intervalIntegrable a b)
    ((hcont x₀ hx₀).intervalIntegrable a b)]
  have hbound : ∀ θ ∈ Set.uIoc a b, ‖f x θ - f x₀ θ‖ ≤ ε / (|b - a| + 1) := fun θ hθ => by
    have := hvε x hxv θ (uIoc_subset_uIcc hθ)
    rw [Set.mem_ofPred_eq, dist_eq_norm] at this
    exact this.le
  calc ‖∫ θ in a..b, f x θ - f x₀ θ‖ ≤ ε / (|b - a| + 1) * |b - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- **Joint continuity at a point of holomorphy from a cleared form.** Let `E'(s)(g)` be
holomorphic in `s` on an open set `O ∋ s₀` for every `g`. Let `h(s, g)` be continuous on
`W × X` for an open `W ∋ s₀`, and suppose that for every `s ∈ W ∩ O` and every `g ∈ X` the
product `(∏_{β ∈ S} L_β(s - s₀))^k · E'(s)(g)` of `E'` with a power of finitely many nonzero
linear forms equals `h(s, g)`. Then `(s, g) ↦ E'(s)(g)` is
continuous at every `(s₀, g₀)`. The proof writes `E'(s)(g)` as a Cauchy integral over the
circle `ζ ↦ s + ζ v` of radius `r`, for a direction `v` with `L_β(v) ≠ 0` for all `β`; on that
circle no `L_β(s + ζ v - s₀)` vanishes when `s` is close to `s₀`, so the integrand is
`h / (∏ L_β)^k`, jointly continuous. -/
theorem continuousAt_of_rootHyperplane_cleared {X : Type*} [TopologicalSpace X] {m : ℕ}
    {E' : (Fin m → ℂ) → X → ℂ} {O : Set (Fin m → ℂ)} (hO : IsOpen O)
    (hdiff : ∀ g, DifferentiableOn ℂ (fun s => E' s g) O)
    {Idx : Type*} (S : Finset Idx) (L : Idx → (Fin m → ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ β ∈ S, ∃ w, L β w ≠ 0) (k : ℕ) {W : Set (Fin m → ℂ)} (hW : IsOpen W)
    {s₀ : Fin m → ℂ} (hs₀W : s₀ ∈ W) (hs₀O : s₀ ∈ O) {h : (Fin m → ℂ) → X → ℂ}
    (hh : ContinuousOn (fun q : (Fin m → ℂ) × X => h q.1 q.2) (W ×ˢ univ))
    (hhE : ∀ g, ∀ s ∈ W, s ∈ O → h s g = (∏ β ∈ S, L β (s - s₀)) ^ k * E' s g)
    (g₀ : X) : ContinuousAt (fun q : (Fin m → ℂ) × X => E' q.1 q.2) (s₀, g₀) := by
  classical
  -- a direction transversal to all root hyperplanes
  obtain ⟨v, hv⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun β : S => L β) (fun β => hL β β.2)
  have hLc : ∀ β, Continuous (L β) := fun β => LinearMap.continuous_of_finiteDimensional _
  -- the radius
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hW.inter hO) s₀ ⟨hs₀W, hs₀O⟩
  set r : ℝ := δ / (2 * (‖v‖ + 1)) with hr_def
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  have hr : 0 < r := div_pos hδ (by positivity)
  have hrv : r * ‖v‖ < δ / 2 := by
    rw [hr_def, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith
  -- the neighbourhood of `s₀`
  let U : Set (Fin m → ℂ) :=
    ball s₀ (δ / 2) ∩ ⋂ β ∈ S, {s | ‖L β (s - s₀)‖ < r * ‖L β v‖}
  have hUo : IsOpen U := isOpen_ball.inter (isOpen_biInter_finset fun β _ =>
    isOpen_lt ((hLc β).comp (continuous_id.sub continuous_const)).norm continuous_const)
  have hs₀U : s₀ ∈ U := by
    refine ⟨mem_ball_self (by linarith), mem_iInter₂.2 fun β hβ => ?_⟩
    simp only [Set.mem_ofPred_eq, sub_self, map_zero, norm_zero]
    exact mul_pos hr (norm_pos_iff.2 (hv ⟨β, hβ⟩))
  have hmem : ∀ s ∈ U, ∀ z : ℂ, ‖z‖ ≤ r → s + z • v ∈ ball s₀ δ := by
    intro s hs z hz
    have h1 : dist s s₀ < δ / 2 := hs.1
    rw [mem_ball, dist_eq_norm, add_sub_right_comm]
    calc ‖s - s₀ + z • v‖ ≤ ‖s - s₀‖ + ‖z • v‖ := norm_add_le _ _
      _ ≤ ‖s - s₀‖ + r * ‖v‖ := by
          rw [norm_smul]; gcongr
      _ < δ / 2 + δ / 2 := by rw [← dist_eq_norm]; linarith
      _ = δ := by ring
  have hmemWO : ∀ s ∈ U, ∀ z : ℂ, ‖z‖ ≤ r → s + z • v ∈ W ∧ s + z • v ∈ O :=
    fun s hs z hz => hball (hmem s hs z hz)
  -- the root forms do not vanish on the circle
  set f : (Fin m → ℂ) → ℂ := fun s => ∏ β ∈ S, L β (s - s₀) with hf_def
  have hfc : Continuous f := continuous_finsetProd _ fun β _ =>
    (hLc β).comp (continuous_id.sub continuous_const)
  have hfne : ∀ s ∈ U, ∀ z : ℂ, ‖z‖ = r → f (s + z • v) ≠ 0 := by
    intro s hs z hz
    refine Finset.prod_ne_zero_iff.2 fun β hβ => ?_
    have hsβ : ‖L β (s - s₀)‖ < r * ‖L β v‖ := (mem_iInter₂.1 hs.2) β hβ
    have heq : L β (s + z • v - s₀) = L β (s - s₀) + z * L β v := by
      rw [add_sub_right_comm, map_add, map_smul, smul_eq_mul]
    rw [heq]
    intro h0
    have : ‖z * L β v‖ = ‖L β (s - s₀)‖ := by
      rw [eq_neg_of_add_eq_zero_right h0, norm_neg]
    rw [norm_mul, hz] at this
    linarith
  -- Cauchy's formula and the cleared integrand
  let H : (Fin m → ℂ) → X → ℂ := fun s g => h s g / f s ^ k
  have hEH : ∀ s ∈ U, ∀ z : ℂ, ‖z‖ = r → ∀ g, E' (s + z • v) g = H (s + z • v) g := by
    intro s hs z hz g
    obtain ⟨hW', hO'⟩ := hmemWO s hs z hz.le
    have hfz := pow_ne_zero k (hfne s hs z hz)
    simp only [H]
    rw [hhE g _ hW' hO']
    exact (mul_div_cancel_left₀ (E' (s + z • v) g) hfz).symm
  have hcauchy : ∀ s ∈ U, ∀ g, E' s g =
      (2 * π * I : ℂ)⁻¹ • ∮ z in C(0, r), (z - 0)⁻¹ • H (s + z • v) g := by
    intro s hs g
    have hZo : IsOpen {z : ℂ | s + z • v ∈ ball s₀ δ} :=
      isOpen_ball.preimage (continuous_const.add (continuous_id.smul continuous_const))
    have hdz : DifferentiableOn ℂ (fun z : ℂ => E' (s + z • v) g) {z | s + z • v ∈ ball s₀ δ} :=
      (hdiff g).comp ((differentiable_const _).add (differentiable_id.smul_const v)).differentiableOn
        fun z hz => (hball hz).2
    have hcb : closedBall (0 : ℂ) r ⊆ {z | s + z • v ∈ ball s₀ δ} := fun z hz =>
      hmem s hs z (by simpa using mem_closedBall_zero_iff.1 hz)
    have hformula := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (s := ∅) countable_empty (mem_ball_self hr) (hdz.continuousOn.mono hcb)
      (fun z hz => hdz.differentiableAt (hZo.mem_nhds (hcb (ball_subset_closedBall hz.1))))
    simp only [add_zero, zero_smul] at hformula
    rw [← hformula]
    congr 1
    refine circleIntegral.integral_congr hr.le fun z hz => ?_
    rw [hEH s hs z (by simpa using mem_sphere_zero_iff_norm.1 hz) g]
  -- the Cauchy integral is jointly continuous
  let Φ : (Fin m → ℂ) × X → ℂ := fun q => (2 * π * I : ℂ)⁻¹ •
    ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap 0 r) θ •
      ((circleMap 0 r θ - 0)⁻¹ • H (q.1 + circleMap 0 r θ • v) q.2)
  have hΦeq : ∀ q ∈ U ×ˢ (univ : Set X), E' q.1 q.2 = Φ q := fun q hq => by
    rw [hcauchy q.1 hq.1 q.2]
    rfl
  have hcircle : ∀ θ : ℝ, ‖circleMap 0 r θ‖ = r := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hr]
  have hintegrand : ContinuousOn (Function.uncurry fun (q : (Fin m → ℂ) × X) (θ : ℝ) =>
      deriv (circleMap 0 r) θ • ((circleMap 0 r θ - 0)⁻¹ • H (q.1 + circleMap 0 r θ • v) q.2))
      ((U ×ˢ univ) ×ˢ univ) := by
    have hcm : Continuous fun p : ((Fin m → ℂ) × X) × ℝ => circleMap 0 r p.2 :=
      (continuous_circleMap 0 r).comp continuous_snd
    have hpt : Continuous fun p : ((Fin m → ℂ) × X) × ℝ => p.1.1 + circleMap 0 r p.2 • v :=
      (continuous_fst.comp continuous_fst).add (hcm.smul continuous_const)
    have hmaps : MapsTo (fun p : ((Fin m → ℂ) × X) × ℝ => (p.1.1 + circleMap 0 r p.2 • v, p.1.2))
        ((U ×ˢ univ) ×ˢ univ) (W ×ˢ univ) := fun p hp =>
      ⟨(hmemWO p.1.1 hp.1.1 _ (hcircle p.2).le).1, mem_univ _⟩
    have hhc : ContinuousOn (fun p : ((Fin m → ℂ) × X) × ℝ =>
        h (p.1.1 + circleMap 0 r p.2 • v) p.1.2) ((U ×ˢ univ) ×ˢ univ) :=
      hh.comp (hpt.prodMk (continuous_snd.comp continuous_fst)).continuousOn hmaps
    have hfc' : ContinuousOn (fun p : ((Fin m → ℂ) × X) × ℝ =>
        f (p.1.1 + circleMap 0 r p.2 • v) ^ k) ((U ×ˢ univ) ×ˢ univ) :=
      ((hfc.comp hpt).pow k).continuousOn
    have hHc : ContinuousOn (fun p : ((Fin m → ℂ) × X) × ℝ =>
        H (p.1.1 + circleMap 0 r p.2 • v) p.1.2) ((U ×ˢ univ) ×ˢ univ) :=
      hhc.div hfc' fun p hp => pow_ne_zero k (hfne p.1.1 hp.1.1 _ (hcircle p.2))
    have hinv : Continuous fun p : ((Fin m → ℂ) × X) × ℝ => (circleMap 0 r p.2 - 0)⁻¹ := by
      simp only [sub_zero]
      exact hcm.inv₀ fun p => circleMap_ne_center hr.ne'
    have hder : Continuous fun p : ((Fin m → ℂ) × X) × ℝ => deriv (circleMap 0 r) p.2 := by
      simp only [deriv_circleMap]
      exact hcm.mul continuous_const
    exact hder.continuousOn.smul (hinv.continuousOn.smul hHc)
  have hΦc : ContinuousOn Φ (U ×ˢ univ) :=
    ((continuousOn_intervalIntegral_of_continuousOn hintegrand 0 (2 * π)).const_smul
      ((2 * π * I : ℂ)⁻¹)).congr fun q _ => rfl
  have hnhds : U ×ˢ (univ : Set X) ∈ nhds (s₀, g₀) :=
    (hUo.prod isOpen_univ).mem_nhds ⟨hs₀U, mem_univ g₀⟩
  exact ((hΦc.continuousAt hnhds).congr
    (Filter.eventuallyEq_of_mem hnhds fun q hq => (hΦeq q hq).symm))

end Analysis

/-- A nonzero real root form has a nonzero complex extension on some point `1 ⊗ χ`. -/
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.exists_rootFunctional_ne_zero
    {F : Type} [Field F]
    {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) {β : characterLattice A}
    (hβ : r.realRootFunctional hA hT β ≠ 0) :
    ∃ χ : GroupScheme.rationalCharacters P, r.rootFunctional hA hT β ((1 : ℂ) ⊗ₜ[ℤ] χ) ≠ 0 := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  apply hβ
  refine TensorProduct.AlgebraTensorModule.ext fun x χ => ?_
  have h1 : r.realRootFunctional hA hT β ((1 : ℝ) ⊗ₜ[ℤ] χ) = 0 := by
    have := hcon χ
    rw [ParabolicRootPresentation.rootFunctional_tmul, one_mul, Complex.ofReal_eq_zero] at this
    exact this
  have h2 : x ⊗ₜ[ℤ] χ = x • ((1 : ℝ) ⊗ₜ[ℤ] χ : RealCharacterParameter F P) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h2, map_smul, h1, smul_zero, LinearMap.zero_apply]

/-- **Joint continuity from the root-hyperplane form.** `EisensteinJointRootHyperplaneStatement`
implies `EisensteinImaginaryJointContinuityStatement`. -/
def EisensteinImaginaryJointContinuityReductionStatement : Prop :=
  EisensteinJointRootHyperplaneStatement.{0} → EisensteinImaginaryJointContinuityStatement

theorem eisensteinImaginaryJointContinuityReduction :
    EisensteinImaginaryJointContinuityReductionStatement := by
  intro hJ F _ _ G P M U A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hsmooth hcalc φ
    hKmax hrho hφ E D himag hmero hreg n eR
  have : FiniteDimensional ℂ (ComplexCharacterParameter F P) := (hmero 1).1
  set m := Module.finrank ℂ (ComplexCharacterParameter F P)
  let eC : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
    (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  have key : ∀ s₀ : Fin m → ℂ, eC s₀ ∈ D → ∀ g₀ : AdelicGroupPoints F G,
      ContinuousAt (fun q : (Fin m → ℂ) × AdelicGroupPoints F G => E (eC q.1) q.2) (s₀, g₀) := by
    intro s₀ hs₀ g₀
    obtain ⟨S, k, W, h, -, hSne, hWo, hs₀W, hhc, -, -, hhE⟩ :=
      hJ F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ.1 E D hmero
        hreg m eC s₀
    refine continuousAt_of_rootHyperplane_cleared (E' := fun s g => E (eC s) g)
      ((hmero g₀).2 m eC).1
      (fun g => differentiableOn_of_isHolomorphicOn ((hmero g).2 m eC).2.2.1) S
      (fun β => (r.rootFunctional hA hT β).comp eC.toLinearMap) ?_ k hWo hs₀W hs₀ hhc ?_ g₀
    · intro β hβ
      obtain ⟨χ, hχ⟩ := r.exists_rootFunctional_ne_zero hA hT (hSne β hβ)
      exact ⟨eC.symm ((1 : ℂ) ⊗ₜ[ℤ] χ), by simpa using hχ⟩
    · intro g s hsW hsD
      rw [hhE g s hsW hsD]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_sub]
  let Lx : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℂ) :=
    (eC.symm.toLinearMap.restrictScalars ℝ) ∘ₗ (imaginaryParameter F P) ∘ₗ eR.toLinearMap
  have hLx : Continuous Lx := LinearMap.continuous_of_finiteDimensional Lx
  refine continuous_iff_continuousAt.2 fun q => ?_
  have hq : eC (Lx q.1) = imaginaryParameter F P (eR q.1) := by
    simp only [Lx, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have hkey := key (Lx q.1) (hq ▸ himag ⟨eR q.1, rfl⟩) q.2
  have hcomp := hkey.comp (f := fun q : (Fin n → ℝ) × AdelicGroupPoints F G => (Lx q.1, q.2))
    ((hLx.comp continuous_fst).prodMk continuous_snd).continuousAt
  refine hcomp.congr (Filter.Eventually.of_forall fun q' => ?_)
  simp only [Function.comp_apply]
  have hq' : eC (Lx q'.1) = imaginaryParameter F P (eR q'.1) := by
    simp only [Lx, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [hq']

/-- `EisensteinJointRootHyperplaneStatement` and `WavePacketChamberDecayStatement` imply
`WavePacketSiegelDecayStatement`. -/
theorem wavePacketSiegelDecay_of_jointRootHyperplane
    (hJ : EisensteinJointRootHyperplaneStatement.{0})
    (hchamber : WavePacketChamberDecayStatement) : WavePacketSiegelDecayStatement :=
  wavePacketSiegelDecay_of_reduction (eisensteinImaginaryJointContinuityReduction hJ) hchamber

end Langlands.Global
