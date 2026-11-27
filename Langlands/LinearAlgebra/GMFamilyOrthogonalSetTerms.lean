import Langlands.LinearAlgebra.GMFamilySplittingDisplacement
import Langlands.LinearAlgebra.GMFamilyConeIntegrals
import Langlands.LinearAlgebra.GMFamilyRelativeFourier
import Langlands.LinearAlgebra.GMFamilyChamberCoordinates

/-! # The terms of the alternate splitting formula along a positive orthogonal set

Estimates for the integrals over `𝔞_M^G` of the products `c_M^{Q₁} d_M^{Q₂}` in the alternate
splitting formula, with `c_P(λ) = e^{λ(Y_P)}` for a positive `(G, M)`-orthogonal set `Y`. -/

noncomputable section

open scoped RealInnerProductSpace SchwartzMap Topology FourierTransform
open Finset Classical MeasureTheory Complex
open Langlands.Analysis

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {R : Finset E} {a : Submodule ℝ E}

/-- `x ↦ Λ_x = ⟪x, ·⟫` (`dualParam`, the point `λ = iΛ_x`), as a continuous linear map from
`𝔞_M^G` to `StrongDual ℝ a`. -/
def dualParamCLM (R : Finset E) (a : Submodule ℝ E) : relativeSpace R a →L[ℝ] StrongDual ℝ a :=
  LinearMap.mkContinuous
    { toFun := dualParam R a
      map_add' := fun x y => by ext v; simp [dualParam_apply, inner_add_left]
      map_smul' := fun c x => by ext v; simp [dualParam_apply, inner_smul_left] } 1 fun x => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, dualParam_apply, one_mul, Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans_eq (by simp)

omit [FiniteDimensional ℝ E] in
theorem dualParamCLM_apply (x : relativeSpace R a) : dualParamCLM R a x = dualParam R a x := rfl

omit [FiniteDimensional ℝ E] in
theorem norm_le_dualParamCLM (x : relativeSpace R a) : ‖x‖ ≤ ‖dualParamCLM R a x‖ := by
  have h := (dualParamCLM R a x).le_opNorm ⟨x, x.property.1⟩
  rw [dualParamCLM_apply, dualParam_apply] at h
  rw [dualParamCLM_apply]
  have h2 : ⟪(x : E), (x : E)⟫ = ‖x‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq]; rfl
  rw [h2, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)] at h
  have h3 : ‖(⟨x, x.property.1⟩ : a)‖ = ‖x‖ := rfl
  rw [h3] at h
  by_cases hx : ‖x‖ = 0
  · rw [hx]; exact norm_nonneg (dualParam R a x)
  · have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    have h4 : ‖x‖ * ‖x‖ ≤ ‖dualParam R a x‖ * ‖x‖ := by nlinarith
    exact le_of_mul_le_mul_right h4 hpos

variable [MeasurableSpace E] [BorelSpace E]

/-- **The `d`-side of a term.** For a face `Q₂ = posSet R w`, `w ∈ a`, and `N ∈ ℕ` there are `K` and
`C ≥ 0` such that for every `(G, M)`-family `d` of Schwartz functions, the function
`x ↦ d_M^{Q₂}(Λ_x)` on `𝔞_M^G` agrees off the walls with a Schwartz function `u` satisfying
`(1 + ‖H‖)^N |phaseFourier u H| ≤ C ∑_P schwartzSup K (d_P)` for all `H`. -/
theorem exists_face_schwartz (hR : IsRootSet R) (ha : IsLeviSpace R a) (w : a) (N : ℕ) :
    ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ d : Finset E → 𝓢(StrongDual ℝ a, ℂ),
      IsFamily R a (fun S Λ => d S Λ) →
      ∃ u : 𝓢(relativeSpace R a, ℂ),
        (∀ x : relativeSpace R a, OffWalls R a (dualParam R a x) →
          u x = cQM R a (fun S Λ => d S Λ) (posSet R (w : E)) (dualParam R a x)) ∧
        ∀ H : relativeSpace R a, (1 + ‖H‖) ^ N * ‖phaseFourier u H‖ ≤
          C * ∑ P ∈ parabolics R a, schwartzSup ℂ K (d P) := by
  let R' := leviRoots R (posSet R (w : E))
  have hR' : IsRootSet R' := isRootSet_leviRoots_posSet hR _
  have ha' : IsLeviSpace R' a := isLeviSpace_leviRoots ha w
  obtain ⟨K₁, C₁, hC₁, H₁⟩ := exists_phaseFourier_decay (V := relativeSpace R a) N
  let T : 𝓢(StrongDual ℝ a, ℂ) →L[ℂ] 𝓢(relativeSpace R a, ℂ) :=
    SchwartzMap.compCLM ℂ (dualParamCLM R a).hasTemperateGrowth
      ⟨1, 1, fun x => by
        have := norm_le_dualParamCLM x
        simp only [pow_one, one_mul]
        linarith [norm_nonneg (dualParamCLM R a x)]⟩
  obtain ⟨K₂, C₂, hC₂, H₂⟩ := exists_schwartzSup_bound_schwartz T K₁
  obtain ⟨K₃, C₃, hC₃, H₃⟩ := exists_schwartz_cM hR' ha' K₂
  let n₂ := (parabolics R' a).card
  refine ⟨K₃, C₁ * C₂ * C₃ * n₂, by positivity, fun d hd => ?_⟩
  let d' : Finset E → 𝓢(StrongDual ℝ a, ℂ) := fun S => d (posSet R (w : E) ∪ S)
  have hd' : IsFamily R' a (fun S Λ => d' S Λ) := isFamily_face hR w hd
  obtain ⟨F, hF, hFb⟩ := H₃ d' hd'
  refine ⟨T F, fun x hx => ?_, fun H => ?_⟩
  · change F (dualParamCLM R a x) = _
    rw [dualParamCLM_apply, hF _ fun S hS => theta_ne_zero_of_offWalls_face hR ha w hS hx]
    rfl
  · have hsum : ∑ S ∈ parabolics R' a, schwartzSup ℂ K₃ (d' S) ≤
        n₂ * ∑ P ∈ parabolics R a, schwartzSup ℂ K₃ (d P) := by
      have hle : ∀ S ∈ parabolics R' a, schwartzSup ℂ K₃ (d' S) ≤
          ∑ P ∈ parabolics R a, schwartzSup ℂ K₃ (d P) := fun S hS =>
        Finset.single_le_sum (f := fun P => schwartzSup ℂ K₃ (d P))
          (fun P _ => apply_nonneg _ _) (union_parabolic_of_local hR w hS).1
      refine (Finset.sum_le_sum hle).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    calc (1 + ‖H‖) ^ N * ‖phaseFourier (T F) H‖ ≤ C₁ * schwartzSup ℂ K₁ (T F) := H₁ _ H
      _ ≤ C₁ * (C₂ * schwartzSup ℂ K₂ F) := mul_le_mul_of_nonneg_left (H₂ F) hC₁
      _ ≤ C₁ * (C₂ * (C₃ * ∑ S ∈ parabolics R' a, schwartzSup ℂ K₃ (d' S))) := by gcongr
      _ ≤ C₁ * (C₂ * (C₃ * (n₂ * ∑ P ∈ parabolics R a, schwartzSup ℂ K₃ (d P)))) := by gcongr
      _ = _ := by ring

section OrthantTerms

variable (hR : IsRootSet R) (ha : IsLeviSpace R a) {P : Finset E} (hP : P ∈ parabolics R a)
  {ι : Type*} [Fintype ι] (j : ι → simpleRoots a P)

omit [MeasurableSpace E] [BorelSpace E] in
include hR ha hP in
/-- Coordinates of the chamber basis are bounded by the norm. -/
theorem exists_chamber_coord_norm :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : relativeSpace R a) (β : simpleRoots a P),
      |(chamberBasis hR ha hP).repr z β| ≤ C * ‖z‖ := by
  let b := chamberBasis hR ha hP
  refine ⟨‖(b.equivFunL : relativeSpace R a →L[ℝ] (simpleRoots a P → ℝ))‖ + 1, by positivity,
    fun z β => ?_⟩
  have h1 : |b.repr z β| ≤ ‖b.equivFunL z‖ := by
    have := norm_le_pi_norm (b.equivFunL z) β
    simpa [Module.Basis.equivFunL, Real.norm_eq_abs] using this
  refine h1.trans ((ContinuousLinearMap.le_opNorm (b.equivFunL :
    relativeSpace R a →L[ℝ] (simpleRoots a P → ℝ)) z).trans ?_)
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

omit [MeasurableSpace E] [BorelSpace E] in
include hR ha hP in
theorem chamberBasis_repr_orthant (Y : relativeSpace R a)
    (X : ι → ℝ) (β : simpleRoots a P) :
    (chamberBasis hR ha hP).repr (Y - ∑ i, X i • chamberBasis hR ha hP (j i)) β =
      (chamberBasis hR ha hP).repr Y β - ∑ i, if j i = β then X i else 0 := by
  rw [map_sub, map_sum, Finsupp.sub_apply, Finsupp.finsetSum_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  split_ifs <;> simp

theorem one_add_pow_inv_le {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (n : ℕ) :
    ((1 + c * t) ^ n)⁻¹ ≤ (max 1 c⁻¹) ^ n * ((1 + t) ^ n)⁻¹ := by
  have hM : 1 ≤ max 1 c⁻¹ := le_max_left _ _
  have hMc : 1 ≤ max 1 c⁻¹ * c := by
    have := mul_le_mul_of_nonneg_right (le_max_right 1 c⁻¹) hc.le
    rwa [inv_mul_cancel₀ hc.ne'] at this
  have h5 : 1 + t ≤ max 1 c⁻¹ * (1 + c * t) := by nlinarith
  rw [← inv_pow, ← inv_pow, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ n
  rw [inv_le_comm₀ (by positivity) (by positivity), mul_inv, inv_inv]
  calc 1 + c * t = max 1 c⁻¹ * (1 + c * t) * (max 1 c⁻¹)⁻¹ := by
        field_simp
    _ ≥ (1 + t) * (max 1 c⁻¹)⁻¹ :=
        mul_le_mul_of_nonneg_right h5 (inv_nonneg.mpr (by positivity))
    _ = (max 1 c⁻¹)⁻¹ * (1 + t) := mul_comm _ _

include hR ha hP in
/-- **Integrals over orthants of the Fourier integral of a test.** Let `j : ι → Δ_P` be injective
and `n ∈ ℕ`. There is `C ≥ 0` such that for all `t ≥ 0`, all `Y ∈ 𝔞_M^G` with `⟪β, Y⟫ ≥ t` for
every simple root `β` of `P`, all `u` and `A ≥ 0` with
`(1 + ‖H‖)^{n + |ι| + 1} |phaseFourier u H| ≤ A`, and every measurable set `D` of `X ∈ ℝ^ι` such
that each `X ∈ D` has a simple root `β` with `X_i ≤ 0` whenever `j(i) = β` (vacuous if `β` is not
in the image of `j`), the integral over `D` of `phaseFourier u (Y − ∑_i X_i v_{j(i)})` is at most
`C A (1 + t)^{−n}`. -/
theorem exists_orthant_term_bound (hj : Function.Injective j) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : relativeSpace R a) (t : ℝ), 0 ≤ t →
      (∀ β : simpleRoots a P, t ≤ ⟪((β : a) : E), (Y : E)⟫) →
      ∀ (u : relativeSpace R a → ℂ) (A : ℝ), 0 ≤ A →
        (∀ H, (1 + ‖H‖) ^ (n + Fintype.card ι + 1) * ‖phaseFourier u H‖ ≤ A) →
        ∀ D : Set (ι → ℝ), MeasurableSet D →
          (∀ X ∈ D, ∃ β : simpleRoots a P, ∀ i, j i = β → X i ≤ 0) →
          ‖∫ X in D, phaseFourier u (Y - ∑ i, X i • chamberBasis hR ha hP (j i))‖ ≤
            C * A * ((1 + t) ^ n)⁻¹ := by
  let b := chamberBasis hR ha hP
  obtain ⟨c, hc, hlow⟩ := exists_chamber_coord_lower hR ha hP
  obtain ⟨Cb, hCb, hcoord⟩ := exists_chamber_coord_norm hR ha hP
  obtain ⟨C₁, hC₁, hdec⟩ := exists_integral_decay_bound ι n (inv_pos.mpr hCb)
  refine ⟨C₁ * (max 1 c⁻¹) ^ n, by positivity, fun Y t ht hY u A hA hu D hD hDβ => ?_⟩
  let y : simpleRoots a P → ℝ := fun β => b.repr Y β
  have hbound : ∀ X ∈ D, ‖phaseFourier u (Y - ∑ i, X i • b (j i))‖ ≤
      A * ((1 + Cb⁻¹ * max (c * t) ‖X - y ∘ j‖) ^ (n + Fintype.card ι + 1))⁻¹ := by
    intro X hX
    set Z := Y - ∑ i, X i • b (j i) with hZ
    have hrepr := chamberBasis_repr_orthant hR ha hP j Y X
    have h1 : ‖X - y ∘ j‖ ≤ Cb * ‖Z‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
      have hsum : (∑ i', if j i' = j i then X i' else 0) = X i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro i' _ hi'
          exact ite_eq_right_iff.mpr fun h => absurd (hj h) hi'
        · simp
      have hc' := hcoord Z (j i)
      rw [hrepr, hsum] at hc'
      rw [Real.norm_eq_abs, Pi.sub_apply, Function.comp_apply, abs_sub_comm]
      exact hc'
    have h2 : c * t ≤ Cb * ‖Z‖ := by
      obtain ⟨β, hβ⟩ := hDβ X hX
      have hneg : (∑ i, if j i = β then X i else 0) ≤ 0 :=
        Finset.sum_nonpos fun i _ => by split_ifs with h; exacts [hβ i h, le_refl _]
      have hc' := hcoord Z β
      rw [hrepr] at hc'
      have hl := hlow Y t ht hY β
      have := le_abs_self (y β - ∑ i, if j i = β then X i else 0)
      change |b.repr Y β - _| ≤ _ at hc'
      linarith
    have hmax : Cb⁻¹ * max (c * t) ‖X - y ∘ j‖ ≤ ‖Z‖ := by
      rw [inv_mul_le_iff₀ hCb]
      exact max_le h2 h1
    have hpos : 0 < (1 + ‖Z‖) ^ (n + Fintype.card ι + 1) := by positivity
    have hu' := hu Z
    calc ‖phaseFourier u Z‖ ≤ A * ((1 + ‖Z‖) ^ (n + Fintype.card ι + 1))⁻¹ := by
          rw [le_mul_inv_iff₀ hpos, mul_comm]; exact hu'
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
            (pow_le_pow_left₀ (by positivity) (by linarith) _)) hA
  have h := hdec _ D hD A (c * t) (y ∘ j) hA (by positivity) hbound
  calc _ ≤ C₁ * A * ((1 + c * t) ^ n)⁻¹ := h
    _ ≤ C₁ * A * ((max 1 c⁻¹) ^ n * ((1 + t) ^ n)⁻¹) :=
        mul_le_mul_of_nonneg_left (one_add_pow_inv_le hc ht n) (by positivity)
    _ = _ := by ring

include hR ha hP in
/-- **Integrability of the orthant integrands.** For injective `j : ι → Δ_P`, `Y ∈ 𝔞_M^G` and a
Schwartz function `u` with `(1 + ‖H‖)^{|ι| + 1} |phaseFourier u H| ≤ A`, the function
`X ↦ phaseFourier u (Y − ∑_i X_i v_{j(i)})` is integrable on `ℝ^ι`. -/
theorem integrable_orthant_phaseFourier (hj : Function.Injective j) (Y : relativeSpace R a)
    (u : 𝓢(relativeSpace R a, ℂ)) {A : ℝ}
    (hu : ∀ H, (1 + ‖H‖) ^ (Fintype.card ι + 1) * ‖phaseFourier u H‖ ≤ A) :
    Integrable (fun X : ι → ℝ => phaseFourier u (Y - ∑ i, X i • chamberBasis hR ha hP (j i))) := by
  let b := chamberBasis hR ha hP
  obtain ⟨Cb, hCb, hcoord⟩ := exists_chamber_coord_norm hR ha hP
  let y : simpleRoots a P → ℝ := fun β => b.repr Y β
  have hA : 0 ≤ A := le_trans (by positivity) (hu 0)
  have hw := ((integrable_decay_weight ι (inv_pos.mpr hCb)).comp_sub_right (y ∘ j)).const_mul A
  refine hw.mono' ?_ (ae_of_all _ fun X => ?_)
  · have hcont : Continuous (fun X : ι → ℝ => phaseFourier (u : relativeSpace R a → ℂ)
        (Y - ∑ i, X i • b (j i))) := by
      have h : (fun X : ι → ℝ => phaseFourier (u : relativeSpace R a → ℂ)
          (Y - ∑ i, X i • b (j i))) = fun X => 𝓕 u (-(2 * Real.pi)⁻¹ • (Y - ∑ i, X i • b (j i))) := by
        funext X; rw [phaseFourier_eq_fourier, SchwartzMap.fourier_coe]
      rw [h]
      exact (𝓕 u).continuous.comp (by fun_prop)
    exact hcont.aestronglyMeasurable
  · set Z := Y - ∑ i, X i • b (j i)
    have hrepr := chamberBasis_repr_orthant hR ha hP j Y X
    have h1 : ‖X - y ∘ j‖ ≤ Cb * ‖Z‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
      have hsum : (∑ i', if j i' = j i then X i' else 0) = X i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro i' _ hi'
          exact ite_eq_right_iff.mpr fun h => absurd (hj h) hi'
        · simp
      have hc' := hcoord Z (j i)
      rw [hrepr, hsum] at hc'
      rw [Real.norm_eq_abs, Pi.sub_apply, Function.comp_apply, abs_sub_comm]
      exact hc'
    have hmax : Cb⁻¹ * ‖X - y ∘ j‖ ≤ ‖Z‖ := by
      rw [inv_mul_le_iff₀ hCb]; exact h1
    have hpos : 0 < (1 + ‖Z‖) ^ (Fintype.card ι + 1) := by positivity
    calc ‖phaseFourier (u : relativeSpace R a → ℂ) Z‖
        ≤ A * ((1 + ‖Z‖) ^ (Fintype.card ι + 1))⁻¹ := by
          rw [le_mul_inv_iff₀ hpos, mul_comm]; exact hu Z
      _ ≤ A * ((1 + Cb⁻¹ * ‖X - y ∘ j‖) ^ (Fintype.card ι + 1))⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
            (pow_le_pow_left₀ (by positivity) (by linarith) _)) hA

end OrthantTerms

section Formula

omit [MeasurableSpace E] [BorelSpace E] in
/-- For a root set `R' ⊆ R` with Levi space `a`, a simple root of a chamber of `a` for `R'` does not
vanish at a point off the walls of `R`. -/
theorem apply_simpleRoot_ne_zero_of_offWalls {R' : Finset E} (hR' : IsRootSet R')
    (ha' : IsLeviSpace R' a) (hsub : R' ⊆ R) {S : Finset E} (hS : S ∈ parabolics R' a)
    {Λ : StrongDual ℝ a} (hΛ : OffWalls R a Λ) {v : a} (hv : v ∈ simpleRoots a S) : Λ v ≠ 0 := by
  have hli : LinearIndependent ℝ (fun v : simpleRoots a S => (v : a)) :=
    linearIndependent_simpleRoots hR' ha' hS
  obtain ⟨α, hα, hαv⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hv).1
  have hSR : S ⊆ R' := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hne : v ≠ 0 := hli.ne_zero ⟨v, hv⟩
  rw [← hαv] at hne ⊢
  exact hΛ α (hsub (hSR hα)) hne

omit [MeasurableSpace E] [BorelSpace E] in
theorem inner_relative_projection (x : relativeSpace R a) (h : E) :
    ⟪x, (relativeSpace R a).orthogonalProjectionOnto h⟫ = ⟪(x : E), h⟫ :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left x h

/-- **The integral of an exponential term in orthant coordinates.** Let `R' ⊆ R` be a root set with
Levi space `a` whose chambers have their simple roots among those of chambers of `R`, let the
points `y` give a `(G, M)`-family of exponentials for `R'`, let `ξ ∈ 𝔞_M^G` with `Λ_ξ` off the
walls, and let `u` be a Schwartz function with `(1 + ‖H‖)^{dim 𝔞_M^G + 1} |phaseFourier u H| ≤ A`.
Then the integral over `𝔞_M^G` of `c_M` of the family `e^{λ(y_S)}` at `Λ_x` against `u` is the sum
over the chambers `S` of `gram(Δ_S) · orthantSign(−Λ_ξ|_{Δ_S})` times the integral over the
oriented orthant `{−Λ_ξ(v) X_v > 0}` of `phaseFourier u` at the points
`pr_V(y_S − ∑_{v ∈ Δ_S} X_v v)`. -/
theorem integral_cM_exp_eq_orthants (hR : IsRootSet R) (ha : IsLeviSpace R a) {R' : Finset E}
    (hR' : IsRootSet R') (ha' : IsLeviSpace R' a) (hsub : R' ⊆ R)
    (hsimple : ∀ S ∈ parabolics R' a, ∃ P ∈ parabolics R a, simpleRoots a S ⊆ simpleRoots a P)
    (y : Finset E → a) (hy : IsFamily R' a (fun S Λ => exp (I * (Λ (y S) : ℂ))))
    (ξ : relativeSpace R a) (hξ : OffWalls R a (dualParam R a ξ))
    (u : 𝓢(relativeSpace R a, ℂ)) {A : ℝ}
    (hu : ∀ H, (1 + ‖H‖) ^ (Module.finrank ℝ (relativeSpace R a) + 1) * ‖phaseFourier u H‖ ≤ A) :
    ∫ x : relativeSpace R a, cM R' a (fun S Λ => exp (I * (Λ (y S) : ℂ))) (dualParam R a x) * u x =
      ∑ S ∈ parabolics R' a, (gramVolume (fun v : simpleRoots a S => ((v : a) : E)) : ℂ) *
        (orthantSign (fun v : simpleRoots a S => -dualParam R a ξ (v : a)) *
          ∫ X in orientedOrthant (fun v : simpleRoots a S => -dualParam R a ξ (v : a)),
            phaseFourier u ((relativeSpace R a).orthogonalProjectionOnto
              ((y S : E) - ∑ v : simpleRoots a S, X v • ((v : a) : E)))) := by
  let V := relativeSpace R a
  let pV := V.orthogonalProjectionOnto
  have hpoint (S : Finset E) (X : simpleRoots a S → ℝ) (x : V) :
      exp (I * ((-(∑ v : simpleRoots a S, X v * dualParam R a x (v : a)) : ℝ) : ℂ)) *
        (exp (I * (dualParam R a x (y S) : ℂ)) * u x) =
      u x * exp (I * (⟪x, pV ((y S : E) - ∑ v : simpleRoots a S, X v • ((v : a) : E))⟫ : ℂ)) := by
    rw [inner_relative_projection, inner_sub_right, inner_sum]
    simp only [real_inner_smul_right, dualParam_apply]
    rw [mul_comm (u x), ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hfun (S : Finset E) (X : simpleRoots a S → ℝ) :
      ∫ x : V, exp (I * ((-(∑ v : simpleRoots a S, X v * dualParam R a x (v : a)) : ℝ) : ℂ)) *
        (exp (I * (dualParam R a x (y S) : ℂ)) * u x) =
      phaseFourier u (pV ((y S : E) - ∑ v : simpleRoots a S, X v • ((v : a) : E))) :=
    integral_congr_ae (ae_of_all _ fun x => hpoint S X x)
  have hμ : ∀ S ∈ parabolics R' a, ∀ v ∈ simpleRoots a S, dualParam R a ξ v ≠ 0 :=
    fun S hS v hv => apply_simpleRoot_ne_zero_of_offWalls hR' ha' hsub hS hξ hv
  have hwall : ∀ᵐ x : V, ∀ S ∈ parabolics R' a, ∀ v ∈ simpleRoots a S, dualParam R a x v ≠ 0 :=
    (ae_offWalls ha).mono fun x hx S hS v hv =>
      apply_simpleRoot_ne_zero_of_offWalls hR' ha' hsub hS hx hv
  have hF : ∀ S ∈ parabolics R' a, IntegrableOn (fun X : simpleRoots a S → ℝ =>
      ∫ x : V, exp (I * ((-(∑ v : simpleRoots a S, X v * dualParam R a x (v : a)) : ℝ) : ℂ)) *
        (exp (I * (dualParam R a x (y S) : ℂ)) * u x))
      (orientedOrthant (fun v : simpleRoots a S => -dualParam R a ξ (v : a))) := by
    intro S hS
    obtain ⟨P, hP, hSP⟩ := hsimple S hS
    let b := chamberBasis hR ha hP
    let j : simpleRoots a S → simpleRoots a P := fun v => ⟨v, hSP v.property⟩
    have hj : Function.Injective j := fun v w h => Subtype.ext (congrArg Subtype.val h :)
    have hcard : Fintype.card (simpleRoots a S) ≤ Module.finrank ℝ V := by
      rw [Module.finrank_eq_card_basis b]
      exact Fintype.card_le_of_injective j hj
    have hu' : ∀ H, (1 + ‖H‖) ^ (Fintype.card (simpleRoots a S) + 1) *
        ‖phaseFourier (u : V → ℂ) H‖ ≤ A := fun H =>
      le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀
        (le_add_of_nonneg_right (norm_nonneg H)) (Nat.succ_le_succ hcard)) (norm_nonneg _)) (hu H)
    have hint := integrable_orthant_phaseFourier hR ha hP j hj (pV (y S)) u hu'
    have heq : (fun X : simpleRoots a S → ℝ =>
        ∫ x : V, exp (I * ((-(∑ v : simpleRoots a S, X v * dualParam R a x (v : a)) : ℝ) : ℂ)) *
          (exp (I * (dualParam R a x (y S) : ℂ)) * u x)) =
        fun X => phaseFourier u (pV (y S) - ∑ v, X v • b (j v)) := by
      funext X
      rw [hfun, map_sub, map_sum]
      congr 2
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [map_smul]
      congr 1
      have hb : ((b (j v) : V) : E) = ((v : a) : E) := chamberBasis_apply hR ha hP (j v)
      rw [← hb, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    rw [heq]
    exact hint.integrableOn
  rw [integral_cM_exp_mul (Ω := V) (ν := volume) hR' ha' y hy (dualParam R a ξ) hμ
    (dualParam R a) continuous_dualParam.measurable u.integrable hwall hF]
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 2
  exact setIntegral_congr_fun (Langlands.Analysis.measurableSet_orientedOrthant _) fun X _ => hfun S X

end Formula

end Langlands.GMFamily
