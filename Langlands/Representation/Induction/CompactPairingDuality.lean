import Langlands.Representation.Induction.CompactBilinearPairing
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Smooth.Contragredient.InvariantPairingProof
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Natural duality for normalized induction from a compact-picture integral

Conditional form of Casselman's compact-group pairing between normalized
inductions of a representation and of its smooth contragredient.
-/

noncomputable section

open MeasureTheory Topology
open scoped NNReal

namespace Langlands.Induction

universe uG uM uV uW

section Scalar

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A scalar function which is `δ`-covariant, equal to `c ≠ 0` on `x₀ L` and
supported in `P x₀ L` has nonzero compact average after translation by `x₀`. -/
theorem integral_ne_zero_of_doubleCoset (P : Subgroup G) (δ : P → ℝ≥0)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K) [μ.IsOpenPosMeasure]
    (ψ : G → ℂ) (hcov : ∀ (q : P) (x : G), ψ ((q : G) * x) = ((δ q : ℝ) : ℂ) * ψ x)
    (x₀ : G) (hint : Integrable (fun k : K => ψ ((k : G) * x₀)) μ)
    (L : OpenSubgroup G) (c : ℂ) (hc : c ≠ 0)
    (hval : ∀ l : L, ψ (x₀ * (l : G)) = c)
    (hsupp : ∀ y : G, ψ y ≠ 0 → ∃ (q : P) (l : L), y = (q : G) * x₀ * (l : G)) :
    (∫ k : K, ψ ((k : G) * x₀) ∂μ) ≠ 0 := by
  have hform : ∀ k : K, ∃ t : ℝ, 0 ≤ t ∧ ψ ((k : G) * x₀) = c * t := by
    intro k
    by_cases h0 : ψ ((k : G) * x₀) = 0
    · exact ⟨0, le_rfl, by simp [h0]⟩
    · obtain ⟨q, l, hql⟩ := hsupp _ h0
      refine ⟨(δ q : ℝ), (δ q).2, ?_⟩
      rw [hql, mul_assoc, hcov, hval, mul_comm]
  let r : K → ℝ := fun k => (ψ ((k : G) * x₀) / c).re
  have hr : ∀ k : K, ψ ((k : G) * x₀) = c * (r k : ℂ) := by
    intro k
    obtain ⟨t, -, ht⟩ := hform k
    simp only [r, ht, mul_div_cancel_left₀ _ hc, Complex.ofReal_re]
  have hr0 : 0 ≤ r := by
    intro k
    obtain ⟨t, ht0, ht⟩ := hform k
    simp only [Pi.zero_apply, r, ht, mul_div_cancel_left₀ _ hc, Complex.ofReal_re, ht0]
  have hrint : Integrable r μ := (hint.div_const c).re
  have hU : IsOpen {k : K | x₀⁻¹ * (k : G) * x₀ ∈ L} :=
    L.isOpen.preimage
      ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  have hUsupp : {k : K | x₀⁻¹ * (k : G) * x₀ ∈ L} ⊆ Function.support r := by
    intro k hk
    have h := hval ⟨x₀⁻¹ * (k : G) * x₀, hk⟩
    have hk1 : r k = 1 := by
      have he : (k : G) * x₀ = x₀ * (x₀⁻¹ * (k : G) * x₀) := by group
      simp only [r]
      rw [he, h, div_self hc, Complex.one_re]
    simp [Function.mem_support, hk1]
  have hpos : 0 < ∫ k, r k ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hr0 hrint]
    exact (hU.measure_pos μ ⟨1, by simp⟩).trans_le (measure_mono hUsupp)
  rw [integral_congr_ae (Filter.Eventually.of_forall hr), integral_const_mul,
    integral_complex_ofReal]
  exact mul_ne_zero hc (Complex.ofReal_ne_zero.mpr hpos.ne')

end Scalar

section Pairing

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (P : Subgroup G) (m : P →* M) (χ : P →* ℂˣ)

omit [IsTopologicalGroup G] in
/-- The coefficient pairing of induced functions from `σ` and its smooth dual
transforms by `χ q ^ 2` under left translation by `q ∈ P`. -/
theorem dualPairing_covariant (σ : Representation ℂ M V)
    (h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m)))
    (f : SmoothFunctions P (twist χ (σ.comp m))) (q : P) (x : G) :
    smoothDualPairing σ (eval P _ h ((q : G) * x)) (eval P _ f ((q : G) * x)) =
      ((χ q : ℂ) * χ q) * smoothDualPairing σ (eval P _ h x) (eval P _ f x) := by
  have hh : eval P _ h ((q : G) * x) =
      (χ q : ℂ) • smoothContragredient σ (m q) (eval P _ h x) := h.1.2 q x
  have hf : eval P _ f ((q : G) * x) = (χ q : ℂ) • σ (m q) (eval P _ f x) := f.1.2 q x
  rw [hh, hf, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, mul_comm (χ q : ℂ) (χ q : ℂ)]
  congr 1
  change (σ.dual (m q) (eval P _ h x).val) (σ (m q) (eval P _ f x)) = _
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rfl

end Pairing

section Sections

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {M : Type uM} [Group M] [TopologicalSpace M]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (P : Subgroup G)

/-- A vector fixed by an open subgroup of `M` is fixed, after inflation along a
continuous `m` and twisting by a character with open kernel, by an open subgroup
of `P`. -/
theorem exists_twist_comp_fixed (m : P →* M) (hm : Continuous m) (χ : P →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set P)) (π : Representation ℂ M W) (w : W)
    (H : OpenSubgroup M) (hw : w ∈ fixedVectors π H.toSubgroup) :
    ∃ H' : OpenSubgroup P, w ∈ fixedVectors (twist χ (π.comp m)) H'.toSubgroup := by
  let Hχ : OpenSubgroup P := ⟨χ.ker, hχ⟩
  refine ⟨H.comap m hm ⊓ Hχ, ?_⟩
  rintro ⟨q, hq⟩
  obtain ⟨hq₁, hq₂⟩ := OpenSubgroup.mem_inf.mp hq
  have hχq : χ q = 1 := hq₂
  change (χ q : ℂ) • π (m q) w = w
  rw [hχq, Units.val_one, one_smul]
  exact hw ⟨m q, hq₁⟩

section Compact

variable [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]

/-- A vector fixed by an open subgroup of `P` is fixed by `P ∩ x₀ L x₀⁻¹` for a
compact open subgroup `L` contained in any prescribed open subgroup `U`. -/
theorem exists_compact_conj_fixed (υ : Representation ℂ P W) (w : W)
    (H : OpenSubgroup P) (hw : w ∈ fixedVectors υ H.toSubgroup) (x₀ : G)
    (U : OpenSubgroup G) :
    ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ U ∧
      w ∈ fixedVectors υ (conjOpenSubgroup P L x₀).toSubgroup := by
  obtain ⟨O, hO, he⟩ := IsInducing.subtypeVal.isOpen_iff.mp H.isOpen
  have h1 : (1 : G) ∈ O := by
    have hh : (1 : P) ∈ (Subtype.val : P → G) ⁻¹' O :=
      (Set.ext_iff.mp he (1 : P)).mpr H.one_mem
    exact hh
  let N : Set G := (fun k => x₀ * k * x₀⁻¹) ⁻¹' O ∩ (U : Set G)
  have hN : N ∈ 𝓝 (1 : G) := by
    apply IsOpen.mem_nhds
    · exact (hO.preimage ((continuous_const.mul continuous_id).mul_const _)).inter U.isOpen
    · exact ⟨by simpa using h1, U.one_mem⟩
  obtain ⟨L, hL, hLN⟩ := compactOpenSubgroupBasis G N hN
  refine ⟨L, hL, fun l hl => (hLN hl).2, ?_⟩
  intro p
  have hp : x₀⁻¹ * ((p : P) : G) * x₀ ∈ L := mem_conjOpenSubgroup.mp p.property
  have hpO : ((p : P) : G) ∈ O := by
    simpa [mul_assoc] using (hLN hp).1
  have hpH : (p : P) ∈ H := (Set.ext_iff.mp he (p : P)).mp hpO
  exact hw ⟨p, hpH⟩

end Compact

variable [IsTopologicalGroup G]

/-- The double-coset section takes its prescribed value on all of `x₀ L`. -/
theorem compactDoubleCosetSection_apply_mul (υ : Representation ℂ P W)
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) (x₀ : G) (w : W)
    (hw : w ∈ fixedVectors υ (conjOpenSubgroup P L x₀).toSubgroup) (l : L) :
    eval P υ (compactDoubleCosetSection P υ L hL x₀ w hw).val (x₀ * (l : G)) = w := by
  simpa using compactDoubleCosetSection_apply P υ L hL x₀ w hw 1 l

/-- The double-coset section vanishes off `P x₀ L`. -/
theorem compactDoubleCosetSection_mem_of_ne_zero (υ : Representation ℂ P W)
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) (x₀ : G) (w : W)
    (hw : w ∈ fixedVectors υ (conjOpenSubgroup P L x₀).toSubgroup) (y : G)
    (hy : eval P υ (compactDoubleCosetSection P υ L hL x₀ w hw).val y ≠ 0) :
    ∃ (q : P) (l : L), y = (q : G) * x₀ * (l : G) := by
  obtain ⟨l, hl, he⟩ := compactDoubleCosetSection_support_subset P υ L hL x₀ w hw
    ⟨y, hy, rfl⟩
  have hq : y * (x₀ * l)⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  exact ⟨⟨_, hq⟩, ⟨l, hl⟩, by simp [mul_assoc]⟩

end Sections

section Separation

variable {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- With a cofinal supply of compact open subgroups, smooth functionals separate
the vectors of a smooth representation. -/
theorem exists_smoothDual_ne_zero
    (hcof : ∀ H : OpenSubgroup M, ∃ L : OpenSubgroup M, IsCompact (L : Set M) ∧ L ≤ H)
    (σ : Representation ℂ M V) (hσ : IsSmooth σ) (v : V) (hv : v ≠ 0) :
    ∃ lam : SmoothDual σ, smoothDualPairing σ lam v ≠ 0 := by
  by_contra h
  push Not at h
  apply hv
  apply smoothBidual_injective_of_compact_cofinal hcof σ hσ
  apply Subtype.ext
  apply LinearMap.ext
  intro lam
  rw [map_zero]
  exact h lam

omit [TopologicalSpace M] [IsTopologicalGroup M] in
/-- A nonzero functional is nonzero at some vector. -/
theorem exists_dual_apply_ne_zero {ρ : Representation ℂ M V} [TopologicalSpace M]
    (lam : SmoothDual ρ) (h : lam ≠ 0) : ∃ v : V, smoothDualPairing ρ lam v ≠ 0 := by
  by_contra hv
  push Not at hv
  apply h
  apply Subtype.ext
  apply LinearMap.ext
  exact hv

end Separation

section Nondegeneracy

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [WeaklyLocallyCompactSpace G]
variable {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (P : Subgroup G) (m : P →* M) (χ : P →* ℂˣ) (δ : P → ℝ≥0)
variable (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)

omit [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G] in
/-- A nonzero smooth induced function is nonzero at some point. -/
theorem exists_eval_ne_zero {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (υ : Representation ℂ P W) (f : SmoothFunctions P υ) (hf : f ≠ 0) :
    ∃ x : G, eval P υ f x ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact h x

/-- Right nondegeneracy of the compact-picture pairing: a nonzero induced
function from `σ` pairs nontrivially with some induced function from the smooth
dual of `σ`. -/
theorem integral_dualPairing_right_nondegenerate (hm : Continuous m)
    (hχ : IsOpen (χ.ker : Set P)) (hδ : ∀ q : P, (χ q : ℂ) * χ q = ((δ q : ℝ) : ℂ))
    (hcofM : ∀ H : OpenSubgroup M, ∃ L : OpenSubgroup M, IsCompact (L : Set M) ∧ L ≤ H)
    [μ.IsOpenPosMeasure]
    (hscalar : ∀ φ : G → ℂ, IsLocallyConstant φ →
      (∀ (q : P) (x : G), φ ((q : G) * x) = ((δ q : ℝ) : ℂ) * φ x) →
      ∀ g : G, Integrable (fun k : K => φ ((k : G) * g)) μ ∧
        (∫ k : K, φ ((k : G) * g) ∂μ) = ∫ k : K, φ (k : G) ∂μ)
    (σ : Representation ℂ M V) (hσ : IsSmooth σ)
    (f : SmoothFunctions P (twist χ (σ.comp m))) (hf : f ≠ 0) :
    ∃ h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m)),
      (∫ k : K, smoothDualPairing σ (eval P _ h k) (eval P _ f k) ∂μ) ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := exists_eval_ne_zero P _ f hf
  obtain ⟨lam, hlam⟩ := exists_smoothDual_ne_zero hcofM σ hσ _ hx₀
  obtain ⟨H, hH⟩ := lam.property
  have hlamH : lam ∈ fixedVectors (smoothContragredient σ) H.toSubgroup :=
    fun k => Subtype.ext (hH k)
  obtain ⟨H', hH'⟩ :=
    exists_twist_comp_fixed P m hm χ hχ (smoothContragredient σ) lam H hlamH
  obtain ⟨Kf, hKf⟩ := f.property
  obtain ⟨L, hL, hLK, hw⟩ := exists_compact_conj_fixed P _ lam H' hH' x₀ Kf
  let h := (compactDoubleCosetSection P (twist χ ((smoothContragredient σ).comp m))
    L hL x₀ lam hw).val
  refine ⟨h, ?_⟩
  let ψ : G → ℂ := fun y => smoothDualPairing σ (eval P _ h y) (eval P _ f y)
  have hcov : ∀ (q : P) (x : G), ψ ((q : G) * x) = ((δ q : ℝ) : ℂ) * ψ x := by
    intro q x
    simp only [ψ]
    rw [dualPairing_covariant, hδ]
  have hloc : IsLocallyConstant ψ :=
    bilinearPairing_isLocallyConstant P _ _ (smoothDualPairing σ) h f
  obtain ⟨hint, heq⟩ := hscalar ψ hloc hcov x₀
  have hne := integral_ne_zero_of_doubleCoset P δ K μ ψ hcov x₀ hint L
    (smoothDualPairing σ lam (eval P _ f x₀)) hlam ?_ ?_
  · rw [heq] at hne
    exact hne
  · intro l
    simp only [ψ, h]
    rw [compactDoubleCosetSection_apply_mul]
    congr 1
    exact congrArg (fun F => F.1 x₀) (hKf ⟨l, hLK l.2⟩)
  · intro y hy
    apply compactDoubleCosetSection_mem_of_ne_zero P _ L hL x₀ lam hw y
    intro h0
    apply hy
    simp only [ψ, h]
    rw [h0, map_zero, LinearMap.zero_apply]

/-- Left nondegeneracy of the compact-picture pairing: a nonzero induced
function from the smooth dual of `σ` pairs nontrivially with some induced
function from `σ`. -/
theorem integral_dualPairing_left_nondegenerate (hm : Continuous m)
    (hχ : IsOpen (χ.ker : Set P)) (hδ : ∀ q : P, (χ q : ℂ) * χ q = ((δ q : ℝ) : ℂ))
    [μ.IsOpenPosMeasure]
    (hscalar : ∀ φ : G → ℂ, IsLocallyConstant φ →
      (∀ (q : P) (x : G), φ ((q : G) * x) = ((δ q : ℝ) : ℂ) * φ x) →
      ∀ g : G, Integrable (fun k : K => φ ((k : G) * g)) μ ∧
        (∫ k : K, φ ((k : G) * g) ∂μ) = ∫ k : K, φ (k : G) ∂μ)
    (σ : Representation ℂ M V) (hσ : IsSmooth σ)
    (h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m))) (hh : h ≠ 0) :
    ∃ f : SmoothFunctions P (twist χ (σ.comp m)),
      (∫ k : K, smoothDualPairing σ (eval P _ h k) (eval P _ f k) ∂μ) ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := exists_eval_ne_zero P _ h hh
  obtain ⟨v, hv⟩ := exists_dual_apply_ne_zero _ hx₀
  obtain ⟨H, hH⟩ := hσ v
  obtain ⟨H', hH'⟩ := exists_twist_comp_fixed P m hm χ hχ σ v H hH
  obtain ⟨Kh, hKh⟩ := h.property
  obtain ⟨L, hL, hLK, hw⟩ := exists_compact_conj_fixed P _ v H' hH' x₀ Kh
  let f := (compactDoubleCosetSection P (twist χ (σ.comp m)) L hL x₀ v hw).val
  refine ⟨f, ?_⟩
  let ψ : G → ℂ := fun y => smoothDualPairing σ (eval P _ h y) (eval P _ f y)
  have hcov : ∀ (q : P) (x : G), ψ ((q : G) * x) = ((δ q : ℝ) : ℂ) * ψ x := by
    intro q x
    simp only [ψ]
    rw [dualPairing_covariant, hδ]
  have hloc : IsLocallyConstant ψ :=
    bilinearPairing_isLocallyConstant P _ _ (smoothDualPairing σ) h f
  obtain ⟨hint, heq⟩ := hscalar ψ hloc hcov x₀
  have hne := integral_ne_zero_of_doubleCoset P δ K μ ψ hcov x₀ hint L
    (smoothDualPairing σ (eval P _ h x₀) v) hv ?_ ?_
  · rw [heq] at hne
    exact hne
  · intro l
    simp only [ψ, f]
    rw [compactDoubleCosetSection_apply_mul]
    congr 2
    exact congrArg (fun F => F.1 x₀) (hKh ⟨l, hLK l.2⟩)
  · intro y hy
    apply compactDoubleCosetSection_mem_of_ne_zero P _ L hL x₀ v hw y
    intro h0
    apply hy
    simp only [ψ, f]
    rw [h0, map_zero]

/-- The compact-picture pairing identifies the smooth dual of the induction of
`σ` with the induction of the smooth dual of `σ`, whenever the former induction
is admissible. The equivalence is characterized by the integral formula. -/
theorem exists_integralDualEquiv (hm : Continuous m)
    (hχ : IsOpen (χ.ker : Set P)) (hδ : ∀ q : P, (χ q : ℂ) * χ q = ((δ q : ℝ) : ℂ))
    (hcofM : ∀ H : OpenSubgroup M, ∃ L : OpenSubgroup M, IsCompact (L : Set M) ∧ L ≤ H)
    [μ.IsOpenPosMeasure]
    (hscalar : ∀ φ : G → ℂ, IsLocallyConstant φ →
      (∀ (q : P) (x : G), φ ((q : G) * x) = ((δ q : ℝ) : ℂ) * φ x) →
      ∀ g : G, Integrable (fun k : K => φ ((k : G) * g)) μ ∧
        (∫ k : K, φ ((k : G) * g) ∂μ) = ∫ k : K, φ (k : G) ∂μ)
    (σ : Representation ℂ M V) (hσ : IsSmooth σ)
    (hadm : IsAdmissible (smoothInduced P (twist χ (σ.comp m)))) :
    ∃ E : Representation.Equiv (smoothContragredient (smoothInduced P (twist χ (σ.comp m))))
        (smoothInduced P (twist χ ((smoothContragredient σ).comp m))),
      ∀ (ℓ : SmoothDual (smoothInduced P (twist χ (σ.comp m))))
        (f : SmoothFunctions P (twist χ (σ.comp m))),
        smoothDualPairing _ ℓ f =
          ∫ k : K, smoothDualPairing σ (eval P _ (E ℓ) k) (eval P _ f k) ∂μ := by
  have hcofG : ∀ U : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ U := by
    intro U
    obtain ⟨L, hL, hLU⟩ := compactOpenSubgroupBasis G U U.mem_nhds_one
    exact ⟨L, hL, fun x hx => hLU hx⟩
  have hpair : ∀ (h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m)))
      (f : SmoothFunctions P (twist χ (σ.comp m))) (g : G),
      Integrable (fun k : K =>
        smoothDualPairing σ (eval P _ h ((k : G) * g)) (eval P _ f ((k : G) * g))) μ ∧
      (∫ k : K, smoothDualPairing σ (eval P _ h ((k : G) * g))
        (eval P _ f ((k : G) * g)) ∂μ) =
        ∫ k : K, smoothDualPairing σ (eval P _ h k) (eval P _ f k) ∂μ := by
    intro h f
    refine hscalar (fun y => smoothDualPairing σ (eval P _ h y) (eval P _ f y))
      (bilinearPairing_isLocallyConstant P _ _ (smoothDualPairing σ) h f) ?_
    intro q x
    rw [dualPairing_covariant, hδ]
  have hint : ∀ (h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m)))
      (f : SmoothFunctions P (twist χ (σ.comp m))),
      Integrable (fun k : K => smoothDualPairing σ (eval P _ h k) (eval P _ f k)) μ := by
    intro h f
    simpa only [mul_one] using (hpair h f 1).1
  let b := integralBilinearPairing P _ _ (smoothDualPairing σ) K μ hint
  have hb : ∀ (g : G) (h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m)))
      (f : SmoothFunctions P (twist χ (σ.comp m))),
      b (smoothInduced P _ g h) (smoothInduced P _ g f) = b h f := by
    intro g h f
    exact (hpair h f g).2
  have hleft : ∀ h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m)),
      (∀ f : SmoothFunctions P (twist χ (σ.comp m)), b h f = 0) → h = 0 := by
    intro h hh
    by_contra hne
    obtain ⟨f, hf⟩ := integral_dualPairing_left_nondegenerate P m χ δ K μ hm hχ hδ hscalar
      σ hσ h hne
    exact hf (hh f)
  have hright : ∀ f : SmoothFunctions P (twist χ (σ.comp m)),
      (∀ h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m)), b h f = 0) →
        f = 0 := by
    intro f hf
    by_contra hne
    obtain ⟨h, hh⟩ := integral_dualPairing_right_nondegenerate P m χ δ K μ hm hχ hδ hcofM
      hscalar σ hσ f hne
    exact hh (hf h)
  obtain ⟨E', hE'⟩ := smoothInvariantPairingDuality hcofG _ _ hadm
    (smoothInduced_smooth P _) b hb hleft hright
  refine ⟨E'.symm, fun ℓ f => ?_⟩
  conv_lhs => rw [← E'.apply_symm_apply ℓ]
  exact hE' _ f

end Nondegeneracy

section Naturality

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (P : Subgroup G) (m : P →* M) (χ : P →* ℂˣ)
variable (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)

/-- Equivalences characterized by the compact-picture integral are natural for
coefficient maps `A` and `A'` that are adjoint for the smooth dual pairings. -/
theorem integralDualEquiv_natural (σ : Representation ℂ M V) (τ : Representation ℂ M W)
    (Eσ : Representation.Equiv
      (smoothContragredient (smoothInduced P (twist χ (σ.comp m))))
      (smoothInduced P (twist χ ((smoothContragredient σ).comp m))))
    (Eτ : Representation.Equiv
      (smoothContragredient (smoothInduced P (twist χ (τ.comp m))))
      (smoothInduced P (twist χ ((smoothContragredient τ).comp m))))
    (hEσ : ∀ (ℓ : SmoothDual (smoothInduced P (twist χ (σ.comp m))))
      (f : SmoothFunctions P (twist χ (σ.comp m))),
      smoothDualPairing _ ℓ f =
        ∫ k : K, smoothDualPairing σ (eval P _ (Eσ ℓ) k) (eval P _ f k) ∂μ)
    (hEτ : ∀ (ℓ : SmoothDual (smoothInduced P (twist χ (τ.comp m))))
      (f : SmoothFunctions P (twist χ (τ.comp m))),
      smoothDualPairing _ ℓ f =
        ∫ k : K, smoothDualPairing τ (eval P _ (Eτ ℓ) k) (eval P _ f k) ∂μ)
    (A : (twist χ (σ.comp m)).IntertwiningMap (twist χ (τ.comp m)))
    (A' : (twist χ ((smoothContragredient τ).comp m)).IntertwiningMap
      (twist χ ((smoothContragredient σ).comp m)))
    (hA : ∀ (lam : SmoothDual τ) (v : V),
      smoothDualPairing σ (A' lam) v = smoothDualPairing τ lam (A v))
    (ℓ : SmoothDual (smoothInduced P (twist χ (τ.comp m)))) :
    Eσ (contragredientMap (smoothInducedMap P A) ℓ) = smoothInducedMap P A' (Eτ ℓ) := by
  rw [← Eσ.apply_symm_apply (smoothInducedMap P A' (Eτ ℓ))]
  congr 1
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  change smoothDualPairing _ ℓ (smoothInducedMap P A f) =
    smoothDualPairing _ (Eσ.symm (smoothInducedMap P A' (Eτ ℓ))) f
  rw [hEσ, Eσ.apply_symm_apply, hEτ]
  congr 1
  funext k
  exact (hA _ _).symm

end Naturality

end Langlands.Induction
