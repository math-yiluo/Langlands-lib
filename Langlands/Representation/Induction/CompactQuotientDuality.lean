import Langlands.Representation.Induction.CompactPairingDuality
import Langlands.Representation.Induction.CompactQuotientProof
import Mathlib.MeasureTheory.Group.ModularCharacter

/-!
# Natural duality for normalized induction from a compact quotient

Inputs for Casselman's pairing between normalized inductions of a representation
and of its smooth contragredient, for a closed subgroup `P` of a unimodular,
locally compact, Hausdorff nonarchimedean group `G` with `P \ G` compact. No
decomposition `G = P K` is used.

* `exists_integralDualEquiv_of_pos`: the duality equivalence of
  `exists_integralDualEquiv` (module `CompactPairingDuality`), for a measure on `K`
  that is only positive on open neighbourhoods of `1`.
* `integral_bruhat_eq`: the Bruhat-function identity behind the invariant
  functional on `P \ G`.
* `bruhatMeasure` and `exists_compactQuotient_measure`: a measure on
  `⊤ : Subgroup G`, given by a Bruhat density against Haar measure, whose integral
  is right invariant on locally constant functions that are left covariant under
  `P` by Mathlib's modular character of `P`.
-/

noncomputable section

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace Langlands.Induction

universe uG uM uV uW

section Scalar

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A scalar function which is `δ`-covariant, equal to `c ≠ 0` on `x₀ L` and
supported in `P x₀ L` has nonzero average after translation by `x₀`, for a
measure on `K` which is positive on open neighbourhoods of `1`. -/
theorem integral_ne_zero_of_doubleCoset_of_pos (P : Subgroup G) (δ : P → ℝ≥0)
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hpos : ∀ U : Set K, IsOpen U → (1 : K) ∈ U → 0 < μ U)
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
  have hrpos : 0 < ∫ k, r k ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hr0 hrint]
    exact (hpos _ hU (by simp)).trans_le (measure_mono hUsupp)
  rw [integral_congr_ae (Filter.Eventually.of_forall hr), integral_const_mul,
    integral_complex_ofReal]
  exact mul_ne_zero hc (Complex.ofReal_ne_zero.mpr hrpos.ne')

end Scalar

section Nondegeneracy

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [WeaklyLocallyCompactSpace G]
variable {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (P : Subgroup G) (m : P →* M) (χ : P →* ℂˣ) (δ : P → ℝ≥0)
variable (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)

/-- Right nondegeneracy of the integral pairing for a measure positive on open
neighbourhoods of `1`: a nonzero induced function from `σ` pairs nontrivially
with some induced function from the smooth dual of `σ`. -/
theorem integral_dualPairing_right_nondegenerate_of_pos (hm : Continuous m)
    (hχ : IsOpen (χ.ker : Set P)) (hδ : ∀ q : P, (χ q : ℂ) * χ q = ((δ q : ℝ) : ℂ))
    (hcofM : ∀ H : OpenSubgroup M, ∃ L : OpenSubgroup M, IsCompact (L : Set M) ∧ L ≤ H)
    (hpos : ∀ U : Set K, IsOpen U → (1 : K) ∈ U → 0 < μ U)
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
  have hne := integral_ne_zero_of_doubleCoset_of_pos P δ K μ hpos ψ hcov x₀ hint L
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

/-- Left nondegeneracy of the integral pairing for a measure positive on open
neighbourhoods of `1`: a nonzero induced function from the smooth dual of `σ`
pairs nontrivially with some induced function from `σ`. -/
theorem integral_dualPairing_left_nondegenerate_of_pos (hm : Continuous m)
    (hχ : IsOpen (χ.ker : Set P)) (hδ : ∀ q : P, (χ q : ℂ) * χ q = ((δ q : ℝ) : ℂ))
    (hpos : ∀ U : Set K, IsOpen U → (1 : K) ∈ U → 0 < μ U)
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
  have hne := integral_ne_zero_of_doubleCoset_of_pos P δ K μ hpos ψ hcov x₀ hint L
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

/-- An invariant integral pairing, for a measure on `K` positive on open
neighbourhoods of `1`, identifies the smooth dual of the induction of `σ` with
the induction of the smooth dual of `σ`, whenever the former induction is
admissible. The equivalence is characterized by the integral formula. -/
theorem exists_integralDualEquiv_of_pos (hm : Continuous m)
    (hχ : IsOpen (χ.ker : Set P)) (hδ : ∀ q : P, (χ q : ℂ) * χ q = ((δ q : ℝ) : ℂ))
    (hcofM : ∀ H : OpenSubgroup M, ∃ L : OpenSubgroup M, IsCompact (L : Set M) ∧ L ≤ H)
    (hpos : ∀ U : Set K, IsOpen U → (1 : K) ∈ U → 0 < μ U)
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
    obtain ⟨f, hf⟩ := integral_dualPairing_left_nondegenerate_of_pos P m χ δ K μ hm hχ hδ
      hpos hscalar σ hσ h hne
    exact hf (hh f)
  have hright : ∀ f : SmoothFunctions P (twist χ (σ.comp m)),
      (∀ h : SmoothFunctions P (twist χ ((smoothContragredient σ).comp m)), b h f = 0) →
        f = 0 := by
    intro f hf
    by_contra hne
    obtain ⟨h, hh⟩ := integral_dualPairing_right_nondegenerate_of_pos P m χ δ K μ hm hχ hδ hcofM
      hpos hscalar σ hσ f hne
    exact hh (hf h)
  obtain ⟨E', hE'⟩ := smoothInvariantPairingDuality hcofG _ _ hadm
    (smoothInduced_smooth P _) b hb hleft hright
  refine ⟨E'.symm, fun ℓ f => ?_⟩
  conv_lhs => rw [← E'.apply_symm_apply ℓ]
  exact hE' _ f

end Nondegeneracy

section Modular

open Measure

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Right translation scales the Haar measure by Mathlib's modular character. Unlike
`ModularCompactAverage.map_mul_right_eq_modularCharacter_smul`, this needs no second
countability, because `haar` is regular. -/
theorem map_mul_right_haar_eq [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (q : H) : map (· * q) (haar : Measure H) = modularCharacter q • haar := by
  change _ = modularCharacterFun q • _
  rw [modularCharacterFun_eq_haarScalarFactor haar q]
  have : (map (· * q) (haar : Measure H)).Regular := Regular.map (Homeomorph.mulRight q)
  exact isMulLeftInvariant_eq_smul_of_regular _ _

/-- Right translation of an integral against the Haar measure. -/
theorem integral_mul_right_haar [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : H → E) (q : H) :
    ∫ x, f (x * q) ∂(haar : Measure H) = (modularCharacter q : ℝ) • ∫ x, f x ∂haar := by
  have h := (measurableEmbedding_mulRight q).integral_map (μ := (haar : Measure H)) f
  rw [map_mul_right_haar_eq, integral_smul_nnreal_measure] at h
  rw [← h, NNReal.smul_def]

/-- The modular character is trivial on every compact open subgroup. -/
theorem modularCharacter_eq_one_of_isCompact [LocallyCompactSpace H] (U : Subgroup H)
    (hUo : IsOpen (U : Set H)) (hUc : IsCompact (U : Set H)) {u : H} (hu : u ∈ U) :
    modularCharacter u = 1 := by
  borelize H
  let μ : Measure H := haar
  have hmap := map_mul_right_haar_eq (H := H) u
  have hpre : (· * u) ⁻¹' (U : Set H) = U := by
    ext x
    simp [U.mul_mem_cancel_right hu]
  have h := congrArg (fun ν : Measure H => ν U) hmap
  simp only [Measure.smul_apply, nnreal_smul_coe_apply] at h
  rw [map_apply (measurable_mul_const u) hUo.measurableSet, hpre] at h
  have hpos : μ U ≠ 0 := (hUo.measure_pos μ ⟨1, U.one_mem⟩).ne'
  have hfin : μ U ≠ ∞ := hUc.measure_lt_top.ne
  have h1 : ((modularCharacter u : ℝ≥0) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_eq_right hpos hfin).mp h.symm
  exact_mod_cast h1

/-- A function invariant under right translation by an open subgroup is locally
constant. -/
theorem isLocallyConstant_of_mul_right {X : Type*} (U : Subgroup H)
    (hU : IsOpen (U : Set H)) (f : H → X) (hf : ∀ x : H, ∀ u ∈ U, f (x * u) = f x) :
    IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun k => x * k) '' (U : Set H), isOpenMap_mul_left x _ hU,
    ⟨1, U.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hf x u hu

/-- The modular character of a locally compact group with a compact open subgroup
is locally constant. -/
theorem isLocallyConstant_modularCharacter [LocallyCompactSpace H] (U : Subgroup H)
    (hUo : IsOpen (U : Set H)) (hUc : IsCompact (U : Set H)) :
    IsLocallyConstant (fun x : H => modularCharacter x) :=
  isLocallyConstant_of_mul_right U hUo _ fun x u hu => by
    rw [map_mul, modularCharacter_eq_one_of_isCompact U hUo hUc hu, mul_one]

end Modular

section Bruhat

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The Bruhat-function identity behind the invariant functional on `P \ G`. Let `μ`
be a left invariant measure on `G` and `ν` a measure on the closed subgroup `P`.
Let `β₁` be normalized by `∫_P β₁ (p x) Δ(p) dν = 1` and `β` by
`∫_P β (p⁻¹ x) dν = 1`. Then `β` and `β₁` integrate every continuous
`Δ`-covariant function `φ` to the same value. -/
theorem integral_bruhat_eq [T2Space G] [MeasurableSpace G] [BorelSpace G] (P : Subgroup G)
    (hP : IsClosed (P : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (ν : Measure P) [IsFiniteMeasureOnCompacts ν]
    (Δ : P → ℝ) (hΔ : Continuous Δ) (hΔmul : ∀ p : P, Δ p⁻¹ * Δ p = 1)
    (β β₁ : G → ℝ) (hβ : Continuous β) (hβs : HasCompactSupport β)
    (hβ₁ : Continuous β₁) (hβ₁s : HasCompactSupport β₁)
    (hA : ∀ x : G, ∫ p : P, β₁ ((p : G) * x) * Δ p ∂ν = 1)
    (hB : ∀ x : G, ∫ p : P, β ((p : G)⁻¹ * x) ∂ν = 1)
    (φ : G → ℂ) (hφ : Continuous φ)
    (hcov : ∀ (q : P) (x : G), φ ((q : G) * x) = (Δ q : ℂ) * φ x) :
    ∫ x, (β x : ℂ) * φ x ∂μ = ∫ x, (β₁ x : ℂ) * φ x ∂μ := by
  let S : Set G := (fun z : G × G => z.1 * z.2⁻¹) '' (tsupport β₁ ×ˢ tsupport β)
  have hS : IsCompact S :=
    (hβ₁s.isCompact.prod hβs.isCompact).image (continuous_fst.mul continuous_snd.inv)
  have hSP : IsCompact (((↑) : P → G) ⁻¹' S) :=
    hP.isClosedEmbedding_subtypeVal.isCompact_preimage hS
  let F₁ : G → P → ℂ := fun y p => (β y : ℂ) * φ y * ((β₁ ((p : G) * y) * Δ p : ℝ) : ℂ)
  let F₂ : G → P → ℂ := fun x p => (β ((p : G)⁻¹ * x) : ℂ) * (φ x * (β₁ x : ℂ))
  have hF₁c : Continuous F₁.uncurry := by
    change Continuous (fun z : G × P => F₁ z.1 z.2)
    simp only [F₁]
    fun_prop
  have hF₂c : Continuous F₂.uncurry := by
    change Continuous (fun z : G × P => F₂ z.1 z.2)
    simp only [F₂]
    fun_prop
  have hF₁s : HasCompactSupport F₁.uncurry := by
    refine HasCompactSupport.intro (hβs.isCompact.prod hSP) ?_
    rintro ⟨y, p⟩ hyp
    change F₁ y p = 0
    by_cases hy : β y = 0
    · simp [F₁, hy]
    by_cases hpy : β₁ ((p : G) * y) = 0
    · simp [F₁, hpy]
    exfalso
    apply hyp
    refine ⟨subset_tsupport _ hy,
      ⟨((p : G) * y, y), ⟨subset_tsupport _ hpy, subset_tsupport _ hy⟩, ?_⟩⟩
    simp
  have hF₂s : HasCompactSupport F₂.uncurry := by
    refine HasCompactSupport.intro (hβ₁s.isCompact.prod hSP) ?_
    rintro ⟨x, p⟩ hxp
    change F₂ x p = 0
    by_cases hx : β₁ x = 0
    · simp [F₂, hx]
    by_cases hpx : β ((p : G)⁻¹ * x) = 0
    · simp [F₂, hpx]
    exfalso
    apply hxp
    refine ⟨subset_tsupport _ hx,
      ⟨(x, (p : G)⁻¹ * x), ⟨subset_tsupport _ hx, subset_tsupport _ hpx⟩, ?_⟩⟩
    simp
  have step1 : ∀ y : G, (β y : ℂ) * φ y = ∫ p, F₁ y p ∂ν := by
    intro y
    simp only [F₁]
    rw [integral_const_mul, integral_complex_ofReal, hA y, Complex.ofReal_one, mul_one]
  have step2 : ∀ p : P, ∫ y, F₁ y p ∂μ = ∫ x, F₂ x p ∂μ := by
    intro p
    refine (integral_mul_left_eq_self (μ := μ) (fun y => F₁ y p) ((p : G)⁻¹)).symm.trans ?_
    congr 1
    ext x
    have h1 := hcov p⁻¹ x
    rw [Subgroup.coe_inv] at h1
    have h2 : ((Δ p⁻¹ : ℝ) : ℂ) * (Δ p : ℂ) = 1 := by exact_mod_cast hΔmul p
    simp only [F₁, F₂, mul_inv_cancel_left, h1, Complex.ofReal_mul]
    linear_combination ((β ((p : G)⁻¹ * x) : ℂ) * φ x * (β₁ x : ℂ)) * h2
  have step3 : ∀ x : G, ∫ p, F₂ x p ∂ν = φ x * (β₁ x : ℂ) := by
    intro x
    simp only [F₂]
    rw [integral_mul_const, integral_complex_ofReal, hB x, Complex.ofReal_one, one_mul]
  calc ∫ x, (β x : ℂ) * φ x ∂μ = ∫ y, ∫ p, F₁ y p ∂ν ∂μ := by
        congr 1 with y
        exact step1 y
    _ = ∫ p, ∫ y, F₁ y p ∂μ ∂ν := integral_integral_swap_of_hasCompactSupport hF₁c hF₁s
    _ = ∫ p, ∫ x, F₂ x p ∂μ ∂ν := by
        congr 1 with p
        exact step2 p
    _ = ∫ x, ∫ p, F₂ x p ∂ν ∂μ := (integral_integral_swap_of_hasCompactSupport hF₂c hF₂s).symm
    _ = ∫ x, (β₁ x : ℂ) * φ x ∂μ := by
        congr 1 with x
        rw [step3, mul_comm]

end Bruhat

section Construction

open Measure

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]

/-- On a closed subgroup of a locally compact nonarchimedean group, the modular
character is continuous: it is trivial on a compact open subgroup. -/
theorem continuous_modularCharacter_of_isClosed [LocallyCompactSpace G] (P : Subgroup G)
    (hP : IsClosed (P : Set G)) [LocallyCompactSpace P] :
    Continuous (fun p : P => (modularCharacter p : ℝ)) := by
  obtain ⟨K₀, hK₀c, -⟩ := compactOpenSubgroupBasis G Set.univ Filter.univ_mem
  exact NNReal.continuous_coe.comp (isLocallyConstant_modularCharacter
    ((K₀ : Subgroup G).comap P.subtype) (K₀.isOpen.preimage continuous_subtype_val)
    (hP.isClosedEmbedding_subtypeVal.isCompact_preimage hK₀c)).continuous

omit [NonarchimedeanGroup G] in
/-- The modular character takes inverse values at `p⁻¹` and `p`. -/
theorem modularCharacter_inv_mul_self [IsTopologicalGroup G] [LocallyCompactSpace G] (p : G) :
    (modularCharacter p⁻¹ : ℝ) * modularCharacter p = 1 := by
  rw [← NNReal.coe_mul, ← map_mul, inv_mul_cancel, map_one, NNReal.coe_one]

/-- Bruhat functions for a closed subgroup `P` with compact quotient `P \ G`.
`β₁` is normalized by the `Δ_P`-weighted average `∫_P β₁ (p x) Δ_P(p) dp = 1`.
`β₂` is nonnegative, positive on an open neighbourhood of `1`, and normalized by
`∫_P β₂ (p⁻¹ x) dp = 1`. Both are continuous with compact support. -/
theorem exists_bruhat_functions [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (P : Subgroup G) (hP : IsClosed (P : Set G)) [LocallyCompactSpace P]
    [CompactSpace (LeftQuotient P)] :
    ∃ (β₁ β₂ : G → ℝ) (W : Set G), Continuous β₁ ∧ HasCompactSupport β₁ ∧
      Continuous β₂ ∧ HasCompactSupport β₂ ∧ 0 ≤ β₂ ∧ IsOpen W ∧ (1 : G) ∈ W ∧
      (∀ x ∈ W, 0 < β₂ x) ∧
      (∀ x : G, ∫ p : P, β₁ ((p : G) * x) * (modularCharacter p : ℝ) ∂(haar : Measure P) = 1) ∧
      (∀ x : G, ∫ p : P, β₂ ((p : G)⁻¹ * x) ∂(haar : Measure P) = 1) := by
  classical
  obtain ⟨K₀, hK₀c, -⟩ := compactOpenSubgroupBasis G Set.univ Filter.univ_mem
  obtain ⟨t, ht⟩ := exists_finset_doubleCoset_cover P K₀
  -- The compact open set `C = ⋃_{i ∈ {1} ∪ t} i K₀` meets every coset `P x`.
  let s : Finset G := insert 1 t
  let C : Set G := {x | ∃ i ∈ s, i⁻¹ * x ∈ (K₀ : Set G)}
  have hCeq : C = ⋃ i ∈ s, (fun x => i⁻¹ * x) ⁻¹' (K₀ : Set G) := by
    ext x
    simp [C]
  have hCo : IsOpen C := by
    rw [hCeq]
    exact isOpen_biUnion fun i _ => K₀.isOpen.preimage (continuous_const.mul continuous_id)
  have hCc : IsCompact C := by
    rw [hCeq]
    exact s.isCompact_biUnion fun i _ =>
      (Homeomorph.mulLeft i⁻¹).isCompact_preimage.mpr hK₀c
  have hC1 : (1 : G) ∈ C := ⟨1, Finset.mem_insert_self 1 t, by simp⟩
  have hCK : ∀ x : G, ∀ k ∈ (K₀ : Subgroup G), (x * k ∈ C ↔ x ∈ C) := by
    intro x k hk
    have hk' : k ∈ K₀ := hk
    simp only [C, Set.mem_ofPred_eq, ← mul_assoc, SetLike.mem_coe, mul_mem_cancel_right hk']
  have hCP : ∀ x : G, ∃ p ∈ P, p⁻¹ * x ∈ C := by
    intro x
    obtain ⟨i, hi, p, hp, k, hk, rfl⟩ := ht x
    exact ⟨p, hp, i, Finset.mem_insert_of_mem hi, by simpa [mul_assoc] using hk⟩
  -- The indicator of `C`.
  let c : G → ℝ := C.indicator fun _ => 1
  have hcK : ∀ x : G, ∀ k ∈ (K₀ : Subgroup G), c (x * k) = c x := by
    intro x k hk
    change C.indicator (fun _ => (1 : ℝ)) (x * k) = C.indicator (fun _ => (1 : ℝ)) x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hCK x k hk).mpr hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem fun h => hx ((hCK x k hk).mp h)]
  have hc0 : ∀ x, 0 ≤ c x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hc1 : ∀ x ∈ C, c x = 1 := fun x hx => Set.indicator_of_mem hx _
  have hcC : ∀ x, x ∉ C → c x = 0 := fun x hx => Set.indicator_of_notMem hx _
  have hcc : Continuous c := (isLocallyConstant_of_mul_right _ K₀.isOpen c hcK).continuous
  -- The two `P`-averages of `c`.
  let ν : Measure P := haar
  let Δ : P → ℝ := fun p => (modularCharacter p : ℝ)
  have hΔc : Continuous Δ := continuous_modularCharacter_of_isClosed P hP
  have hΔpos : ∀ p : P, 0 < Δ p := fun p => NNReal.coe_pos.mpr (modularCharacterFun_pos p)
  have hΔmul : ∀ p q : P, Δ (p * q) = Δ p * Δ q := fun p q => by
    simp only [Δ, map_mul, NNReal.coe_mul]
  let Ac : G → ℝ := fun x => ∫ p : P, c ((p : G) * x) * Δ p ∂ν
  let Bc : G → ℝ := fun x => ∫ p : P, c ((p : G)⁻¹ * x) ∂ν
  have hAcK : ∀ x : G, ∀ k ∈ (K₀ : Subgroup G), Ac (x * k) = Ac x := by
    intro x k hk
    simp only [Ac, ← mul_assoc, fun y => hcK y k hk]
  have hBcK : ∀ x : G, ∀ k ∈ (K₀ : Subgroup G), Bc (x * k) = Bc x := by
    intro x k hk
    simp only [Bc, ← mul_assoc, fun y => hcK y k hk]
  have hAcP : ∀ (q : P) (x : G), Ac ((q : G) * x) = Ac x := by
    intro q x
    have h : ∫ p : P, c (((p * q⁻¹ : P) : G) * ((q : G) * x)) * Δ (p * q⁻¹) ∂ν =
        Δ q⁻¹ * Ac ((q : G) * x) :=
      integral_mul_right_haar (fun p : P => c ((p : G) * ((q : G) * x)) * Δ p) q⁻¹
    have h' : ∀ p : P, c (((p * q⁻¹ : P) : G) * ((q : G) * x)) * Δ (p * q⁻¹) =
        c ((p : G) * x) * Δ p * Δ q⁻¹ := by
      intro p
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left, hΔmul]
    simp only [h', integral_mul_const] at h
    change Ac x * Δ q⁻¹ = Δ q⁻¹ * Ac ((q : G) * x) at h
    exact mul_left_cancel₀ (hΔpos q⁻¹).ne' (h.symm.trans (mul_comm _ _))
  have hBcP : ∀ (q : P) (x : G), Bc ((q : G) * x) = Bc x := by
    intro q x
    have h : ∫ p : P, c (((q * p : P) : G)⁻¹ * ((q : G) * x)) ∂ν = Bc ((q : G) * x) :=
      integral_mul_left_eq_self (fun p : P => c ((p : G)⁻¹ * ((q : G) * x))) q
    have h' : ∀ p : P, c (((q * p : P) : G)⁻¹ * ((q : G) * x)) = c ((p : G)⁻¹ * x) := by
      intro p
      rw [Subgroup.coe_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    simp only [h'] at h
    exact h.symm
  have hAcpos : ∀ x : G, 0 < Ac x := by
    intro x
    obtain ⟨p₀, hp₀, hp₀C⟩ := hCP x
    have hsupp : IsCompact (((↑) : P → G) ⁻¹' ((fun y => y * x⁻¹) '' C)) :=
      hP.isClosedEmbedding_subtypeVal.isCompact_preimage
        (hCc.image (continuous_id.mul continuous_const))
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := (⟨p₀, hp₀⟩ : P)⁻¹) ?_ ?_ ?_ ?_
    · exact (hcc.comp (continuous_subtype_val.mul continuous_const)).mul hΔc
    · refine HasCompactSupport.intro hsupp fun p hp => ?_
      rw [hcC _ ?_, zero_mul]
      intro hpx
      exact hp ⟨(p : G) * x, hpx, by simp⟩
    · exact fun p => mul_nonneg (hc0 _) (hΔpos p).le
    · rw [hc1 _ (by simpa using hp₀C), one_mul]
      exact (hΔpos _).ne'
  have hBcpos : ∀ x : G, 0 < Bc x := by
    intro x
    obtain ⟨p₀, hp₀, hp₀C⟩ := hCP x
    have hsupp : IsCompact (((↑) : P → G) ⁻¹' ((fun y => x * y⁻¹) '' C)) :=
      hP.isClosedEmbedding_subtypeVal.isCompact_preimage
        (hCc.image (continuous_const.mul continuous_inv))
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := (⟨p₀, hp₀⟩ : P)) ?_ ?_ ?_ ?_
    · exact hcc.comp (continuous_subtype_val.inv.mul continuous_const)
    · exact HasCompactSupport.intro hsupp fun p hp =>
        hcC _ fun hpx => hp ⟨(p : G)⁻¹ * x, hpx, by simp⟩
    · exact fun p => hc0 _
    · rw [hc1 _ hp₀C]
      exact one_ne_zero
  -- The normalized Bruhat functions.
  let β₁ : G → ℝ := fun x => c x / Ac x
  let β₂ : G → ℝ := fun x => c x / Bc x
  have hβ₁K : ∀ x : G, ∀ k ∈ (K₀ : Subgroup G), β₁ (x * k) = β₁ x := fun x k hk => by
    simp only [β₁, hcK x k hk, hAcK x k hk]
  have hβ₂K : ∀ x : G, ∀ k ∈ (K₀ : Subgroup G), β₂ (x * k) = β₂ x := fun x k hk => by
    simp only [β₂, hcK x k hk, hBcK x k hk]
  refine ⟨β₁, β₂, C, (isLocallyConstant_of_mul_right _ K₀.isOpen β₁ hβ₁K).continuous,
    HasCompactSupport.intro hCc fun x hx => by simp only [β₁, hcC x hx, zero_div],
    (isLocallyConstant_of_mul_right _ K₀.isOpen β₂ hβ₂K).continuous,
    HasCompactSupport.intro hCc fun x hx => by simp only [β₂, hcC x hx, zero_div],
    fun x => div_nonneg (hc0 x) (hBcpos x).le, hCo, hC1, ?_, ?_, ?_⟩
  · intro x hx
    simp only [β₂, hc1 x hx]
    exact one_div_pos.mpr (hBcpos x)
  · intro x
    have h : ∀ p : P, β₁ ((p : G) * x) * Δ p = c ((p : G) * x) * Δ p / Ac x := by
      intro p
      simp only [β₁, hAcP p x]
      ring
    change ∫ p : P, β₁ ((p : G) * x) * Δ p ∂ν = 1
    simp only [h]
    rw [integral_div]
    exact div_self (hAcpos x).ne'
  · intro x
    have h : ∀ p : P, β₂ ((p : G)⁻¹ * x) = c ((p : G)⁻¹ * x) / Bc x := by
      intro p
      have hp := hBcP p⁻¹ x
      rw [Subgroup.coe_inv] at hp
      simp only [β₂, hp]
    change ∫ p : P, β₂ ((p : G)⁻¹ * x) ∂ν = 1
    simp only [h]
    rw [integral_div]
    exact div_self (hBcpos x).ne'

omit [NonarchimedeanGroup G] in
/-- The identity of `G`, as a measurable equivalence onto its top subgroup. -/
def topMeasurableEquiv [MeasurableSpace G] : G ≃ᵐ (⊤ : Subgroup G) where
  toFun x := ⟨x, Subgroup.mem_top x⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_id.subtype_mk
  measurable_invFun := measurable_subtype_coe

/-- The measure on `⊤ : Subgroup G` with density `x ↦ max (β x) 0` against the Haar measure
of `G`, transported along `topMeasurableEquiv`. -/
noncomputable def bruhatMeasure [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (β : G → ℝ) : Measure (⊤ : Subgroup G) :=
  map topMeasurableEquiv ((haar : Measure G).withDensity fun x => (Real.toNNReal (β x) : ℝ≥0∞))

/-- For a nonnegative density, integrability against `bruhatMeasure β` is integrability of the
product with `β` against Haar measure. -/
theorem integrable_bruhatMeasure_iff [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (β : G → ℝ) (hβ : Measurable β) (hβ0 : 0 ≤ β) (ψ : G → ℂ) :
    Integrable (fun k : (⊤ : Subgroup G) => ψ k) (bruhatMeasure β) ↔
      Integrable (fun x => (β x : ℂ) * ψ x) (haar : Measure G) := by
  have hsmul : ∀ x : G, Real.toNNReal (β x) • ψ x = (β x : ℂ) * ψ x := fun x => by
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hβ0 x), Complex.real_smul]
  rw [bruhatMeasure, integrable_map_equiv,
    integrable_withDensity_iff_integrable_smul hβ.real_toNNReal]
  exact integrable_congr (ae_of_all _ hsmul)

/-- For a nonnegative density, integrals against `bruhatMeasure β` are Haar integrals
weighted by `β`. -/
theorem integral_bruhatMeasure [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (β : G → ℝ) (hβ : Measurable β) (hβ0 : 0 ≤ β) (ψ : G → ℂ) :
    ∫ k : (⊤ : Subgroup G), ψ k ∂(bruhatMeasure β) = ∫ x, (β x : ℂ) * ψ x ∂(haar : Measure G) := by
  have hsmul : ∀ x : G, Real.toNNReal (β x) • ψ x = (β x : ℂ) * ψ x := fun x => by
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hβ0 x), Complex.real_smul]
  rw [bruhatMeasure, integral_map_equiv,
    integral_withDensity_eq_integral_smul hβ.real_toNNReal]
  exact integral_congr_ae (ae_of_all _ hsmul)

/-- `bruhatMeasure β` is positive on every open neighbourhood of `1` when `β` is positive on
an open neighbourhood of `1`. -/
theorem bruhatMeasure_pos [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (β : G → ℝ) (hβ : Measurable β) (W : Set G) (hWo : IsOpen W) (hW1 : (1 : G) ∈ W)
    (hW : ∀ x ∈ W, 0 < β x) (U : Set (⊤ : Subgroup G)) (hU : IsOpen U)
    (h1 : (1 : (⊤ : Subgroup G)) ∈ U) : 0 < bruhatMeasure β U := by
  have he : Continuous (topMeasurableEquiv : G → (⊤ : Subgroup G)) :=
    continuous_id.subtype_mk fun x => Subgroup.mem_top x
  rw [bruhatMeasure, MeasurableEquiv.map_apply]
  have hWU : IsOpen (W ∩ topMeasurableEquiv ⁻¹' U) := hWo.inter (hU.preimage he)
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  rw [withDensity_apply_eq_zero' hβ.real_toNNReal.coe_nnreal_ennreal.aemeasurable] at h0
  have hsub : W ∩ topMeasurableEquiv ⁻¹' U ⊆
      {x | (Real.toNNReal (β x) : ℝ≥0∞) ≠ 0} ∩ topMeasurableEquiv ⁻¹' U := by
    rintro x ⟨hxW, hxU⟩
    exact ⟨ENNReal.coe_ne_zero.mpr (Real.toNNReal_pos.mpr (hW x hxW)).ne', hxU⟩
  exact (hWU.measure_pos (haar : Measure G) ⟨1, hW1, h1⟩).ne' (measure_mono_null hsub h0)

/-- For a closed subgroup `P` of a unimodular locally compact nonarchimedean group `G`
with `P \ G` compact, there is a measure on `⊤ : Subgroup G` which is positive on open
neighbourhoods of `1`. Integrating against it is invariant under right translation
on locally constant functions that are left covariant under `P` by Mathlib's modular
character of `P`. It is `bruhatMeasure β₂` for the Bruhat function `β₂` of
`exists_bruhat_functions`. -/
theorem exists_compactQuotient_measure [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (hG : ∀ g : G, Measure.modularCharacter g = 1) (P : Subgroup G)
    (hP : IsClosed (P : Set G)) [LocallyCompactSpace P] [CompactSpace (LeftQuotient P)] :
    ∃ μ : Measure (⊤ : Subgroup G),
      (∀ U : Set (⊤ : Subgroup G), IsOpen U → (1 : (⊤ : Subgroup G)) ∈ U → 0 < μ U) ∧
      ∀ φ : G → ℂ, IsLocallyConstant φ →
        (∀ (q : P) (x : G), φ ((q : G) * x) = ((Measure.modularCharacter q : ℝ) : ℂ) * φ x) →
        ∀ g : G, Integrable (fun k : (⊤ : Subgroup G) => φ ((k : G) * g)) μ ∧
          (∫ k : (⊤ : Subgroup G), φ ((k : G) * g) ∂μ) =
            ∫ k : (⊤ : Subgroup G), φ (k : G) ∂μ := by
  obtain ⟨β₁, β₂, W, hβ₁c, hβ₁s, hβ₂c, hβ₂s, hβ₂0, hWo, hW1, hW, hA, hB⟩ :=
    exists_bruhat_functions P hP
  refine ⟨bruhatMeasure β₂, bruhatMeasure_pos β₂ hβ₂c.measurable W hWo hW1 hW, ?_⟩
  intro φ hφ hcov g
  have key : ∀ g : G, ∫ x, (β₂ x : ℂ) * φ (x * g) ∂(haar : Measure G) =
      ∫ x, (β₁ x : ℂ) * φ x ∂(haar : Measure G) := by
    intro g
    have h1 := integral_mul_right_haar (fun x : G => (β₂ (x * g⁻¹) : ℂ) * φ x) g
    rw [hG g, NNReal.coe_one, one_smul] at h1
    simp only [mul_inv_cancel_right] at h1
    rw [h1]
    exact integral_bruhat_eq P hP haar haar (fun p => (modularCharacter p : ℝ))
      (continuous_modularCharacter_of_isClosed P hP) modularCharacter_inv_mul_self
      (fun x => β₂ (x * g⁻¹)) β₁ (hβ₂c.comp (continuous_id.mul continuous_const))
      (hβ₂s.comp_homeomorph (Homeomorph.mulRight g⁻¹)) hβ₁c hβ₁s hA
      (fun x => by simpa only [mul_assoc] using hB (x * g⁻¹)) φ hφ.continuous hcov
  refine ⟨(integrable_bruhatMeasure_iff β₂ hβ₂c.measurable hβ₂0 (fun y => φ (y * g))).mpr ?_, ?_⟩
  · exact ((Complex.continuous_ofReal.comp hβ₂c).mul
      (hφ.continuous.comp (continuous_id.mul continuous_const))).integrable_of_hasCompactSupport
      ((hβ₂s.comp_left Complex.ofReal_zero).mul_right)
  · calc ∫ k : (⊤ : Subgroup G), φ ((k : G) * g) ∂(bruhatMeasure β₂) =
          ∫ x, (β₂ x : ℂ) * φ (x * g) ∂(haar : Measure G) :=
          integral_bruhatMeasure β₂ hβ₂c.measurable hβ₂0 (fun y => φ (y * g))
      _ = ∫ x, (β₁ x : ℂ) * φ x ∂(haar : Measure G) := key g
      _ = ∫ x, (β₂ x : ℂ) * φ (x * 1) ∂(haar : Measure G) := (key 1).symm
      _ = ∫ x, (β₂ x : ℂ) * φ x ∂(haar : Measure G) := by simp only [mul_one]
      _ = ∫ k : (⊤ : Subgroup G), φ (k : G) ∂(bruhatMeasure β₂) :=
          (integral_bruhatMeasure β₂ hβ₂c.measurable hβ₂0 φ).symm

end Construction

end Langlands.Induction
