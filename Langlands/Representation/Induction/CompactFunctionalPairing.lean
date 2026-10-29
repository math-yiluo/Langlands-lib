import Langlands.Representation.Induction.CompactFormsFunctional

/-!
# A nonzero pairing from an inverse-character functional

The pointwise product of a compactly induced function and a smooth coefficient
has compact support modulo the inducing subgroup. Its quotient integral gives
an invariant bilinear form, nonzero whenever the coefficient functional is.
-/

noncomputable section

namespace Langlands.Induction.CompactFunctionalPairing

open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal

universe uG uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (H : Subgroup G) (θ θ' : H →* ℂˣ)
variable (π : Representation ℂ G W) (hπ : IsSmooth π)
variable (ℓ : Whittaker.functionals H θ' π)
variable (hθ' : ∀ h : H, (θ' h : ℂ) * θ h = 1)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem characterRepresentation_apply (h : H) (z : ℂ) :
    characterRepresentation θ h z = (θ h : ℂ) * z := rfl

private theorem section_ext {σ : Representation ℂ H ℂ} {f f' : CompactFunctions H σ}
    (h : ∀ x, eval H σ f.1 x = eval H σ f'.1 x) : f = f' :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

private theorem exists_eval_mul (f : CompactFunctions H (characterRepresentation θ)) :
    ∃ K : OpenSubgroup G, ∀ k ∈ K, ∀ x : G,
      eval H _ f.1 (x * k) = eval H _ f.1 x := by
  obtain ⟨K, hK⟩ := compactInduced_smooth H (characterRepresentation θ) f
  exact ⟨K, fun k hk x =>
    congrArg (fun f : CompactFunctions H (characterRepresentation θ) => eval H _ f.1 x)
      (hK ⟨k, hk⟩)⟩

private def productSmooth (f : CompactFunctions H (characterRepresentation θ)) (w : W) :
    SmoothFunctions H (Representation.trivial ℂ H ℂ) :=
  smoothFunctionOf H _
    (fun x => eval H _ f.1 x * ℓ.val (π x w))
    (fun h x => by
      rw [eval_covariant, characterRepresentation_apply, map_mul, Module.End.mul_apply,
        ℓ.property, Representation.trivial_apply]
      linear_combination (eval H _ f.1 x * ℓ.val (π x w)) * hθ' h)
    ((exists_eval_mul H θ f).choose ⊓ (hπ w).choose)
    (fun k x => by
      have hk := OpenSubgroup.mem_inf.mp k.property
      have hkw : π (k : G) w = w := (hπ w).choose_spec ⟨k, hk.2⟩
      rw [(exists_eval_mul H θ f).choose_spec (k : G) hk.1 x,
        map_mul, Module.End.mul_apply, hkw])

private def product (f : CompactFunctions H (characterRepresentation θ)) (w : W) :
    CompactFunctions H (Representation.trivial ℂ H ℂ) :=
  ⟨productSmooth H θ θ' π hπ ℓ hθ' f w, by
    refine IsCompact.of_isClosed_subset f.2 (isClosed_quotientSupport H _ _) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, left_ne_zero_of_mul hx, rfl⟩⟩

private theorem eval_product (f : CompactFunctions H (characterRepresentation θ)) (w : W)
    (x : G) :
    eval H _ (product H θ θ' π hπ ℓ hθ' f w).1 x =
      eval H _ f.1 x * ℓ.val (π x w) := rfl

private def coinvariantValue :
    Representation.Coinvariants (Representation.trivial ℂ H ℂ) →ₗ[ℂ] ℂ :=
  Representation.Coinvariants.lift _ LinearMap.id fun _ => LinearMap.ext fun _ => rfl

variable [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
variable [BorelSpace (QuotientIntegration.LeftQuotient H)]
variable (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]

/-- Integrate `f(x) * ℓ(π(x)w)` over the actual left quotient `H \ G`. -/
def pairing : CompactFunctions H (characterRepresentation θ) →ₗ[ℂ] W →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun f w => coinvariantValue H
      (compactCoinvariantIntegral H (Representation.trivial ℂ H ℂ) ν
        (product H θ θ' π hπ ℓ hθ' f w)))
    (fun f f' w => by
      have he : product H θ θ' π hπ ℓ hθ' (f + f') w =
          product H θ θ' π hπ ℓ hθ' f w + product H θ θ' π hπ ℓ hθ' f' w :=
        section_ext H fun x => by
          change (eval H _ f.1 x + eval H _ f'.1 x) * ℓ.val (π x w) =
            eval H _ f.1 x * ℓ.val (π x w) + eval H _ f'.1 x * ℓ.val (π x w)
          exact add_mul _ _ _
      rw [he, map_add, map_add])
    (fun a f w => by
      have he : product H θ θ' π hπ ℓ hθ' (a • f) w =
          a • product H θ θ' π hπ ℓ hθ' f w :=
        section_ext H fun x => by
          change (a * eval H _ f.1 x) * ℓ.val (π x w) = a * (eval H _ f.1 x * ℓ.val (π x w))
          exact mul_assoc _ _ _
      rw [he, map_smul, map_smul, smul_eq_mul])
    (fun f w w' => by
      have he : product H θ θ' π hπ ℓ hθ' f (w + w') =
          product H θ θ' π hπ ℓ hθ' f w + product H θ θ' π hπ ℓ hθ' f w' :=
        section_ext H fun x => by
          change eval H _ f.1 x * ℓ.val (π x (w + w')) =
            eval H _ f.1 x * ℓ.val (π x w) + eval H _ f.1 x * ℓ.val (π x w')
          rw [map_add, map_add, mul_add]
      rw [he, map_add, map_add])
    (fun a f w => by
      have he : product H θ θ' π hπ ℓ hθ' f (a • w) =
          a • product H θ θ' π hπ ℓ hθ' f w :=
        section_ext H fun x => by
          change eval H _ f.1 x * ℓ.val (π x (a • w)) = a * (eval H _ f.1 x * ℓ.val (π x w))
          rw [map_smul, map_smul, smul_eq_mul, mul_left_comm]
      rw [he, map_smul, map_smul, smul_eq_mul])

/-- The integrated form is invariant under the simultaneous right action of `G`. -/
theorem pairing_mem
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν) :
    pairing H θ θ' π hπ ℓ hθ' ν ∈
      InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
        (fun _ => (1 : ℂ)) := by
  intro g f w
  have he : product H θ θ' π hπ ℓ hθ'
      (compactInduced H (characterRepresentation θ) g f) (π g w) =
      compactInduced H (Representation.trivial ℂ H ℂ) g
        (product H θ θ' π hπ ℓ hθ' f w) := by
    apply section_ext H
    intro x
    change eval H _ f.1 (x * g) * ℓ.val (π x (π g w)) =
      eval H _ f.1 (x * g) * ℓ.val (π (x * g) w)
    rw [map_mul, Module.End.mul_apply]
  change coinvariantValue H (compactCoinvariantIntegral H _ ν _) =
    1 * coinvariantValue H (compactCoinvariantIntegral H _ ν _)
  rw [he, compactCoinvariantIntegral_translate H _ ν hinv, one_mul]

omit [IsTopologicalGroup G] [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
  [BorelSpace (QuotientIntegration.LeftQuotient H)] in
private theorem mem_orbit_iff (K : OpenSubgroup G) (y : G) :
    quotientMap H y ∈ QuotientIntegration.compactOpenQuotientOrbit H K ↔
      ∃ (h : H) (k : K), y = (h : G) * (k : G) := by
  constructor
  · rintro ⟨k, hk, he⟩
    have hy : y * k⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
    exact ⟨⟨y * k⁻¹, hy⟩, ⟨k, hk⟩, by simp⟩
  · rintro ⟨h, k, rfl⟩
    refine ⟨k, k.property, Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)⟩
    simp [mul_assoc]

omit [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
  [BorelSpace (QuotientIntegration.LeftQuotient H)] in
private theorem section_apply_mul (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
      (conjOpenSubgroup H K 1).toSubgroup) (h : H) (k : K) :
    eval H _ (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv).1
      ((h : G) * (k : G)) = (θ h : ℂ) := by
  simpa [characterRepresentation_apply] using
    compactDoubleCosetSection_apply H (characterRepresentation θ) K hK 1 1 hv h k

omit [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
  [BorelSpace (QuotientIntegration.LeftQuotient H)] in
private theorem section_apply_of_not_mem (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
      (conjOpenSubgroup H K 1).toSubgroup) {y : G}
    (hy : quotientMap H y ∉ QuotientIntegration.compactOpenQuotientOrbit H K) :
    eval H _ (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv).1 y = 0 := by
  by_contra hne
  obtain ⟨k, hk, he⟩ :=
    compactDoubleCosetSection_support_subset H (characterRepresentation θ) K hK 1 1 hv
      ⟨y, hne, rfl⟩
  exact hy ⟨k, hk, by simpa only [one_mul] using he⟩

/-- A unit section paired with a `K`-fixed vector has the expected orbit-mass value. -/
theorem pairing_section (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hv : (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
      (conjOpenSubgroup H K 1).toSubgroup)
    (w : W) (hw : ∀ k ∈ K, π k w = w) :
    pairing H θ θ' π hπ ℓ hθ' ν
        (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv) w =
      ((ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal : ℂ) * ℓ.val w := by
  have hm := (QuotientIntegration.isOpen_compactOpenQuotientOrbit H K).measurableSet
  have he : quotientCoinvariantSimple H (Representation.trivial ℂ H ℂ)
      (product H θ θ' π hπ ℓ hθ'
        (compactDoubleCosetSection H (characterRepresentation θ) K hK 1 1 hv) w) =
      (SimpleFunc.const _ (Representation.Coinvariants.mk (Representation.trivial ℂ H ℂ)
        (ℓ.val w))).restrict (QuotientIntegration.compactOpenQuotientOrbit H K) := by
    ext q
    induction q using Quotient.inductionOn with
    | h y =>
      rw [SimpleFunc.restrict_apply _ hm, quotientCoinvariantSimple_apply]
      change Representation.Coinvariants.mk _ (eval H _ _ y * ℓ.val (π y w)) =
        (QuotientIntegration.compactOpenQuotientOrbit H K).indicator _ (quotientMap H y)
      by_cases hy : quotientMap H y ∈ QuotientIntegration.compactOpenQuotientOrbit H K
      · rw [Set.indicator_of_mem hy, SimpleFunc.const_apply]
        obtain ⟨h, k, rfl⟩ := (mem_orbit_iff H K y).mp hy
        have hcoeff : ℓ.val (π ((h : G) * (k : G)) w) = (θ' h : ℂ) * ℓ.val w := by
          rw [map_mul π, Module.End.mul_apply, hw k k.property]
          exact ℓ.property h w
        rw [section_apply_mul, hcoeff]
        congr 1
        linear_combination (ℓ.val w) * hθ' h
      · rw [Set.indicator_of_notMem hy, section_apply_of_not_mem H θ K hK hv hy,
          zero_mul, map_zero]
  change coinvariantValue H (compactCoinvariantIntegral H _ ν _) = _
  rw [compactCoinvariantIntegral_apply, he,
    HarmonicAnalysis.AlgebraicIntegral.integral_indicator_const _ hm, map_smul,
    coinvariantValue, Representation.Coinvariants.lift_mk, LinearMap.id_apply, smul_eq_mul]

omit [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
  [BorelSpace (QuotientIntegration.LeftQuotient H)] [IsFiniteMeasureOnCompacts ν] in
include hπ in
private theorem exists_admissible
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth (characterRepresentation θ)) (w : W) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      (1 : ℂ) ∈ fixedVectors (characterRepresentation θ)
        (conjOpenSubgroup H K 1).toSubgroup ∧ ∀ k ∈ K, π k w = w := by
  obtain ⟨L, hL⟩ := hσ 1
  obtain ⟨O, hO, he⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp L.isOpen
  have h1 : (1 : G) ∈ O := by
    have h1L : (1 : H) ∈ (L : Set H) := L.one_mem
    rw [← he] at h1L
    exact h1L
  obtain ⟨K₁, hK₁, hKO⟩ := hG O hO h1
  obtain ⟨M, hM⟩ := hπ w
  refine ⟨K₁ ⊓ M, ?_, fun p => ?_, fun k hk => hM ⟨k, (OpenSubgroup.mem_inf.mp hk).2⟩⟩
  · rw [OpenSubgroup.coe_inf]
    exact hK₁.inter_right M.isClosed
  · have hpKM : ((p : H) : G) ∈ K₁ ⊓ M := by
      simpa using mem_conjOpenSubgroup.mp p.property
    have hpL : (p : H) ∈ (L : Set H) := by
      rw [← he]
      exact hKO (OpenSubgroup.mem_inf.mp hpKM).1
    exact hL ⟨p, hpL⟩

include hπ hθ' in
/-- A nonzero inverse-character functional on any smooth representation gives a
nonzero invariant form against compact induction of the original character. -/
theorem exists_nonzero_form
    (hG : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hσ : IsSmooth (characterRepresentation θ))
    (hinv : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)
    (hmass : ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
      0 < ν (QuotientIntegration.compactOpenQuotientOrbit H J) ∧
        ν (QuotientIntegration.compactOpenQuotientOrbit H J) < ⊤)
    (hℓ : ℓ.val ≠ 0) :
    ∃ B ∈ InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π
        (fun _ => (1 : ℂ)), B ≠ 0 := by
  classical
  obtain ⟨w, hw⟩ : ∃ w, ℓ.val w ≠ 0 := by
    by_contra! h
    exact hℓ (LinearMap.ext h)
  obtain ⟨K, hK, hv, hwK⟩ := exists_admissible H θ π hπ hG hσ w
  refine ⟨pairing H θ θ' π hπ ℓ hθ' ν, pairing_mem H θ θ' π hπ ℓ hθ' ν hinv,
    fun h0 => ?_⟩
  have hs := pairing_section H θ θ' π hπ ℓ hθ' ν K hK hv w hwK
  rw [h0, LinearMap.zero_apply, LinearMap.zero_apply] at hs
  obtain ⟨hpos, hfin⟩ := hmass K hK
  have hne : ((ν (QuotientIntegration.compactOpenQuotientOrbit H K)).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  exact (mul_ne_zero hne hw) hs.symm

end Langlands.Induction.CompactFunctionalPairing
