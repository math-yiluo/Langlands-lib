import Langlands.Representation.RankinSelberg.UnequalRankMirabolicMixedTransfer
import Langlands.AllField.Representation.Derivative.MirabolicMinusPairingTransferProof
import Langlands.AllField.Representation.Smooth.SmallRealizationProof
import Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement
/-!
# Mixed transfer through unnormalized `Φ⁻`

Let `ξ` be a smooth radical-generated representation of `P_(n+1)` and `η` a smooth
representation of `GL_(n+1)`. A nonzero bilinear form `β` with
`β(ξ(levi g) v, η(g) w) = |det g|^(-s) β(v, w)` is integrated against `θ_ψ⁻¹` along
the radical. The result descends to the unnormalized `Φ⁻ ξ` and is a nonzero form on
`Φ⁻ ξ` and `η|_(P_n)` with covariance `|det h|^(-(s - 1))`. The argument adapts the
published proof of `Derivative.Mirabolic.phiMinusPairingTransfer` to a second
representation of `GL_(n+1)`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.UnequalRankMixedTransfer
open Langlands.RankinSelberg.UnequalRankMixedTransfer hiding exists_coefficient_support_mixed exists_open_subgroup_coefficient_mixed mixedTransfer
open Langlands.AllField.RankinSelberg.UnequalRankMixedTransfer
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Topology MeasureTheory
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Derivative.Mirabolic hiding PhiMinusPairingTransferStatement character_dotProduct_eq_one character_mul_eq_one coe_latticeBox exists_coefficient_support exists_integral_character_ne_zero exists_latticeBox_fixes exists_latticeBox_subset exists_mulVec_eq_add exists_ne_zero_mem_additiveLattice exists_open_subgroup_coefficient finite_latticeBox_quotient inv_mem_additiveLattice_of_notMem isCompact_latticeBox isOpen_latticeBox latticeBox latticeBox_mono mem_latticeBox mem_latticeBox_of_forall_character_eq_one phiMinusPairingTransfer phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinusUnnormalized_action
open Langlands.AllField.Derivative.Mirabolic
open scoped Matrix NNReal

universe uF uV uW

section Levi

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {m : ℕ}
variable [MeasurableSpace (Fin (m + 1) → K)] [BorelSpace (Fin (m + 1) → K)]
variable (μ : Measure (Fin (m + 1) → K))
variable (ψ : UnitaryAdditiveCharacter K)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ξ : Representation ℂ (mirabolic (m + 1) K) V)
  (η : Representation ℂ (Langlands.GeneralLinear (m + 1) K) W) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)

end Levi

section Support

variable {F : Type uF} [Field F] (T : LocalFieldData F) {m : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ξ : Representation ℂ (mirabolic (m + 1) F) V)
  (η : Representation ℂ (Langlands.GeneralLinear (m + 1) F) W)
  (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (s : ℂ)

/-- An open subgroup of `GL_(m+1)` under which the radical coefficient of `x` and `w`
is invariant. -/
theorem exists_open_subgroup_coefficient_mixed
    (hβ : ∀ (g : Langlands.GeneralLinear (m + 1) F) (v : V) (w : W),
      β (ξ (levi g) v) (η g w) =
        determinantWeight (normalizedAbsoluteValue T) g (-s) * β v w) :
    letI := T.topology
    IsSmooth ξ → IsSmooth η → ∀ (x : V) (w : W),
      ∃ H : Subgroup (Langlands.GeneralLinear (m + 1) F),
        IsOpen (H : Set (Langlands.GeneralLinear (m + 1) F)) ∧
        ∀ k ∈ H, ∀ c : Fin (m + 1) → F,
          β (ξ (radicalElement (k.val *ᵥ c) : mirabolic (m + 1) F) x) w =
            β (ξ (radicalElement c : mirabolic (m + 1) F) x) w := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F := T.fieldT2
  intro hs hs' x w
  obtain ⟨K₁, hK₁⟩ := hs x
  obtain ⟨K₂, hK₂⟩ := hs' w
  have hfix₁ : ∀ k ∈ K₁, ξ k x = x := fun k hk =>
    (Representation.mem_invariants _ x).mp hK₁ ⟨k, hk⟩
  have hfix₂ : ∀ k ∈ K₂, η k w = w := fun k hk =>
    (Representation.mem_invariants _ w).mp hK₂ ⟨k, hk⟩
  have hdet : IsOpen {g : Langlands.GeneralLinear (m + 1) F |
      normalizedAbsoluteValue T (Matrix.det g.val) = 1} := by
    have e : {g : Langlands.GeneralLinear (m + 1) F |
        normalizedAbsoluteValue T (Matrix.det g.val) = 1} =
        ((T.determinantNorm (m + 1)).ker :
          Set (Langlands.GeneralLinear (m + 1) F)) := by
      ext g
      rw [Set.mem_ofPred_eq, SetLike.mem_coe, MonoidHom.mem_ker, ← Units.val_eq_one,
        ← NNReal.coe_eq_one, T.determinantNorm_coe]
      rfl
    rw [e]
    exact T.isOpen_ker_determinantNorm (m + 1)
  refine ⟨K₁.toSubgroup.comap levi ⊓ K₂.toSubgroup ⊓
      EqualRankFrobenius.detOne (normalizedAbsoluteValue T), ?_, ?_⟩
  · exact ((K₁.isOpen.preimage continuous_levi).inter K₂.isOpen).inter hdet
  · rintro k ⟨⟨hk₁, hk₂⟩, hkdet⟩ c
    have hkdet' : normalizedAbsoluteValue T (Matrix.det k.val) = 1 := hkdet
    calc β (ξ (radicalElement (k.val *ᵥ c) : mirabolic (m + 1) F) x) w =
          β (ξ (radicalElement (k.val *ᵥ c) : mirabolic (m + 1) F) (ξ (levi k) x))
            (η k w) := by
          rw [hfix₁ _ hk₁, hfix₂ _ hk₂]
      _ = β (ξ (levi k) (ξ (radicalElement c : mirabolic (m + 1) F) x)) (η k w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← levi_mul_radicalElement, map_mul,
            Module.End.mul_apply]
      _ = _ := by
          rw [hβ, EqualRankFrobenius.determinantWeight_eq_one _ hkdet', one_mul]

/-- Radical coefficients of a radical-generated representation have compact support. -/
theorem exists_coefficient_support_mixed
    (hβ : ∀ (g : Langlands.GeneralLinear (m + 1) F) (v : V) (w : W),
      β (ξ (levi g) v) (η g w) =
        determinantWeight (normalizedAbsoluteValue T) g (-s) * β v w) :
    letI := T.topology
    IsSmooth ξ → IsSmooth η → Whittaker.MirabolicRigidity.IsRadicalGenerated ξ →
      ∀ (v : V) (w : W), ∃ N : ℤ, ∀ c ∉ latticeBox T (m + 1) N,
        β (ξ (radicalElement c : mirabolic (m + 1) F) v) w = 0 := by
  let := T.topology
  intro hs hs' hgen v w
  let S : Submodule ℂ V :=
    { carrier := {v | ∃ N : ℤ, ∀ c ∉ latticeBox T (m + 1) N,
        β (ξ (radicalElement c : mirabolic (m + 1) F) v) w = 0}
      add_mem' := by
        rintro a b ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
        refine ⟨max N₁ N₂, fun c hc => ?_⟩
        have hc₁ : c ∉ latticeBox T (m + 1) N₁ :=
          fun h => hc (latticeBox_mono T (le_max_left _ _) h)
        have hc₂ : c ∉ latticeBox T (m + 1) N₂ :=
          fun h => hc (latticeBox_mono T (le_max_right _ _) h)
        rw [map_add, map_add, LinearMap.add_apply, h₁ c hc₁, h₂ c hc₂, add_zero]
      zero_mem' := ⟨0, fun c _ => by rw [map_zero, map_zero, LinearMap.zero_apply]⟩
      smul_mem' := by
        rintro a b ⟨N, h⟩
        exact ⟨N, fun c hc => by
          rw [map_smul, map_smul, LinearMap.smul_apply, h c hc, smul_zero]⟩ }
  have hle : Submodule.span ℂ (Set.range fun p : Mirabolic.radical (m + 1) F × V =>
      ξ (p.1 : mirabolic (m + 1) F) p.2 - p.2) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨u, x⟩, rfl⟩
    obtain ⟨d, rfl⟩ : ∃ d, radicalElement d = u := ⟨_, radicalElement_coordinates u⟩
    obtain ⟨H, hHo, hH⟩ := exists_open_subgroup_coefficient_mixed T ξ η β s hβ hs hs' x w
    obtain ⟨N, hN⟩ := exists_mulVec_eq_add T (H : Set (Langlands.GeneralLinear (m + 1) F))
      hHo H.one_mem d
    refine ⟨N, fun c hc => ?_⟩
    obtain ⟨h, hh, hhc⟩ := hN c hc
    change β (ξ (radicalElement c : mirabolic (m + 1) F)
      (ξ (radicalElement d : mirabolic (m + 1) F) x - x)) w = 0
    rw [map_sub, rep_radicalElement_mul, map_sub, LinearMap.sub_apply, ← hhc, hH h hh c,
      sub_self]
  have hS : S = ⊤ := top_le_iff.mp (hgen ▸ hle)
  have hv : v ∈ S := by
    rw [hS]
    exact Submodule.mem_top
  exact hv

end Support

/-- Mixed transfer: a nonzero form between a smooth radical-generated representation `ξ`
of `P_(n+1)` and a smooth representation `η` of `GL_(n+1)`, covariant under the Levi
`GL_(n+1)` with weight `|det g|^(-s)`, gives a nonzero form between the unnormalized
`Φ⁻ ξ` and `η|_(P_n)` with weight `|det h|^(-(s - 1))`. -/
theorem mixedTransfer (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ξ : Representation ℂ (mirabolic (n + 1) F) V)
      (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
      (hs : IsSmooth ξ), IsSmooth η → Whittaker.MirabolicRigidity.IsRadicalGenerated ξ →
      ∀ (s : ℂ) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ),
        (∀ (g : Langlands.GeneralLinear (n + 1) F) (v : V) (w : W),
          β (ξ (levi g) v) (η g w) =
            determinantWeight (normalizedAbsoluteValue T) g (-s) * β v w) →
        β ≠ 0 →
        ∃ β' : InvariantBilinear.forms
            ((phiMinusUnnormalized T ψ n).obj (SmoothRep.of ξ hs)).representation
            (η.comp (mirabolic n F).subtype)
            (fun h => determinantWeight (normalizedAbsoluteValue T) h.val (-(s - 1))),
          β' ≠ 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F := T.fieldT2
  have : SecondCountableTopology F := T.secondCountableTopology
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  intro ψ V _ _ W _ _ ξ η hs hsη hgen s β hβ hβ0
  let abv := normalizedAbsoluteValue T
  let μ : Measure (Fin (n + 1) → F) := Measure.addHaar
  -- Haar scaling on the radical coordinates.
  have hχ (a : F) (ha : a ≠ 0) :
      (Measure.addHaar : Measure F).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • Measure.addHaar :=
    Langlands.AllField.HarmonicAnalysis.padicScalarHaarScaling F T Measure.addHaar (Units.mk0 a ha)
  have hscale : ∀ k : Langlands.GeneralLinear (n + 1) F,
      μ.map (fun x => k.val *ᵥ x) = (T.normalizedAbsHom (Matrix.det k.val))⁻¹ • μ := by
    intro k
    have h := HarmonicAnalysis.haarMeasure_map_matrix (Measure.addHaar : Measure F)
      T.normalizedAbsHom hχ μ (EqualRankFrobenius.det_ne_zero k)
    have e : (fun x => k.val *ᵥ x) = ⇑(Matrix.toLin' k.val) := by
      funext x
      rw [Matrix.toLin'_apply]
    rw [e, h]
  have habv : ∀ a, (T.normalizedAbsHom a : ℝ) = abv a := fun _ => rfl
  -- Local constancy, continuity and compact support of the radical coefficients.
  have hloc : ∀ v : V, ∃ l : ℤ, ∀ (c d : Fin (n + 1) → F),
      d ∈ latticeBox T (n + 1) l → ∀ w : W,
        β (ξ (radicalElement (c + d) : mirabolic (n + 1) F) v) w =
          β (ξ (radicalElement c : mirabolic (n + 1) F) v) w := by
    intro v
    obtain ⟨l, hl⟩ := exists_latticeBox_fixes T ξ hs v
    exact ⟨l, fun c d hd w => by rw [← rep_radicalElement_mul, hl d hd]⟩
  have hsupp : ∀ (v : V) (w : W), ∃ N : ℤ, ∀ c ∉ latticeBox T (n + 1) N,
      β (ξ (radicalElement c : mirabolic (n + 1) F) v) w = 0 :=
    exists_coefficient_support_mixed T ξ η β s hβ hs hsη hgen
  have hcont : ∀ v w, Continuous fun c : Fin (n + 1) → F =>
      β (ξ (radicalElement c : mirabolic (n + 1) F) v) w := by
    intro v w
    obtain ⟨l, hl⟩ := hloc v
    exact continuous_of_forall_add_eq ((isOpen_latticeBox T (n + 1) l).mem_nhds (zero_mem _))
      fun c d hd => hl c d hd w
  have hcpt : ∀ v w, HasCompactSupport fun c : Fin (n + 1) → F =>
      β (ξ (radicalElement c : mirabolic (n + 1) F) v) w := by
    intro v w
    obtain ⟨N, hN⟩ := hsupp v w
    exact HasCompactSupport.intro (isCompact_latticeBox T (n + 1) N) hN
  -- The transferred form before descent.
  let B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ := transferForm μ ψ ξ β hcont hcpt
  have hB : ∀ v w, B v w = transferIntegral μ ψ ξ β v w := fun _ _ => rfl
  have hBl : ∀ (d : Fin (n + 1) → F) v w,
      B (ξ (radicalElement d : mirabolic (n + 1) F) v) w =
        ψ.complex (d (Fin.last n)) * B v w := by
    intro d v w
    rw [hB, hB, transferIntegral_radical_left]
  -- Descent to the coinvariants in the first variable.
  let Θ := T.mirabolicTheta ψ n
  have hΘ : ∀ u : Mirabolic.radical (n + 1) F,
      ∃ d : Fin (n + 1) → F, radicalElement d = u ∧
        (Θ u : ℂ) = ψ.complex (d (Fin.last n)) := by
    intro u
    refine ⟨radicalCoordinates u, radicalElement_coordinates u, ?_⟩
    rw [← theta_radicalElement ψ n (radicalCoordinates u), radicalElement_coordinates u]
    rfl
  let B₄ := Jacquet.Localization.lift ξ (Mirabolic.radical (n + 1) F) Θ B
    (fun u v => by
      obtain ⟨d, rfl, hd⟩ := hΘ u
      ext w
      rw [LinearMap.smul_apply, hd, smul_eq_mul]
      exact hBl d v w)
  have hB₄ : ∀ v w, B₄ (Jacquet.Localization.mk ξ _ Θ v) w = B v w := fun _ _ => rfl
  refine ⟨⟨B₄, ?_⟩, ?_⟩
  · -- Covariance under the smaller mirabolic group.
    intro h a w
    obtain ⟨v, rfl⟩ := phiMinusQuotient_surjective T ψ n (SmoothRep.of ξ hs) a
    change B (ξ (successor h) v) (η h.val w) =
      determinantWeight abv h.val (-(s - 1)) * B v w
    rw [hB, hB, show successor h = levi (h : Langlands.GeneralLinear (n + 1) F) from
      rfl, transferIntegral_levi_mixed μ ψ ξ η β abv T.normalizedAbsHom habv hscale s hβ hcont]
    simp only [mulVec_last]
    rw [neg_sub, EqualRankFrobenius.determinantWeight_one_sub]
    unfold transferIntegral
    ring
  · -- Nonvanishing.
    intro h0
    obtain ⟨v₀, w₀, hvw⟩ : ∃ v w, β v w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hβ0 (LinearMap.ext₂ hall)
    obtain ⟨l, hl⟩ := hloc v₀
    obtain ⟨N, hN⟩ := hsupp v₀ w₀
    obtain ⟨y, hy0, hy⟩ := exists_integral_character_ne_zero T ψ μ
      (fun c => β (ξ (radicalElement c : mirabolic (n + 1) F) v₀) w₀) l N
      (fun c d hd => hl c d hd w₀) hN (by simpa [rep_radicalElement_zero] using hvw)
    obtain ⟨g, rfl⟩ := EqualRankFrobenius.exists_lastRow_eq y hy0
    have hval : B (ξ (levi g) v₀) (η g w₀) =
        determinantWeight abv g (-s) * (abv (Matrix.det g.val) : ℂ) *
          ∫ c, ψ.complex (-(lastRow g ⬝ᵥ c)) *
            β (ξ (radicalElement c : mirabolic (n + 1) F) v₀) w₀ ∂μ := by
      rw [hB, transferIntegral_levi_mixed μ ψ ξ η β abv T.normalizedAbsHom habv hscale s hβ
        hcont]
      rfl
    have hne : B (ξ (levi g) v₀) (η g w₀) ≠ 0 := by
      rw [hval]
      refine mul_ne_zero (mul_ne_zero ?_ ?_) hy
      · rw [determinantWeight, Complex.cpow_ne_zero_iff]
        exact Or.inl (Complex.ofReal_ne_zero.mpr (EqualRankFrobenius.abv_det_ne_zero abv g))
      · exact Complex.ofReal_ne_zero.mpr (EqualRankFrobenius.abv_det_ne_zero abv g)
    apply hne
    rw [← hB₄]
    have h0' := congrArg Subtype.val h0
    change B₄ = 0 at h0'
    rw [h0']
    rfl

end Langlands.AllField.RankinSelberg.UnequalRankMixedTransfer
