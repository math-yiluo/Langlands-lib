import Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof
import Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.AllField.Representation.Derivative.MirabolicLatticeBox
import Langlands.AllField.Representation.Derivative.MirabolicMinusPairingTransferStatement
/-!
# Proof of the pairing transfer through unnormalized `Φ⁻`

A covariant pairing `β` of `ξ` and `ξ'` is integrated against `θ_ψ⁻¹` along the radical:
`β̃(v, w) = ∫ ψ(-c_last) β(ξ(u c) v, ξ'(ε) w) dc`, with `ε = levi (-1)`. The integrand is
locally constant and compactly supported, `β̃` descends to the `θ_ψ`-coinvariants, and a
Haar change of variables gives covariance `|det|^(1 - s)` on the smaller mirabolic group.
A finite character sum shows that some Levi translate of `β̃` is nonzero. See the paired
Markdown for the route.
-/

noncomputable section

namespace Langlands.AllField.Derivative.Mirabolic
open Langlands.Derivative.Mirabolic hiding PhiMinusPairingTransferStatement character_dotProduct_eq_one character_mul_eq_one coe_latticeBox exists_coefficient_support exists_integral_character_ne_zero exists_latticeBox_fixes exists_latticeBox_subset exists_mulVec_eq_add exists_ne_zero_mem_additiveLattice exists_open_subgroup_coefficient finite_latticeBox_quotient inv_mem_additiveLattice_of_notMem isCompact_latticeBox isOpen_latticeBox latticeBox latticeBox_mono mem_latticeBox mem_latticeBox_of_forall_character_eq_one phiMinusPairingTransfer phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinusUnnormalized_action
open Langlands.AllField.Derivative.Mirabolic
open Langlands.Derivative
open Langlands.AllField.Derivative

open Topology MeasureTheory
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open scoped Matrix NNReal

universe uF uV uW

/-! ### A finite character-sum argument on the radical coordinates -/

section Fourier

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- A locally constant, compactly supported function `f` on `F^(k+1)` with `f 0 ≠ 0` has
a nonzero twisted integral `∫ ψ(-(y ⬝ c)) f(c) dc` at some `y ≠ 0`. -/
theorem exists_integral_character_ne_zero {k : ℕ} :
    letI := T.topology
    letI : MeasurableSpace F := borel F
    ∀ (ψ : UnitaryAdditiveCharacter F) (μ : Measure (Fin (k + 1) → F))
      [μ.IsAddHaarMeasure] (f : (Fin (k + 1) → F) → ℂ) (l N : ℤ),
      (∀ c, ∀ d ∈ latticeBox T (k + 1) l, f (c + d) = f c) →
      (∀ c ∉ latticeBox T (k + 1) N, f c = 0) → f 0 ≠ 0 →
      ∃ y : Fin (k + 1) → F, y ≠ 0 ∧
        ∫ c, ψ.complex (-(y ⬝ᵥ c)) * f c ∂μ ≠ 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F := T.fieldT2
  have : SecondCountableTopology F := T.secondCountableTopology
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  intro ψ μ _ f l N hper hsupp h0
  have hcont : Continuous f :=
    continuous_of_forall_add_eq ((isOpen_latticeBox T (k + 1) l).mem_nhds (zero_mem _))
      fun c d hd => hper c d hd
  have hint : ∀ y : Fin (k + 1) → F,
      Integrable (fun c => ψ.complex (-(y ⬝ᵥ c)) * f c) μ := by
    intro y
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (ψ.continuous_complex.comp (continuous_const.dotProduct continuous_id).neg).mul hcont
    · refine HasCompactSupport.intro (isCompact_latticeBox T (k + 1) N) fun c hc => ?_
      rw [hsupp c hc, mul_zero]
  by_contra hcon
  push Not at hcon
  -- The levels of the boxes.
  let n := T.additiveConductor ψ
  let B : ℤ := n - N
  let A : ℤ := max B (n - l)
  let C : ℤ := n - A
  have hCl : C ≤ l := by omega
  -- The twisted integral is constant on the `B`-box.
  have hconst : ∀ y ∈ latticeBox T (k + 1) B,
      ∫ c, ψ.complex (-(y ⬝ᵥ c)) * f c ∂μ = ∫ c, f c ∂μ := by
    intro y hy
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    by_cases hc : c ∈ latticeBox T (k + 1) N
    · have h1 : ψ ((-y) ⬝ᵥ c) = 1 := character_dotProduct_eq_one T ψ (neg_mem hy) hc
      simp only [← neg_dotProduct, UnitaryAdditiveCharacter.complex_apply, h1, Circle.coe_one,
        one_mul]
    · simp only [hsupp c hc, mul_zero]
  have hzero : ∀ y : Fin (k + 1) → F, ∫ c, ψ.complex (-(y ⬝ᵥ c)) * f c ∂μ = 0 := by
    have hmass : ∫ c, f c ∂μ = 0 := by
      obtain ⟨t, ht0, ht⟩ := exists_ne_zero_mem_additiveLattice T B
      have hy : (Pi.single 0 t : Fin (k + 1) → F) ∈ latticeBox T (k + 1) B := by
        rw [mem_latticeBox]
        intro i
        by_cases hi : i = 0
        · subst hi
          simpa using ht
        · simp [hi]
      rw [← hconst _ hy]
      apply hcon
      intro h
      apply ht0
      simpa using congrFun h 0
    intro y
    by_cases hy : y = 0
    · rw [hy, hconst 0 (zero_mem _), hmass]
    · exact hcon y hy
  -- The finite quotient of the `A`-box by the `B`-box.
  let BA := latticeBox T (k + 1) A
  let L := (latticeBox T (k + 1) B).addSubgroupOf BA
  have : Finite (BA ⧸ L) := finite_latticeBox_quotient T (k + 1) A B
  let : Fintype (BA ⧸ L) := Fintype.ofFinite _
  have hpoint : ∀ c : Fin (k + 1) → F,
      ∑ q : BA ⧸ L, ψ.complex (-(((q.out : BA) : Fin (k + 1) → F) ⬝ᵥ c)) * f c =
        (latticeBox T (k + 1) C : Set (Fin (k + 1) → F)).indicator
          (fun _ => (Fintype.card (BA ⧸ L) : ℂ) * f 0) c := by
    intro c
    by_cases hc : c ∈ latticeBox T (k + 1) C
    · rw [Set.indicator_of_mem (show c ∈ (latticeBox T (k + 1) C : Set _) from hc)]
      have hfc : f c = f 0 := by
        have h := hper 0 c (latticeBox_mono T hCl hc)
        rwa [zero_add] at h
      have hterm : ∀ q : BA ⧸ L,
          ψ.complex (-(((q.out : BA) : Fin (k + 1) → F) ⬝ᵥ c)) = 1 := by
        intro q
        have hq : -((q.out : BA) : Fin (k + 1) → F) ∈
            latticeBox T (k + 1) (T.additiveConductor ψ - C) := by
          have hA : T.additiveConductor ψ - C = A := by omega
          rw [hA]
          exact neg_mem (q.out).property
        rw [← neg_dotProduct, UnitaryAdditiveCharacter.complex_apply,
          character_dotProduct_eq_one T ψ hq hc, Circle.coe_one]
      simp only [hterm, one_mul, hfc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    · rw [Set.indicator_of_notMem (show c ∉ (latticeBox T (k + 1) C : Set _) from hc)]
      by_cases hcN : c ∈ latticeBox T (k + 1) N
      · let χc : AddChar BA ℂ := ψ.complex.compAddMonoidHom
          ((AddMonoidHom.mk' (fun y : Fin (k + 1) → F => -(y ⬝ᵥ c)) (by
              intro a b
              simp only [add_dotProduct]
              ring)).comp BA.subtype)
        have hχc : ∀ y : BA,
            χc y = ψ.complex (-((y : Fin (k + 1) → F) ⬝ᵥ c)) := fun _ => rfl
        obtain ⟨y₁, hy₁A, hy₁⟩ : ∃ y ∈ latticeBox T (k + 1) A, ψ (y ⬝ᵥ c) ≠ 1 := by
          by_contra hall
          push Not at hall
          exact hc (mem_latticeBox_of_forall_character_eq_one T ψ hall)
        have hsum : ∑ q : BA ⧸ L, χc q.out = 0 := by
          refine sum_out_eq_zero L χc ?_ (c₁ := ⟨-y₁, neg_mem hy₁A⟩) ?_
          · intro y hy
            have hyB : (y : Fin (k + 1) → F) ∈ latticeBox T (k + 1) B := hy
            rw [hχc, ← neg_dotProduct, UnitaryAdditiveCharacter.complex_apply,
              character_dotProduct_eq_one T ψ (neg_mem hyB) hcN, Circle.coe_one]
          · rw [hχc]
            intro h
            apply hy₁
            simp only [neg_dotProduct, neg_neg, UnitaryAdditiveCharacter.complex_apply] at h
            exact Circle.coe_eq_one.mp h
        rw [← Finset.sum_mul]
        simp only [← hχc]
        rw [hsum, zero_mul]
      · simp only [hsupp c hcN, mul_zero, Finset.sum_const_zero]
  have hsum_int : ∑ q : BA ⧸ L,
      ∫ c, ψ.complex (-(((q.out : BA) : Fin (k + 1) → F) ⬝ᵥ c)) * f c ∂μ =
        ∫ c, (latticeBox T (k + 1) C : Set (Fin (k + 1) → F)).indicator
          (fun _ => (Fintype.card (BA ⧸ L) : ℂ) * f 0) c ∂μ := by
    rw [← integral_finsetSum _ fun q _ => hint _]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  rw [integral_indicator_const _ (isOpen_latticeBox T (k + 1) C).measurableSet] at hsum_int
  simp only [hzero, Finset.sum_const_zero] at hsum_int
  have hpos : μ.real (latticeBox T (k + 1) C : Set (Fin (k + 1) → F)) ≠ 0 := by
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨((isOpen_latticeBox T (k + 1) C).measure_pos μ ⟨0, zero_mem _⟩).ne',
      (isCompact_latticeBox T (k + 1) C).measure_lt_top.ne⟩
  have hne : (μ.real (latticeBox T (k + 1) C : Set (Fin (k + 1) → F)) : ℂ) *
      ((Fintype.card (BA ⧸ L) : ℂ) * f 0) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hpos)
      (mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) h0)
  apply hne
  rw [← Complex.real_smul]
  exact hsum_int.symm

end Fourier

/-! ### Elementary identities in the mirabolic group -/

section Group

variable {K : Type uF} [Field K] {m : ℕ}

end Group

/-! ### The twisted radical integral -/

section Transfer

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {m : ℕ}
variable [MeasurableSpace (Fin (m + 1) → K)] [BorelSpace (Fin (m + 1) → K)]
variable (μ : Measure (Fin (m + 1) → K)) [μ.IsAddHaarMeasure]
variable (ψ : UnitaryAdditiveCharacter K)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ξ : Representation ℂ (mirabolic (m + 1) K) V)
  (ξ' : Representation ℂ (mirabolic (m + 1) K) W) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)

end Transfer

/-! ### Local constancy and compact support of radical coefficients -/

section Support

variable {F : Type uF} [Field F] (T : LocalFieldData F) {m : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A smooth vector is fixed by the radical elements of some lattice box. -/
theorem exists_latticeBox_fixes (ξ : Representation ℂ (mirabolic (m + 1) F) V) :
    letI := T.topology
    IsSmooth ξ → ∀ v : V, ∃ l : ℤ, ∀ d ∈ latticeBox T (m + 1) l,
      ξ (radicalElement d : mirabolic (m + 1) F) v = v := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F := T.fieldT2
  intro hs v
  obtain ⟨K, hK⟩ := hs v
  have hfix : ∀ k ∈ K, ξ k v = v := fun k hk =>
    (Representation.mem_invariants _ v).mp hK ⟨k, hk⟩
  have hrad0 : {d : Fin (m + 1) → F |
      (radicalElement d : mirabolic (m + 1) F) ∈ K} ∈
        𝓝 (0 : Fin (m + 1) → F) := by
    apply (K.isOpen.preimage (continuous_subtype_val.comp continuous_radicalElement)).mem_nhds
    simp only [Set.mem_preimage, Function.comp_apply, radicalElement_zero]
    exact K.one_mem
  obtain ⟨l, hl⟩ := exists_latticeBox_subset T hrad0
  exact ⟨l, fun d hd => hfix _ (hl hd)⟩

/-- Near the identity, `GL_(m+1)` moves every large vector `c` to `c + d`. -/
theorem exists_mulVec_eq_add (H : Set (Langlands.GeneralLinear (m + 1) F)) :
    letI := T.topology
    IsOpen H → (1 : Langlands.GeneralLinear (m + 1) F) ∈ H →
      ∀ d : Fin (m + 1) → F, ∃ N : ℤ, ∀ c ∉ latticeBox T (m + 1) N,
        ∃ h ∈ H, h.val *ᵥ c = c + d := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F := T.fieldT2
  intro hH h1 d
  let φ : (Fin (m + 1) → F) → Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    fun r => 1 + Matrix.vecMulVec d r
  have hφ : Continuous φ :=
    continuous_const.add (continuous_const.matrix_vecMulVec continuous_id)
  have hO : IsOpen (Units.val '' H) :=
    (isOpenEmbedding_generalLinear_val (m + 1)).isOpenMap _ hH
  have hmem : φ ⁻¹' (Units.val '' H) ∈ 𝓝 (0 : Fin (m + 1) → F) := by
    apply (hO.preimage hφ).mem_nhds
    refine ⟨1, h1, ?_⟩
    simp [φ]
  obtain ⟨N₀, hN₀⟩ := exists_latticeBox_subset T hmem
  refine ⟨-N₀, fun c hc => ?_⟩
  rw [mem_latticeBox] at hc
  push Not at hc
  obtain ⟨j, hj⟩ := hc
  have hcj : c j ≠ 0 := fun h => hj (h ▸ zero_mem _)
  let r : Fin (m + 1) → F := Pi.single j (c j)⁻¹
  have hr : r ∈ latticeBox T (m + 1) N₀ := by
    rw [mem_latticeBox]
    intro i
    by_cases hi : i = j
    · subst hi
      have h := inv_mem_additiveLattice_of_notMem T hj
      rw [neg_neg] at h
      simpa [r] using h
    · simp [r, hi]
  obtain ⟨h, hH', hh⟩ := hN₀ hr
  refine ⟨h, hH', ?_⟩
  rw [hh]
  simp only [φ, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, r,
    single_dotProduct, inv_mul_cancel₀ hcj]
  simp

section Coefficients

variable (ξ : Representation ℂ (mirabolic (m + 1) F) V)
  (ξ' : Representation ℂ (mirabolic (m + 1) F) W) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (s : ℂ)

/-- An open subgroup of `GL_(m+1)` under which the radical coefficient of `x` and `w`
is invariant. -/
theorem exists_open_subgroup_coefficient
    (hβ : ∀ (g : mirabolic (m + 1) F) (v : V) (w : W),
      β (ξ g v) (ξ' g w) = determinantWeight (normalizedAbsoluteValue T) g.val (-s) * β v w) :
    letI := T.topology
    IsSmooth ξ → IsSmooth ξ' → ∀ (x : V) (w : W),
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
  have hfix₂ : ∀ k ∈ K₂, ξ' k w = w := fun k hk =>
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
  refine ⟨(K₁.toSubgroup ⊓ K₂.toSubgroup).comap levi ⊓
      EqualRankFrobenius.detOne (normalizedAbsoluteValue T), ?_, ?_⟩
  · exact ((K₁.isOpen.inter K₂.isOpen).preimage continuous_levi).inter hdet
  · rintro k ⟨⟨hk₁, hk₂⟩, hkdet⟩ c
    have hkdet' : normalizedAbsoluteValue T (Matrix.det k.val) = 1 := hkdet
    calc β (ξ (radicalElement (k.val *ᵥ c) : mirabolic (m + 1) F) x) w =
          β (ξ (radicalElement (k.val *ᵥ c) : mirabolic (m + 1) F) (ξ (levi k) x))
            (ξ' (levi k) w) := by
          rw [hfix₁ _ hk₁, hfix₂ _ hk₂]
      _ = β (ξ (levi k) (ξ (radicalElement c : mirabolic (m + 1) F) x))
            (ξ' (levi k) w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← levi_mul_radicalElement, map_mul,
            Module.End.mul_apply]
      _ = _ := by
          rw [hβ, determinantWeight_levi,
            EqualRankFrobenius.determinantWeight_eq_one _ hkdet', one_mul]

/-- Radical coefficients of a radical-generated representation have compact support. -/
theorem exists_coefficient_support
    (hβ : ∀ (g : mirabolic (m + 1) F) (v : V) (w : W),
      β (ξ g v) (ξ' g w) = determinantWeight (normalizedAbsoluteValue T) g.val (-s) * β v w) :
    letI := T.topology
    IsSmooth ξ → IsSmooth ξ' →
      Submodule.span ℂ (Set.range fun p : Mirabolic.radical (m + 1) F × V =>
        ξ (p.1 : mirabolic (m + 1) F) p.2 - p.2) = ⊤ →
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
    obtain ⟨H, hHo, hH⟩ := exists_open_subgroup_coefficient T ξ ξ' β s hβ hs hs' x w
    obtain ⟨N, hN⟩ := exists_mulVec_eq_add T (H : Set (Langlands.GeneralLinear (m + 1) F))
      hHo H.one_mem d
    refine ⟨N, fun c hc => ?_⟩
    obtain ⟨h, hh, hhc⟩ := hN c hc
    change β (ξ (radicalElement c : mirabolic (m + 1) F)
      (ξ (radicalElement d : mirabolic (m + 1) F) x - x)) w = 0
    rw [map_sub, rep_radicalElement_mul, map_sub, LinearMap.sub_apply, ← hhc, hH h hh c,
      sub_self]
  have hv : v ∈ S := by
    have hS : S = ⊤ := top_le_iff.mp (hgen ▸ hle)
    rw [hS]
    exact Submodule.mem_top
  exact hv

end Coefficients

end Support

/-! ### The pairing transfer -/

/-- Unnormalized `Φ⁻` transfers nonzero covariant pairings of radical-generated smooth
representations, lowering the exponent by one. -/
theorem phiMinusPairingTransfer (F : Type uF) [Field F]
    (T : LocalFieldData F) (m : ℕ) : PhiMinusPairingTransferStatement.{uF, uV, uW} F T m := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F := T.fieldT2
  have : SecondCountableTopology F := T.secondCountableTopology
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  intro ψ V _ _ W _ _ ξ ξ' hs hs' hgen s β hβ0
  let abv := normalizedAbsoluteValue T
  let μ : Measure (Fin (m + 1) → F) := Measure.addHaar
  have hβ : ∀ (g : mirabolic (m + 1) F) (v : V) (w : W),
      β.val (ξ g v) (ξ' g w) = determinantWeight abv g.val (-s) * β.val v w :=
    fun g v w => β.property g v w
  have hβu : ∀ (d : Fin (m + 1) → F) (v : V) (w : W),
      β.val (ξ (radicalElement d : mirabolic (m + 1) F) v)
        (ξ' (radicalElement d : mirabolic (m + 1) F) w) = β.val v w := by
    intro d v w
    rw [hβ, determinantWeight_radicalElement, one_mul]
  -- Haar scaling on the radical coordinates.
  have hχ (a : F) (ha : a ≠ 0) :
      (Measure.addHaar : Measure F).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • Measure.addHaar :=
    Langlands.AllField.HarmonicAnalysis.padicScalarHaarScaling F T Measure.addHaar (Units.mk0 a ha)
  have hscale : ∀ k : Langlands.GeneralLinear (m + 1) F,
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
  have hloc : ∀ v : V, ∃ l : ℤ, ∀ (c d : Fin (m + 1) → F),
      d ∈ latticeBox T (m + 1) l → ∀ w : W,
        β.val (ξ (radicalElement (c + d) : mirabolic (m + 1) F) v) w =
          β.val (ξ (radicalElement c : mirabolic (m + 1) F) v) w := by
    intro v
    obtain ⟨l, hl⟩ := exists_latticeBox_fixes T ξ hs v
    exact ⟨l, fun c d hd w => by rw [← rep_radicalElement_mul, hl d hd]⟩
  have hsupp : ∀ (v : V) (w : W), ∃ N : ℤ, ∀ c ∉ latticeBox T (m + 1) N,
      β.val (ξ (radicalElement c : mirabolic (m + 1) F) v) w = 0 :=
    exists_coefficient_support T ξ ξ' β.val s hβ hs hs' hgen
  have hcont : ∀ v w, Continuous fun c : Fin (m + 1) → F =>
      β.val (ξ (radicalElement c : mirabolic (m + 1) F) v) w := by
    intro v w
    obtain ⟨l, hl⟩ := hloc v
    exact continuous_of_forall_add_eq ((isOpen_latticeBox T (m + 1) l).mem_nhds (zero_mem _))
      fun c d hd => hl c d hd w
  have hcpt : ∀ v w, HasCompactSupport fun c : Fin (m + 1) → F =>
      β.val (ξ (radicalElement c : mirabolic (m + 1) F) v) w := by
    intro v w
    obtain ⟨N, hN⟩ := hsupp v w
    exact HasCompactSupport.intro (isCompact_latticeBox T (m + 1) N) hN
  -- The transferred form before descent.
  let ε : mirabolic (m + 1) F := levi (-1 : Langlands.GeneralLinear (m + 1) F)
  let B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ := (transferForm μ ψ ξ β.val hcont hcpt).compl₂ (ξ' ε)
  have hB : ∀ v w, B v w = transferIntegral μ ψ ξ β.val v (ξ' ε w) := fun _ _ => rfl
  have hBl : ∀ (d : Fin (m + 1) → F) v w,
      B (ξ (radicalElement d : mirabolic (m + 1) F) v) w =
        ψ.complex (d (Fin.last m)) * B v w := by
    intro d v w
    rw [hB, hB, transferIntegral_radical_left]
  have hBr : ∀ (d : Fin (m + 1) → F) v w,
      B v (ξ' (radicalElement d : mirabolic (m + 1) F) w) =
        ψ.complex (d (Fin.last m)) * B v w := by
    intro d v w
    rw [hB, hB, ← Module.End.mul_apply, ← map_mul, levi_neg_one_mul_radicalElement, map_mul,
      Module.End.mul_apply, transferIntegral_radical_right μ ψ ξ ξ' β.val hβu,
      transferIntegral_radical_left]
  -- Descent to the coinvariants.
  let Θ := T.mirabolicTheta ψ m
  have hΘ : ∀ u : Mirabolic.radical (m + 1) F,
      ∃ d : Fin (m + 1) → F, radicalElement d = u ∧
        (Θ u : ℂ) = ψ.complex (d (Fin.last m)) := by
    intro u
    refine ⟨radicalCoordinates u, radicalElement_coordinates u, ?_⟩
    rw [← theta_radicalElement ψ m (radicalCoordinates u), radicalElement_coordinates u]
    rfl
  let B₂ := Jacquet.Localization.lift ξ' (Mirabolic.radical (m + 1) F) Θ B.flip
    (fun u w => by
      obtain ⟨d, rfl, hd⟩ := hΘ u
      ext v
      rw [LinearMap.smul_apply, LinearMap.flip_apply, LinearMap.flip_apply, hd, smul_eq_mul]
      exact hBr d v w)
  let B₄ := Jacquet.Localization.lift ξ (Mirabolic.radical (m + 1) F) Θ B₂.flip
    (fun u v => by
      obtain ⟨d, rfl, hd⟩ := hΘ u
      apply Jacquet.Localization.hom_ext
      ext w
      change B (ξ (radicalElement d : mirabolic (m + 1) F) v) w = (Θ _ : ℂ) • B v w
      rw [hd, smul_eq_mul]
      exact hBl d v w)
  have hB₄ : ∀ v w, B₄ (Jacquet.Localization.mk ξ _ Θ v) (Jacquet.Localization.mk ξ' _ Θ w) =
      B v w := fun _ _ => rfl
  refine ⟨⟨B₄, ?_⟩, ?_⟩
  · -- Covariance under the smaller mirabolic group.
    intro h a b
    obtain ⟨v, rfl⟩ := phiMinusQuotient_surjective T ψ m (SmoothRep.of ξ hs) a
    obtain ⟨w, rfl⟩ := phiMinusQuotient_surjective T ψ m (SmoothRep.of ξ' hs') b
    change B (ξ (successor h) v) (ξ' (successor h) w) =
      determinantWeight abv h.val (-(s - 1)) * B v w
    have hε : ξ' ε (ξ' (successor h) w) = ξ' (successor h) (ξ' ε w) := by
      rw [← Module.End.mul_apply, ← map_mul, show ε * successor h = successor h * ε from
        levi_neg_one_commute _, map_mul, Module.End.mul_apply]
    rw [hB, hB, hε, show successor h = levi (h : Langlands.GeneralLinear (m + 1) F) from
      rfl, transferIntegral_levi μ ψ ξ ξ' β.val abv T.normalizedAbsHom habv hscale s hβ hcont]
    simp only [mulVec_last]
    rw [neg_sub, EqualRankFrobenius.determinantWeight_one_sub]
    unfold transferIntegral
    ring
  · -- Nonvanishing.
    intro h0
    obtain ⟨v₀, w₀, hvw⟩ : ∃ v w, β.val v w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hβ0 (Subtype.ext (LinearMap.ext₂ hall))
    obtain ⟨l, hl⟩ := hloc v₀
    obtain ⟨N, hN⟩ := hsupp v₀ w₀
    obtain ⟨y, hy0, hy⟩ := exists_integral_character_ne_zero T ψ μ
      (fun c => β.val (ξ (radicalElement c : mirabolic (m + 1) F) v₀) w₀) l N
      (fun c d hd => hl c d hd w₀) hN (by simpa [rep_radicalElement_zero] using hvw)
    obtain ⟨g, rfl⟩ := EqualRankFrobenius.exists_lastRow_eq y hy0
    let w₁ := ξ' ε⁻¹ w₀
    have hw₁ : ξ' ε w₁ = w₀ := by
      simp only [w₁, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    have hval : B (ξ (levi g) v₀) (ξ' (levi g) w₁) =
        determinantWeight abv g (-s) * (abv (Matrix.det g.val) : ℂ) *
          ∫ c, ψ.complex (-(lastRow g ⬝ᵥ c)) *
            β.val (ξ (radicalElement c : mirabolic (m + 1) F) v₀) w₀ ∂μ := by
      rw [hB, ← Module.End.mul_apply, ← map_mul, levi_neg_one_commute, map_mul,
        Module.End.mul_apply, hw₁,
        transferIntegral_levi μ ψ ξ ξ' β.val abv T.normalizedAbsHom habv hscale s hβ hcont]
      rfl
    have hne : B (ξ (levi g) v₀) (ξ' (levi g) w₁) ≠ 0 := by
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

end Langlands.AllField.Derivative.Mirabolic
