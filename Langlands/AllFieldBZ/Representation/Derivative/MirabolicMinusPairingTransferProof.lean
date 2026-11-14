import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicLatticeBox
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicMinus
import Langlands.AllFieldBZ.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.Derivative.Mirabolic hiding character_dotProduct_eq_one character_mul_eq_one coe_latticeBox exists_integral_character_ne_zero exists_latticeBox_fixes exists_latticeBox_subset exists_mulVec_eq_add exists_ne_zero_mem_additiveLattice exists_open_subgroup_coefficient finite_latticeBox_quotient inv_mem_additiveLattice_of_notMem isCompact_latticeBox isOpen_ker_phiMinusCharacter isOpen_ker_psiMinusCharacter isOpen_latticeBox ker_psiMinusQuotient latticeBox latticeBox_mono mem_latticeBox mem_latticeBox_of_forall_character_eq_one phiMinus phiMinusCharacter phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinus_action phiMinus_map_quotient psiMinus psiMinusCharacter psiMinusQuotient psiMinusQuotient_radical psiMinusQuotient_surjective psiMinusUnnormalized psiMinus_action psiMinus_action_eq_smul psiMinus_map_quotient
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
open Langlands.RankinSelberg hiding normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllFieldBZ.RankinSelberg
open Topology
open MeasureTheory
open scoped Matrix
open scoped NNReal
universe uF uV uW

/-! ### A finite character-sum argument on the radical coordinates -/

section Fourier
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- A locally constant, compactly supported function `f` on `F^(k+1)` with `f 0 ≠ 0` has
a nonzero twisted integral `∫ ψ(-(y ⬝ c)) f(c) dc` at some `y ≠ 0`. -/
theorem exists_integral_character_ne_zero {k : ℕ} :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : Measure (Fin (k + 1) → F.Carrier))
      [μ.IsAddHaarMeasure] (f : (Fin (k + 1) → F.Carrier) → ℂ) (l N : ℤ),
      (∀ c, ∀ d ∈ latticeBox T (k + 1) l, f (c + d) = f c) →
      (∀ c ∉ latticeBox T (k + 1) N, f c = 0) → f 0 ≠ 0 →
      ∃ y : Fin (k + 1) → F.Carrier, y ≠ 0 ∧
        ∫ c, ψ.complex (-(y ⬝ᵥ c)) * f c ∂μ ≠ 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ μ _ f l N hper hsupp h0
  have hcont : Continuous f :=
    continuous_of_forall_add_eq ((isOpen_latticeBox T (k + 1) l).mem_nhds (zero_mem _))
      fun c d hd => hper c d hd
  have hint : ∀ y : Fin (k + 1) → F.Carrier,
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
  have hzero : ∀ y : Fin (k + 1) → F.Carrier, ∫ c, ψ.complex (-(y ⬝ᵥ c)) * f c ∂μ = 0 := by
    have hmass : ∫ c, f c ∂μ = 0 := by
      obtain ⟨t, ht0, ht⟩ := exists_ne_zero_mem_additiveLattice T B
      have hy : (Pi.single 0 t : Fin (k + 1) → F.Carrier) ∈ latticeBox T (k + 1) B := by
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
  have hpoint : ∀ c : Fin (k + 1) → F.Carrier,
      ∑ q : BA ⧸ L, ψ.complex (-(((q.out : BA) : Fin (k + 1) → F.Carrier) ⬝ᵥ c)) * f c =
        (latticeBox T (k + 1) C : Set (Fin (k + 1) → F.Carrier)).indicator
          (fun _ => (Fintype.card (BA ⧸ L) : ℂ) * f 0) c := by
    intro c
    by_cases hc : c ∈ latticeBox T (k + 1) C
    · rw [Set.indicator_of_mem (show c ∈ (latticeBox T (k + 1) C : Set _) from hc)]
      have hfc : f c = f 0 := by
        have h := hper 0 c (latticeBox_mono T hCl hc)
        rwa [zero_add] at h
      have hterm : ∀ q : BA ⧸ L,
          ψ.complex (-(((q.out : BA) : Fin (k + 1) → F.Carrier) ⬝ᵥ c)) = 1 := by
        intro q
        have hq : -((q.out : BA) : Fin (k + 1) → F.Carrier) ∈
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
          ((AddMonoidHom.mk' (fun y : Fin (k + 1) → F.Carrier => -(y ⬝ᵥ c)) (by
              intro a b
              simp only [add_dotProduct]
              ring)).comp BA.subtype)
        have hχc : ∀ y : BA,
            χc y = ψ.complex (-((y : Fin (k + 1) → F.Carrier) ⬝ᵥ c)) := fun _ => rfl
        obtain ⟨y₁, hy₁A, hy₁⟩ : ∃ y ∈ latticeBox T (k + 1) A, ψ (y ⬝ᵥ c) ≠ 1 := by
          by_contra hall
          push Not at hall
          exact hc (mem_latticeBox_of_forall_character_eq_one T ψ hall)
        have hsum : ∑ q : BA ⧸ L, χc q.out = 0 := by
          refine sum_out_eq_zero L χc ?_ (c₁ := ⟨-y₁, neg_mem hy₁A⟩) ?_
          · intro y hy
            have hyB : (y : Fin (k + 1) → F.Carrier) ∈ latticeBox T (k + 1) B := hy
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
      ∫ c, ψ.complex (-(((q.out : BA) : Fin (k + 1) → F.Carrier) ⬝ᵥ c)) * f c ∂μ =
        ∫ c, (latticeBox T (k + 1) C : Set (Fin (k + 1) → F.Carrier)).indicator
          (fun _ => (Fintype.card (BA ⧸ L) : ℂ) * f 0) c ∂μ := by
    rw [← integral_finsetSum _ fun q _ => hint _]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  rw [integral_indicator_const _ (isOpen_latticeBox T (k + 1) C).measurableSet] at hsum_int
  simp only [hzero, Finset.sum_const_zero] at hsum_int
  have hpos : μ.real (latticeBox T (k + 1) C : Set (Fin (k + 1) → F.Carrier)) ≠ 0 := by
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨((isOpen_latticeBox T (k + 1) C).measure_pos μ ⟨0, zero_mem _⟩).ne',
      (isCompact_latticeBox T (k + 1) C).measure_lt_top.ne⟩
  have hne : (μ.real (latticeBox T (k + 1) C : Set (Fin (k + 1) → F.Carrier)) : ℂ) *
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
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData) {m : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A smooth vector is fixed by the radical elements of some lattice box. -/
theorem exists_latticeBox_fixes (ξ : Representation ℂ (mirabolic (m + 1) F.Carrier) V) :
    letI := T.topology
    IsSmooth ξ → ∀ v : V, ∃ l : ℤ, ∀ d ∈ latticeBox T (m + 1) l,
      ξ (radicalElement d : mirabolic (m + 1) F.Carrier) v = v := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  intro hs v
  obtain ⟨K, hK⟩ := hs v
  have hfix : ∀ k ∈ K, ξ k v = v := fun k hk =>
    (Representation.mem_invariants _ v).mp hK ⟨k, hk⟩
  have hrad0 : {d : Fin (m + 1) → F.Carrier |
      (radicalElement d : mirabolic (m + 1) F.Carrier) ∈ K} ∈
        𝓝 (0 : Fin (m + 1) → F.Carrier) := by
    apply (K.isOpen.preimage (continuous_subtype_val.comp continuous_radicalElement)).mem_nhds
    simp only [Set.mem_preimage, Function.comp_apply, radicalElement_zero]
    exact K.one_mem
  obtain ⟨l, hl⟩ := exists_latticeBox_subset T hrad0
  exact ⟨l, fun d hd => hfix _ (hl hd)⟩

/-- Near the identity, `GL_(m+1)` moves every large vector `c` to `c + d`. -/
theorem exists_mulVec_eq_add (H : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) :
    letI := T.topology
    IsOpen H → (1 : Langlands.GeneralLinear (m + 1) F.Carrier) ∈ H →
      ∀ d : Fin (m + 1) → F.Carrier, ∃ N : ℤ, ∀ c ∉ latticeBox T (m + 1) N,
        ∃ h ∈ H, h.val *ᵥ c = c + d := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  intro hH h1 d
  let φ : (Fin (m + 1) → F.Carrier) → Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier :=
    fun r => 1 + Matrix.vecMulVec d r
  have hφ : Continuous φ :=
    continuous_const.add (continuous_const.matrix_vecMulVec continuous_id)
  have hO : IsOpen (Units.val '' H) :=
    (isOpenEmbedding_generalLinear_val (m + 1)).isOpenMap _ hH
  have hmem : φ ⁻¹' (Units.val '' H) ∈ 𝓝 (0 : Fin (m + 1) → F.Carrier) := by
    apply (hO.preimage hφ).mem_nhds
    refine ⟨1, h1, ?_⟩
    simp [φ]
  obtain ⟨N₀, hN₀⟩ := exists_latticeBox_subset T hmem
  refine ⟨-N₀, fun c hc => ?_⟩
  rw [mem_latticeBox] at hc
  push Not at hc
  obtain ⟨j, hj⟩ := hc
  have hcj : c j ≠ 0 := fun h => hj (h ▸ zero_mem _)
  let r : Fin (m + 1) → F.Carrier := Pi.single j (c j)⁻¹
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
variable (ξ : Representation ℂ (mirabolic (m + 1) F.Carrier) V)
  (ξ' : Representation ℂ (mirabolic (m + 1) F.Carrier) W) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (s : ℂ)

/-- An open subgroup of `GL_(m+1)` under which the radical coefficient of `x` and `w`
is invariant. -/
theorem exists_open_subgroup_coefficient
    (hβ : ∀ (g : mirabolic (m + 1) F.Carrier) (v : V) (w : W),
      β (ξ g v) (ξ' g w) = determinantWeight (Langlands.AllFieldBZ.RankinSelberg.normalizedAbsoluteValue T) g.val (-s) * β v w) :
    letI := T.topology
    IsSmooth ξ → IsSmooth ξ' → ∀ (x : V) (w : W),
      ∃ H : Subgroup (Langlands.GeneralLinear (m + 1) F.Carrier),
        IsOpen (H : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) ∧
        ∀ k ∈ H, ∀ c : Fin (m + 1) → F.Carrier,
          β (ξ (radicalElement (k.val *ᵥ c) : mirabolic (m + 1) F.Carrier) x) w =
            β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) x) w := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  intro hs hs' x w
  obtain ⟨K₁, hK₁⟩ := hs x
  obtain ⟨K₂, hK₂⟩ := hs' w
  have hfix₁ : ∀ k ∈ K₁, ξ k x = x := fun k hk =>
    (Representation.mem_invariants _ x).mp hK₁ ⟨k, hk⟩
  have hfix₂ : ∀ k ∈ K₂, ξ' k w = w := fun k hk =>
    (Representation.mem_invariants _ w).mp hK₂ ⟨k, hk⟩
  have hdet : IsOpen {g : Langlands.GeneralLinear (m + 1) F.Carrier |
      Langlands.AllFieldBZ.RankinSelberg.normalizedAbsoluteValue T (Matrix.det g.val) = 1} := by
    have e : {g : Langlands.GeneralLinear (m + 1) F.Carrier |
        Langlands.AllFieldBZ.RankinSelberg.normalizedAbsoluteValue T (Matrix.det g.val) = 1} =
        ((T.determinantNorm (m + 1)).ker :
          Set (Langlands.GeneralLinear (m + 1) F.Carrier)) := by
      ext g
      rw [Set.mem_ofPred_eq, SetLike.mem_coe, MonoidHom.mem_ker, ← Units.val_eq_one,
        ← NNReal.coe_eq_one, T.determinantNorm_coe]
      rfl
    rw [e]
    exact T.isOpen_ker_determinantNorm (m + 1)
  refine ⟨(K₁.toSubgroup ⊓ K₂.toSubgroup).comap levi ⊓
      EqualRankFrobenius.detOne (Langlands.AllFieldBZ.RankinSelberg.normalizedAbsoluteValue T), ?_, ?_⟩
  · exact ((K₁.isOpen.inter K₂.isOpen).preimage continuous_levi).inter hdet
  · rintro k ⟨⟨hk₁, hk₂⟩, hkdet⟩ c
    have hkdet' : Langlands.AllFieldBZ.RankinSelberg.normalizedAbsoluteValue T (Matrix.det k.val) = 1 := hkdet
    calc β (ξ (radicalElement (k.val *ᵥ c) : mirabolic (m + 1) F.Carrier) x) w =
          β (ξ (radicalElement (k.val *ᵥ c) : mirabolic (m + 1) F.Carrier) (ξ (levi k) x))
            (ξ' (levi k) w) := by
          rw [hfix₁ _ hk₁, hfix₂ _ hk₂]
      _ = β (ξ (levi k) (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) x))
            (ξ' (levi k) w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← levi_mul_radicalElement, map_mul,
            Module.End.mul_apply]
      _ = _ := by
          rw [hβ, determinantWeight_levi,
            EqualRankFrobenius.determinantWeight_eq_one _ hkdet', one_mul]

end Coefficients
end Support
/-! ### The pairing transfer -/

end Langlands.AllFieldBZ.Derivative.Mirabolic
