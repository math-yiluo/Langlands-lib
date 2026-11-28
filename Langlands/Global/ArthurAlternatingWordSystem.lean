import Langlands.Global.ArthurAlternatingConstantTermFamily
import Langlands.Global.AdelicNormOneFamilyDecay

/-! # The system of derivatives of an alternating constant term

Let `R ⊆ S ⊆ Δ₀` and let `φ` on `G(𝔸)¹` be of class `Cʳ` at a fixed level. For `n ≤ r`,
`alternatingWordSystem` assigns to each word `w` of length at most `n` Arthur's alternating
constant term over `R ⊆ P ⊆ S` of the extension of `D_w φ`, and `0` to longer words. These
functions are continuous, right invariant under the level, and left invariant under the rational
points of every standard radical and the adelic radical of `S`. Their constant terms along the
radical of the maximal standard parabolic indexed by `Δ₀ \ {α}` vanish for each `α ∈ S \ R`.
For `w.length < n`, the integrated derivative identity for the system at `w` uses the system at
`l :: w` as the coordinate derivative along `l`. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped Classical CategoryTheory.MonObj ENNReal

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSubgroupPoints RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  {d e : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom} (At : NormOneLieAtlas F G hsmooth e)

local notation "A" => AdelicGroupPoints F G
local notation "G¹" => normOneSubgroup F G
local notation "Δ" => simpleFinset ν hG hi
local notation "J" => Finset (characterLattice T)
local notation "U₀(" S ")" => Standard.unipotentHom i ν S

/-- Arthur's alternating constant term of the extension of the word derivatives of `φ`, for words
of length at most `n`. -/
def alternatingWordSystem (R S : J) (n : ℕ) (φ : G¹ → ℂ) (w : List (Fin e)) : A → ℂ :=
  if w.length ≤ n then
    alternatingConstantTerm (ν := ν) hG hi R S (normOneExtension hG (normOneWordDerivative At w φ))
  else 0

variable {K₀ : Subgroup (FiniteAdelicGroupPoints F G)}
  {hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))}

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Continuity and rational invariance of the word derivatives. -/
theorem normOneWordDerivative_props (hK₀o : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G)))
    {φ : G¹ → ℂ} {r : ℕ} (hφ : IsNormOneCr At r K₀ hK₀ φ) (w : List (Fin e))
    (hw : w.length ≤ r) :
    Continuous (normOneWordDerivative At w φ) ∧
      (∀ (g : rationalNormOneSubgroup F G) x,
        normOneWordDerivative At w φ ((g : G¹) * x) = normOneWordDerivative At w φ x) ∧
      ∀ (k : K₀) x, normOneWordDerivative At w φ (x * finiteLevelInclusion F G K₀ hK₀ k) =
        normOneWordDerivative At w φ x := by
  have h := isNormOneCr_normOneWordDerivative At hφ w hw
  exact ⟨continuous_of_isNormOneCr At hK₀o h, h.1, h.2.1⟩

/-- The system as an alternating constant term of a continuous rational function. -/
theorem alternatingWordSystem_eq (hK₀o : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G)))
    (R S : J) {n r : ℕ} (hnr : n ≤ r) {φ : G¹ → ℂ} (hφ : IsNormOneCr At r K₀ hK₀ φ)
    (w : List (Fin e)) (hw : w.length ≤ n) :
    alternatingWordSystem (ν := ν) hG hi At R S n φ w =
      alternatingConstantTerm (ν := ν) hG hi R S (evaluate F G (normOneExtensionCRF hG
        (normOneWordDerivative At w φ) (normOneWordDerivative_props At hK₀o hφ w (hw.trans hnr)).1
        (normOneWordDerivative_props At hK₀o hφ w (hw.trans hnr)).2.1)) := by
  simp [alternatingWordSystem, hw]

variable {hG hi}

omit [IsAffine G.X.left] [Mono i.hom.hom.left] in
/-- Constant terms of right-invariant functions are right invariant. -/
theorem constantTerm_mul_right_of_invariant (P : Set (characterLattice T)) {f : A → ℂ} {g : A}
    (hf : ∀ y, f (y * g) = f y) (x : A) :
    constantTerm F i ν P f (x * g) = constantTerm F i ν P f x := by
  unfold constantTerm subgroupConstantTerm
  congr 1
  funext q
  rw [← mul_assoc, hf]

include hν in
/-- **Continuity of the system.** -/
theorem continuous_alternatingWordSystem (hK₀o : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G)))
    {R S : J} (hS : S ⊆ Δ) {n r : ℕ} (hnr : n ≤ r) {φ : G¹ → ℂ} (hφ : IsNormOneCr At r K₀ hK₀ φ)
    (w : List (Fin e)) : Continuous (alternatingWordSystem (ν := ν) hG hi At R S n φ w) := by
  by_cases hw : w.length ≤ n
  · obtain ⟨hc, hinv, -⟩ := normOneWordDerivative_props At hK₀o hφ w (hw.trans hnr)
    simp only [alternatingWordSystem, hw, ite_true]
    unfold alternatingConstantTerm
    refine continuous_finsetSum _ fun P hP => continuous_const.mul ?_
    have hP₀ : (P : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun α hα =>
      (mem_simpleFinset hG hi).mp (hS (Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1 hα))
    exact continuous_constantTerm_normOneExtension hG hi hν hP₀ hc hinv
  · simp only [alternatingWordSystem, hw, ite_false]
    exact continuous_const

include hν in
/-- **Joint measurability of the system of a family.** -/
theorem measurable_alternatingWordSystem (hK₀o : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G)))
    {R S : J} (hS : S ⊆ Δ) {n r : ℕ} (hnr : n ≤ r) {Ω : Type w} [MeasurableSpace Ω]
    {φ : Ω → G¹ → ℂ} (hφ : ∀ o, IsNormOneCr At r K₀ hK₀ (φ o))
    (hm : Measurable (fun p : Ω × G¹ => φ p.1 p.2)) (w : List (Fin e)) :
    Measurable (fun p : Ω × A => alternatingWordSystem (ν := ν) hG hi At R S n (φ p.1) w p.2) := by
  by_cases hw : w.length ≤ n
  · simp only [alternatingWordSystem, hw, ite_true]
    unfold alternatingConstantTerm
    refine Finset.measurable_sum _ fun P hP => measurable_const.mul ?_
    have hP₀ : (P : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun α hα =>
      (mem_simpleFinset hG hi).mp (hS (Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1 hα))
    exact measurable_constantTerm_normOneExtension_family hG hi hν hP₀
      (ψ := fun o => normOneWordDerivative At w (φ o))
      (fun o => (normOneWordDerivative_props At hK₀o (hφ o) w (hw.trans hnr)).1)
      (fun o => (normOneWordDerivative_props At hK₀o (hφ o) w (hw.trans hnr)).2.1)
      (measurable_normOneWordDerivative At hφ hm w (hw.trans hnr))
  · simp only [alternatingWordSystem, hw, ite_false]
    exact measurable_const

/-- **Right invariance under the level.** -/
theorem alternatingWordSystem_mul_ofFinite (hK₀o : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G)))
    (R S : J) {n r : ℕ} (hnr : n ≤ r) {φ : G¹ → ℂ} (hφ : IsNormOneCr At r K₀ hK₀ φ)
    (w : List (Fin e)) (l : FiniteAdelicGroupPoints F G) (hl : l ∈ K₀) (x : A) :
    alternatingWordSystem (ν := ν) hG hi At R S n φ w (x * ofFinite F G l) =
      alternatingWordSystem (ν := ν) hG hi At R S n φ w x := by
  by_cases hw : w.length ≤ n
  · obtain ⟨-, -, hlev⟩ := normOneWordDerivative_props At hK₀o hφ w (hw.trans hnr)
    simp only [alternatingWordSystem, hw, ite_true]
    unfold alternatingConstantTerm
    refine Finset.sum_congr rfl fun P _ => congrArg (_ * ·) ?_
    exact constantTerm_mul_right_of_invariant (g := ofFinite F G l) (P : Set (characterLattice T))
      (f := normOneExtension hG (normOneWordDerivative At w φ))
      (fun y => normOneExtension_mul_ofFinite hG hK₀ hlev l hl y) x
  · simp only [alternatingWordSystem, hw, ite_false, Pi.zero_apply]

include hν in
/-- **Rational invariance** under every standard unipotent radical. -/
theorem alternatingWordSystem_isRationalInvariant
    (hK₀o : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G))) {R S : J} (hS : S ⊆ Δ) {n r : ℕ}
    (hnr : n ≤ r) {φ : G¹ → ℂ} (hφ : IsNormOneCr At r K₀ hK₀ φ) (w : List (Fin e))
    (P : StandardIndex F G i ν) :
    ConstantTermComposition.IsRationalInvariant F G (SubgroupFunctor.range (U₀(P.val)))
      (alternatingWordSystem (ν := ν) hG hi At R S n φ w) := by
  by_cases hw : w.length ≤ n
  · rw [alternatingWordSystem_eq hG hi At hK₀o R S hnr hφ w hw]
    exact alternatingConstantTerm_isRationalInvariant hG hi hν hS P _
  · intro c _ x
    simp only [alternatingWordSystem, hw, ite_false, Pi.zero_apply]

include hν in
/-- **Left invariance under the radical of `S`.** -/
theorem alternatingWordSystem_radical_mul
    (hK₀o : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G))) {R S : J} (hS : S ⊆ Δ) {n r : ℕ}
    (hnr : n ≤ r) {φ : G¹ → ℂ} (hφ : IsNormOneCr At r K₀ hK₀ φ) (w : List (Fin e)) (u : A)
    (hu : u ∈ adelicPoints F G (SubgroupFunctor.range (U₀((S : Set (characterLattice T))))))
    (x : A) :
    alternatingWordSystem (ν := ν) hG hi At R S n φ w (u * x) =
      alternatingWordSystem (ν := ν) hG hi At R S n φ w x := by
  by_cases hw : w.length ≤ n
  · rw [alternatingWordSystem_eq hG hi At hK₀o R S hnr hφ w hw]
    exact alternatingConstantTerm_radical_mul hG hi hν hS _ u hu x
  · simp only [alternatingWordSystem, hw, ite_false, Pi.zero_apply]

include hν in
/-- **Vanishing constant term** along the maximal standard radical omitting a root of
`S \ R`. -/
theorem constantTerm_alternatingWordSystem_eq_zero
    (hK₀o : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G))) {R S : J} (hRS : R ⊆ S)
    (hS : S ⊆ Δ) {α : characterLattice T} (hα : α ∈ S \ R) {n r : ℕ} (hnr : n ≤ r)
    {φ : G¹ → ℂ} (hφ : IsNormOneCr At r K₀ hK₀ φ) (w : List (Fin e)) :
    constantTerm F i ν (simpleRelativeRoots i ν \ {α})
      (alternatingWordSystem (ν := ν) hG hi At R S n φ w) = 0 := by
  by_cases hw : w.length ≤ n
  · rw [alternatingWordSystem_eq hG hi At hK₀o R S hnr hφ w hw]
    exact constantTerm_alternatingConstantTerm_eq_zero hG hi hν hRS hS hα _
  · simp only [alternatingWordSystem, hw, ite_false]
    funext x
    simp [constantTerm, subgroupConstantTerm]

include hν in
/-- **Integrated derivative identity.** For words shorter than `n`, the system at `l :: w` is
the derivative along `l` of the system at `w`. -/
theorem isNormOnePathDerivative_alternatingWordSystem
    (hK₀o : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G))) {R S : J} (hS : S ⊆ Δ) {n r : ℕ}
    (hnr : n ≤ r) {φ : G¹ → ℂ} (hφ : IsNormOneCr At r K₀ hK₀ φ) (w : List (Fin e))
    (hw : w.length < n) :
    IsNormOnePathDerivative At (alternatingWordSystem (ν := ν) hG hi At R S n φ w)
      (fun l => alternatingWordSystem (ν := ν) hG hi At R S n φ (l :: w)) := by
  have hw' : w.length ≤ n := hw.le
  have hlw (l : Fin e) : (l :: w).length ≤ n := by simpa using hw
  obtain ⟨hc, hinv, -⟩ := normOneWordDerivative_props At hK₀o hφ w (hw'.trans hnr)
  have hc' (l : Fin e) := (normOneWordDerivative_props At hK₀o hφ (l :: w) ((hlw l).trans hnr)).1
  have hinv' (l : Fin e) :=
    (normOneWordDerivative_props At hK₀o hφ (l :: w) ((hlw l).trans hnr)).2.1
  have hret : IsNormOnePathDerivative At (normOneExtension hG (normOneWordDerivative At w φ))
      (fun l => normOneExtension hG (normOneWordDerivative At (l :: w) φ)) :=
    isNormOnePathDerivative_comp_retraction At (normOneRetraction hG) (normOneRetraction_coe hG)
      (mdifferentiable_slice_normOneWordDerivative At hφ w (lt_of_lt_of_le hw hnr)) hc'
  have hP₀ (P : J) (hP : P ∈ S.powerset.filter (R ⊆ ·)) :
      (P : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun α hα =>
    (mem_simpleFinset hG hi).mp (hS (Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1 hα))
  have h := isNormOnePathDerivative_sum At (S.powerset.filter (R ⊆ ·))
    (fun P => (-1 : ℂ) ^ ((Δ).card - P.card))
    (fun P => constantTerm F i ν (P : Set (characterLattice T))
      (normOneExtension hG (normOneWordDerivative At w φ)))
    (fun P l => constantTerm F i ν (P : Set (characterLattice T))
      (normOneExtension hG (normOneWordDerivative At (l :: w) φ)))
    (fun P hP l => continuous_constantTerm_normOneExtension hG hi hν (hP₀ P hP) (hc' l) (hinv' l))
    (fun P hP => isNormOnePathDerivative_constantTerm_normOneExtension hG hi hν At (hP₀ P hP) hc
      hc' hinv hinv' hret)
  simp only [alternatingWordSystem, hw', hlw, ite_true]
  exact h

include hν in
/-- **Family height bound.** If the integrals over a family of a word derivative are bounded by
`M` times a power `H^{n₀}` of the height on `G(𝔸)¹`, then so are the integrals of the system at
that word, up to a constant depending on `R`, `S`, the chosen height `H` and `n₀`. -/
theorem exists_lintegral_alternatingWordSystem_le
    (hK₀o : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G))) {R S : J} (hS : S ⊆ Δ) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (n₀ : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ {Ω : Type w} [MeasurableSpace Ω] (mΩ : Measure Ω) (φ : Ω → G¹ → ℂ)
      (n r : ℕ), n ≤ r → (∀ o, IsNormOneCr At r K₀ hK₀ (φ o)) →
      Measurable (fun p : Ω × G¹ => φ p.1 p.2) → ∀ (M : ℝ≥0∞) (w : List (Fin e)),
      (∀ y : G¹, ∫⁻ o, ‖normOneWordDerivative At w (φ o) y‖ₑ ∂mΩ ≤
        ENNReal.ofReal (adelicHeight F G rho y ^ n₀) * M) →
      ∀ x : G¹, ∫⁻ o, ‖alternatingWordSystem (ν := ν) hG hi At R S n (φ o) w x‖ₑ ∂mΩ ≤
        ENNReal.ofReal (Cg * adelicHeight F G rho x ^ n₀) * M := by
  let H := adelicHeight F G rho
  have hH : Continuous H := continuous_adelicHeight F G rho hN
  have hH1 (x : A) : 1 ≤ H x := one_le_adelicHeight F G rho hN x
  let Idx := S.powerset.filter (R ⊆ ·)
  have hP₀ (P : J) (hP : P ∈ Idx) :
      (P : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := fun α hα =>
    (mem_simpleFinset hG hi).mp (hS (Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1 hα))
  have hex (P : J) (hP : P ∈ Idx) :=
    exists_lintegral_constantTerm_normOneExtension_le.{u, w} hG hi hν (hP₀ P hP)
  choose CP hCP hCP₁ hbound using hex
  have hE (P : J) (hP : P ∈ Idx) : ∃ E : ℝ, 1 ≤ E ∧ ∀ h ∈ CP P hP, H h ≤ E := by
    obtain ⟨E, hE⟩ := (hCP P hP).bddAbove_image hH.continuousOn
    exact ⟨max E 1, le_max_right _ _, fun h hh => (hE ⟨h, hh, rfl⟩).trans (le_max_left _ _)⟩
  choose E hE1 hEb using hE
  let Efun (P : J) : ℝ := if hP : P ∈ Idx then E P hP else 1
  have hEf1 (P : J) : 1 ≤ Efun P := by
    by_cases hP : P ∈ Idx
    · simp only [Efun, dite_eq_left hP]; exact hE1 P hP
    · simp only [Efun, dite_eq_right hP, le_refl]
  refine ⟨∑ P ∈ Idx, Efun P ^ n₀,
    Finset.sum_nonneg fun P _ => pow_nonneg (zero_le_one.trans (hEf1 P)) _, ?_⟩
  intro Ω _ mΩ φ n r hnr hφ hm M w hw x
  by_cases hwn : w.length ≤ n
  swap
  · simp only [alternatingWordSystem, hwn, ite_false, Pi.zero_apply, enorm_zero,
      MeasureTheory.lintegral_zero, zero_le]
  have hc (o : Ω) := (normOneWordDerivative_props At hK₀o (hφ o) w (hwn.trans hnr)).1
  have hinv (o : Ω) := (normOneWordDerivative_props At hK₀o (hφ o) w (hwn.trans hnr)).2.1
  have hmw := measurable_normOneWordDerivative At hφ hm w (hwn.trans hnr)
  let f (P : J) (o : Ω) : ℝ≥0∞ := ‖constantTerm F i ν (P : Set (characterLattice T))
    (normOneExtension hG (normOneWordDerivative At w (φ o))) (x : A)‖ₑ
  have hfm (P : J) (hP : P ∈ Idx) : Measurable (f P) :=
    ((measurable_constantTerm_normOneExtension_family hG hi hν (hP₀ P hP)
      (ψ := fun o => normOneWordDerivative At w (φ o)) hc hinv hmw).comp
      (measurable_id.prodMk measurable_const)).enorm
  have hpt (o : Ω) :
      ‖alternatingWordSystem (ν := ν) hG hi At R S n (φ o) w x‖ₑ ≤ ∑ P ∈ Idx, f P o := by
    simp only [alternatingWordSystem, hwn, ite_true, alternatingConstantTerm]
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun P _ => ?_)
    rw [enorm_mul]
    simp [f]
  have hterm (P : J) (hP : P ∈ Idx) :
      ∫⁻ o, f P o ∂mΩ ≤ ENNReal.ofReal (Efun P ^ n₀ * H x ^ n₀) * M := by
    refine (hbound P hP mΩ (fun o => normOneWordDerivative At w (φ o)) hc hinv hmw x).trans ?_
    refine iSup₂_le fun h hh => (hw (h * x)).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    rw [← mul_pow]
    refine pow_le_pow_left₀ (zero_le_one.trans (hH1 _)) ?_ _
    have hEf : Efun P = E P hP := dite_eq_left hP
    rw [hEf]
    exact (adelicHeight_mul_le F G rho hN (h : A) (x : A)).trans
      (mul_le_mul_of_nonneg_right (hEb P hP h hh) (zero_le_one.trans (hH1 _)))
  calc ∫⁻ o, ‖alternatingWordSystem (ν := ν) hG hi At R S n (φ o) w x‖ₑ ∂mΩ
      ≤ ∫⁻ o, ∑ P ∈ Idx, f P o ∂mΩ := lintegral_mono hpt
    _ = ∑ P ∈ Idx, ∫⁻ o, f P o ∂mΩ := lintegral_finsetSum _ hfm
    _ ≤ ∑ P ∈ Idx, ENNReal.ofReal (Efun P ^ n₀ * H x ^ n₀) * M := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ((∑ P ∈ Idx, Efun P ^ n₀) * H x ^ n₀) * M := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg, Finset.sum_mul]
        intro P _
        exact mul_nonneg (pow_nonneg (zero_le_one.trans (hEf1 P)) _)
          (pow_nonneg (zero_le_one.trans (hH1 _)) _)

end Langlands.Global.ArthurTruncation
