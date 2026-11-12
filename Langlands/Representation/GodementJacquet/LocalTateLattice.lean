import Langlands.Representation.GodementJacquet.LocalTateConductorPreliminaries
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof

/-! # Orders, lattices and unit levels for scalar Tate theory over a local field -/

noncomputable section

namespace Langlands.GodementJacquet.LocalTate

open MeasureTheory HarmonicAnalysis Topology ValuativeRel
open GeneralLinear.Iwasawa
open scoped ENNReal NNReal

universe uF

/-- The normalization data of `LocalTateConductorStatement`: the residue
cardinality, a uniformizer and an absolute value normalized by them. -/
structure Normalization (F : Type uF) [Field F] [ValuativeRel F] where
  q : ℕ
  hq : q = Nat.card (IsLocalRing.ResidueField (valuation F).integer)
  abv : AbsoluteValue F ℝ
  ϖ : Fˣ
  hϖ : IsUniformizingElement (valuation F) ϖ
  habvϖ : abv (ϖ : F) = (q : ℝ)⁻¹
  habv1 : ∀ x : F, valuation F x = 1 → abv x = 1

namespace Normalization

variable {F : Type uF} [Field F] [ValuativeRel F] (N : Normalization F)

theorem valuation_ϖ_pos : 0 < valuation F (N.ϖ : F) :=
  GeneralLinear.Iwasawa.valuation_pos (valuation F) N.ϖ

theorem zpow_strictAnti : StrictAnti (fun k : ℤ => valuation F (N.ϖ : F) ^ k) :=
  zpow_right_strictAnti₀ N.valuation_ϖ_pos N.hϖ.1

/-- The order of a nonzero element with respect to the chosen uniformizer;
zero is sent to zero by convention. -/
def ord (x : F) : ℤ := by
  classical
  exact if h : x = 0 then 0 else Classical.choose (N.hϖ.2 x h)

theorem valuation_eq_zpow_ord {x : F} (hx : x ≠ 0) :
    valuation F x = valuation F (N.ϖ : F) ^ N.ord x := by
  classical
  simp only [ord, hx, ↓reduceDIte]
  exact Classical.choose_spec (N.hϖ.2 x hx)

theorem ord_eq_iff {x : F} (hx : x ≠ 0) {k : ℤ} :
    N.ord x = k ↔ valuation F x = valuation F (N.ϖ : F) ^ k := by
  constructor
  · rintro rfl
    exact N.valuation_eq_zpow_ord hx
  · intro h
    exact N.zpow_strictAnti.injective ((N.valuation_eq_zpow_ord hx).symm.trans h)

theorem ord_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    N.ord (x * y) = N.ord x + N.ord y := by
  rw [N.ord_eq_iff (mul_ne_zero hx hy), map_mul, N.valuation_eq_zpow_ord hx,
    N.valuation_eq_zpow_ord hy, zpow_add₀ N.valuation_ϖ_pos.ne']

theorem ord_zpow_ϖ (k : ℤ) : N.ord ((N.ϖ : F) ^ k) = k := by
  rw [N.ord_eq_iff (zpow_ne_zero _ N.ϖ.ne_zero), map_zpow₀]

theorem ord_ϖ : N.ord (N.ϖ : F) = 1 := by
  simpa using N.ord_zpow_ϖ 1

theorem ord_eq_zero_iff {x : F} (hx : x ≠ 0) : N.ord x = 0 ↔ valuation F x = 1 := by
  rw [N.ord_eq_iff hx, zpow_zero]

theorem ord_inv {x : F} (hx : x ≠ 0) : N.ord x⁻¹ = -N.ord x := by
  rw [N.ord_eq_iff (inv_ne_zero hx), map_inv₀, N.valuation_eq_zpow_ord hx, zpow_neg]

theorem abv_eq {x : F} (hx : x ≠ 0) : N.abv x = (N.q : ℝ) ^ (-N.ord x) := by
  set k := N.ord x
  have hϖk : ((N.ϖ : F) ^ k) ≠ 0 := zpow_ne_zero _ N.ϖ.ne_zero
  have hu : valuation F (x * ((N.ϖ : F) ^ k)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, map_zpow₀, N.valuation_eq_zpow_ord hx,
      mul_inv_cancel₀ (zpow_ne_zero _ N.valuation_ϖ_pos.ne')]
  have h1 := N.habv1 _ hu
  have hx' : x = (x * ((N.ϖ : F) ^ k)⁻¹) * (N.ϖ : F) ^ k := by
    rw [inv_mul_cancel_right₀ hϖk]
  rw [hx', map_mul, h1, one_mul, map_zpow₀, N.habvϖ, inv_zpow', zpow_neg]

theorem abv_ϖ_zpow (k : ℤ) : N.abv ((N.ϖ : F) ^ k) = (N.q : ℝ) ^ (-k) := by
  rw [N.abv_eq (zpow_ne_zero _ N.ϖ.ne_zero), N.ord_zpow_ϖ]

/-- The lattice `ϖ ^ n O`, as an additive subgroup. -/
def ball (n : ℤ) : AddSubgroup F where
  carrier := {x | valuation F x ≤ valuation F (N.ϖ : F) ^ n}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    change valuation F (x + y) ≤ _
    exact (Valuation.map_add _ x y).trans (max_le hx hy)
  neg_mem' {x} hx := by
    change valuation F (-x) ≤ _
    rw [Valuation.map_neg]
    exact hx

theorem mem_ball {n : ℤ} {x : F} :
    x ∈ N.ball n ↔ valuation F x ≤ valuation F (N.ϖ : F) ^ n := Iff.rfl

theorem mem_ball_iff_ord {n : ℤ} {x : F} (hx : x ≠ 0) : x ∈ N.ball n ↔ n ≤ N.ord x := by
  rw [mem_ball, N.valuation_eq_zpow_ord hx]
  exact N.zpow_strictAnti.le_iff_ge

theorem ball_zero_eq : (N.ball 0 : Set F) = (valuation F).integer := by
  ext x
  simp [mem_ball, Valuation.mem_integer_iff]

theorem mem_ball_zero {x : F} : x ∈ N.ball 0 ↔ x ∈ (valuation F).integer := by
  rw [← SetLike.mem_coe, N.ball_zero_eq, SetLike.mem_coe]

theorem ball_antitone {m n : ℤ} (h : m ≤ n) : N.ball n ≤ N.ball m := by
  intro x hx
  exact (N.mem_ball.mp hx).trans (N.zpow_strictAnti.antitone h)

theorem mul_mem_ball {m n : ℤ} {x y : F} (hx : x ∈ N.ball m) (hy : y ∈ N.ball n) :
    x * y ∈ N.ball (m + n) := by
  rw [mem_ball, map_mul, zpow_add₀ N.valuation_ϖ_pos.ne']
  exact mul_le_mul' hx hy

theorem units_mul_mem_ball_iff (a : Fˣ) {n : ℤ} {x : F} :
    (a : F) * x ∈ N.ball (n + N.ord a) ↔ x ∈ N.ball n := by
  rw [mem_ball, mem_ball, map_mul, N.valuation_eq_zpow_ord a.ne_zero,
    zpow_add₀ N.valuation_ϖ_pos.ne', mul_comm (valuation F (N.ϖ : F) ^ n)]
  exact mul_le_mul_iff_right₀ (zpow_pos N.valuation_ϖ_pos _)

theorem ϖ_zpow_mem_ball (k : ℤ) : (N.ϖ : F) ^ k ∈ N.ball k := by
  rw [mem_ball, map_zpow₀]

theorem not_mem_ball_succ {x : F} (hx : x ≠ 0) : x ∉ N.ball (N.ord x + 1) := by
  rw [N.mem_ball_iff_ord hx]
  omega

theorem mem_ball_ord {x : F} (hx : x ≠ 0) : x ∈ N.ball (N.ord x) := by
  rw [N.mem_ball_iff_ord hx]

theorem mem_ball_neg_iff_mul (n : ℤ) (y : F) :
    y ∈ N.ball (-n) ↔ (N.ϖ : F) ^ n * y ∈ N.ball 0 := by
  have h := N.units_mul_mem_ball_iff (N.ϖ ^ n) (n := -n) (x := y)
  rw [Units.val_zpow_eq_zpow_val, N.ord_zpow_ϖ, neg_add_cancel] at h
  exact h.symm

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem one_lt_q : 1 < N.q := by
  rw [N.hq]
  exact Finite.one_lt_card

theorem q_pos : 0 < N.q := lt_trans zero_lt_one N.one_lt_q

theorem ball_mem_nhds (n : ℤ) : (N.ball n : Set F) ∈ 𝓝 (0 : F) := by
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  refine ⟨Units.mk0 (valuation F (N.ϖ : F) ^ n) (zpow_ne_zero _ N.valuation_ϖ_pos.ne'), ?_⟩
  intro x hx
  have hx' : valuation F x < valuation F (N.ϖ : F) ^ n := by simpa using hx
  exact hx'.le

theorem isOpen_ball (n : ℤ) : IsOpen (N.ball n : Set F) :=
  AddSubgroup.isOpen_of_mem_nhds (N.ball n) (N.ball_mem_nhds n)

theorem isClosed_ball (n : ℤ) : IsClosed (N.ball n : Set F) :=
  AddSubgroup.isClosed_of_isOpen (N.ball n) (N.isOpen_ball n)

theorem isClopen_ball (n : ℤ) : IsClopen (N.ball n : Set F) :=
  ⟨N.isClosed_ball n, N.isOpen_ball n⟩

theorem isCompact_ball (n : ℤ) : IsCompact (N.ball n : Set F) :=
  IsNonarchimedeanLocalField.isCompact_closedBall F _

/-- The lattices `ϖ ^ n O` form a basis of neighbourhoods of zero. -/
theorem exists_ball_subset {s : Set F} (hs : s ∈ 𝓝 (0 : F)) :
    ∃ n : ℤ, (N.ball n : Set F) ⊆ s := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).mp hs
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero F)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact γ.ne_zero hy.symm
  refine ⟨N.ord y + 1, fun x hx => hγ ?_⟩
  change valuation F x < γ
  rw [← hy, N.valuation_eq_zpow_ord hy0]
  exact (N.mem_ball.mp hx).trans_lt (N.zpow_strictAnti (lt_add_one _))

/-- The set of nonzero elements of a fixed order is open. -/
theorem isOpen_ord_shell (k : ℤ) : IsOpen {x : F | x ≠ 0 ∧ N.ord x = k} := by
  have h : {x : F | x ≠ 0 ∧ N.ord x = k} = (N.ball k : Set F) \ (N.ball (k + 1) : Set F) := by
    ext x
    by_cases hx : x = 0
    · subst hx
      simp only [ne_eq, not_true_eq_false, false_and, Set.mem_ofPred_eq, Set.mem_sdiff,
        SetLike.mem_coe, zero_mem, not_true_eq_false, and_false]
    · simp only [ne_eq, hx, not_false_eq_true, true_and, Set.mem_ofPred_eq, Set.mem_sdiff,
        SetLike.mem_coe, N.mem_ball_iff_ord hx]
      omega
  rw [h]
  exact (N.isOpen_ball k).sdiff (N.isClosed_ball (k + 1))

/-- The order is locally constant on the unit group. -/
theorem isLocallyConstant_ord_units : IsLocallyConstant (fun x : Fˣ => N.ord (x : F)) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro k
  have h : (fun x : Fˣ => N.ord (x : F)) ⁻¹' {k} =
      Units.val ⁻¹' {x : F | x ≠ 0 ∧ N.ord x = k} := by
    ext x
    simp
  rw [h]
  exact (N.isOpen_ord_shell k).preimage Units.continuous_val

theorem continuous_ord_units : Continuous (fun x : Fˣ => N.ord (x : F)) :=
  N.isLocallyConstant_ord_units.continuous

end LocalField

end Normalization

section Indicators

variable {X : Type*} [TopologicalSpace X]

theorem isLocallyConstant_indicator_const {U : Set X} (hU : IsClopen U) (c : ℂ) :
    IsLocallyConstant (U.indicator (fun _ => c)) :=
  (LocallyConstant.indicator (LocallyConstant.const X c) hU).isLocallyConstant

/-- The indicator of a compact open set as a Schwartz--Bruhat function. -/
def indicatorSB {U : Set X} (hU : IsClopen U) (hK : IsCompact U) : SchwartzBruhat X :=
  ⟨U.indicator (fun _ => 1), isLocallyConstant_indicator_const hU 1,
    HasCompactSupport.intro' hK hU.isClosed (fun _ hx => Set.indicator_of_notMem hx _)⟩

@[simp] theorem indicatorSB_apply {U : Set X} (hU : IsClopen U) (hK : IsCompact U) (x : X) :
    indicatorSB hU hK x = U.indicator (fun _ => (1 : ℂ)) x := rfl

end Indicators

namespace Normalization

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : Normalization F)

theorem isClopen_coset (x0 : F) (n : ℤ) : IsClopen {x : F | x - x0 ∈ N.ball n} :=
  (N.isClopen_ball n).preimage (continuous_id.sub continuous_const)

theorem isCompact_coset (x0 : F) (n : ℤ) : IsCompact {x : F | x - x0 ∈ N.ball n} := by
  have h : {x : F | x - x0 ∈ N.ball n} = (fun y => y + x0) '' (N.ball n : Set F) := by
    ext x
    constructor
    · intro hx
      exact ⟨x - x0, hx, sub_add_cancel x x0⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [h]
  exact (N.isCompact_ball n).image (continuous_id.add continuous_const)

/-- The indicator of the coset `x0 + ϖ ^ n O`. -/
def cosetIndicator (x0 : F) (n : ℤ) : SchwartzBruhat F :=
  indicatorSB (N.isClopen_coset x0 n) (N.isCompact_coset x0 n)

theorem cosetIndicator_apply (x0 : F) (n : ℤ) (x : F) :
    N.cosetIndicator x0 n x = {x : F | x - x0 ∈ N.ball n}.indicator (fun _ => (1 : ℂ)) x :=
  rfl

/-- Every Schwartz--Bruhat function is invariant under one lattice. -/
theorem exists_ball_invariant (f : SchwartzBruhat F) :
    ∃ m : ℤ, ∀ x h : F, h ∈ N.ball m → f (x + h) = f x := by
  have hloc (x : F) : ∃ n : ℤ, ∀ d ∈ N.ball n, f (x + d) = f x := by
    have hs : {d : F | f (x + d) = f x} ∈ 𝓝 (0 : F) :=
      ((f.locallyConstant.isOpen_fiber (f x)).preimage
        (continuous_const.add continuous_id)).mem_nhds (by simp)
    obtain ⟨n, hn⟩ := N.exists_ball_subset hs
    exact ⟨n, fun d hd => hn hd⟩
  choose n hn using hloc
  have hK : IsCompact (tsupport (f : F → ℂ)) := f.hasCompactSupport.isCompact
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover
    (fun x => {z | z - x ∈ N.ball (n x)})
    (fun x _ => ((N.isOpen_ball (n x)).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simp))
  obtain ⟨M, hM⟩ := Finset.exists_le (t.image n)
  refine ⟨M, ?_⟩
  have hsupp : ∀ y ∈ tsupport (f : F → ℂ), ∀ h ∈ N.ball M, f (y + h) = f y := by
    intro y hy h hh
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (htK hy)
    have hyx : y - x ∈ N.ball (n x) := hyx
    have hle : n x ≤ M := hM _ (Finset.mem_image_of_mem _ hx)
    have hh' := N.ball_antitone hle hh
    have e1 := hn x (y - x) hyx
    have e2 := hn x (y + h - x) (by
      rw [show y + h - x = (y - x) + h by abel]
      exact (N.ball (n x)).add_mem hyx hh')
    rw [show x + (y - x) = y by abel] at e1
    rw [show x + (y + h - x) = y + h by abel] at e2
    rw [e1, e2]
  intro y h hh
  by_cases hy : y ∈ tsupport (f : F → ℂ)
  · exact hsupp y hy h hh
  by_cases hyh : y + h ∈ tsupport (f : F → ℂ)
  · have := hsupp (y + h) hyh (-h) (neg_mem hh)
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]

/-- Every Schwartz--Bruhat function is a finite linear combination of indicators
of cosets of one lattice. -/
theorem exists_coset_expansion (f : SchwartzBruhat F) :
    ∃ (m : ℤ) (S : Finset F), ∀ x : F,
      f x = ∑ x0 ∈ S, f x0 * N.cosetIndicator x0 m x := by
  classical
  obtain ⟨m, hm⟩ := N.exists_ball_invariant f
  let L := N.ball m
  have hK : IsCompact (tsupport (f : F → ℂ)) := f.hasCompactSupport.isCompact
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover (fun x => {z | z - x ∈ L})
    (fun x _ => ((N.isOpen_ball m).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simp))
  let S : Finset (F ⧸ L) := t.image (fun x : F => (QuotientAddGroup.mk x : F ⧸ L))
  refine ⟨m, S.image (fun c => c.out), ?_⟩
  intro x
  rw [Finset.sum_image (fun c _ d _ h => by
    rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' d]
    exact congrArg _ h)]
  have hmem (c : F ⧸ L) : x - c.out ∈ L ↔ (x : F ⧸ L) = c := by
    conv_rhs => rw [← QuotientAddGroup.out_eq' c]
    exact QuotientAddGroup.eq_iff_sub_mem.symm
  have hval : f (x : F ⧸ L).out = f x := by
    have h2 := hm (x : F ⧸ L).out _ ((hmem _).mpr rfl)
    rw [show (x : F ⧸ L).out + (x - (x : F ⧸ L).out) = x by abel] at h2
    exact h2.symm
  have hterm (c : F ⧸ L) :
      f c.out * N.cosetIndicator c.out m x = if (x : F ⧸ L) = c then f c.out else 0 := by
    rw [cosetIndicator_apply]
    by_cases hc : (x : F ⧸ L) = c
    · have : x ∈ {z : F | z - c.out ∈ N.ball m} := (hmem c).mpr hc
      rw [Set.indicator_of_mem this, mul_one, if_pos hc]
    · have : x ∉ {z : F | z - c.out ∈ N.ball m} := fun h => hc ((hmem c).mp h)
      rw [Set.indicator_of_notMem this, mul_zero, if_neg hc]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq]
  split_ifs with hS
  · exact hval.symm
  · apply image_eq_zero_of_notMem_tsupport
    intro hx
    apply hS
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (htK hx)
    have hxy : x - y ∈ L := hxy
    exact Finset.mem_image.mpr ⟨y, hy, (QuotientAddGroup.eq_iff_sub_mem.mpr hxy).symm⟩

/-- An induction principle: a property of Schwartz--Bruhat functions stable
under zero, sums and scalars which holds for all lattice-coset indicators holds
for every Schwartz--Bruhat function. -/
theorem schwartzBruhat_induction {p : SchwartzBruhat F → Prop} (hzero : p 0)
    (hadd : ∀ f g, p f → p g → p (f + g)) (hsmul : ∀ (c : ℂ) f, p f → p (c • f))
    (hcoset : ∀ (x0 : F) (n : ℤ), p (N.cosetIndicator x0 n)) (f : SchwartzBruhat F) :
    p f := by
  obtain ⟨m, S, hS⟩ := N.exists_coset_expansion f
  have hf : f = ∑ x0 ∈ S, f x0 • N.cosetIndicator x0 m := by
    apply Subtype.ext
    funext x
    rw [hS x, Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [hf]
  exact Finset.sum_induction _ p hadd hzero (fun x0 _ => hsmul _ _ (hcoset x0 m))

section Measure

variable [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]

theorem measurableSet_ball (n : ℤ) : MeasurableSet (N.ball n : Set F) :=
  (N.isOpen_ball n).measurableSet

theorem measure_ball_pos (n : ℤ) : 0 < ν (N.ball n) :=
  (N.isOpen_ball n).measure_pos ν ⟨0, zero_mem _⟩

theorem measure_ball_lt_top (n : ℤ) : ν (N.ball n) < ∞ :=
  (N.isCompact_ball n).measure_lt_top

/-- Scaling of the lattice measures: `ν (ϖ ^ n O) = q ^ (-n) ν O`. -/
theorem measure_ball (n : ℤ) :
    (ν (N.ball n)).toReal = (N.q : ℝ) ^ (-n) * (ν (N.ball 0)).toReal := by
  have hscale := HarmonicAnalysis.generalScalarHaarScalingStatement F N.q N.hq N.abv N.ϖ N.hϖ
    N.habvϖ N.habv1 ν (N.ϖ ^ (-n))
  have hpre : (fun x : F => ((N.ϖ ^ (-n) : Fˣ) : F) * x) ⁻¹' (N.ball 0 : Set F) =
      (N.ball n : Set F) := by
    ext x
    have h := N.units_mul_mem_ball_iff (N.ϖ ^ (-n)) (n := n) (x := x)
    rw [Units.val_zpow_eq_zpow_val, N.ord_zpow_ϖ, add_neg_cancel] at h
    simpa [Units.val_zpow_eq_zpow_val] using h
  have happ := congrArg (fun μ : Measure F => μ (N.ball 0 : Set F)) hscale
  rw [Measure.map_apply (measurable_const_mul _) (N.measurableSet_ball 0), hpre,
    Measure.smul_apply] at happ
  rw [happ, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul]
  congr 1
  have habs : ((Shahidi.absUnits N.abv (N.ϖ ^ (-n)) : ℝ≥0) : ℝ) =
      (N.q : ℝ) ^ n := by
    change N.abv ((N.ϖ ^ (-n) : Fˣ) : F) = _
    rw [Units.val_zpow_eq_zpow_val, N.abv_ϖ_zpow, neg_neg]
  rw [ENNReal.coe_toReal, NNReal.coe_inv, habs, ← zpow_neg]

end Measure

end Normalization

end Langlands.GodementJacquet.LocalTate
