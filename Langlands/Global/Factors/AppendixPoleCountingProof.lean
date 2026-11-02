import Langlands.Global.Factors.AppendixPoleCountingStatement
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# Finite shifted-factor pole counting
-/

noncomputable section

namespace Langlands.Global.PoleComparison

universe u

theorem symmetricBlockShift (I : Type u) : SymmetricBlockShiftStatement I := by
  intro length exponent partner h hs hatt hmax
  obtain ⟨hinv, hlength, hexponent, hinterval⟩ := hs
  obtain ⟨a, ha⟩ := hatt
  have hpartner := hmax (partner a)
  have hnonneg : 0 ≤ h := by
    dsimp [blockHeight] at ha hpartner
    rw [hlength, hexponent] at hpartner
    have := Nat.cast_nonneg (α := ℝ) (length a)
    linarith
  refine ⟨hnonneg, ?_, a, ?_⟩
  · intro i j k hk
    have hki : (k : ℝ) ≤ length i := by
      exact_mod_cast hk.trans (min_le_left _ _)
    have hkj : (k : ℝ) ≤ length j := by
      exact_mod_cast hk.trans (min_le_right _ _)
    have hknonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hi := hmax i
    have hj := hmax (partner j)
    have hei := (hinterval i).1
    have hej := (hinterval j).2
    dsimp [blockHeight] at hi hj
    rw [hlength, hexponent] at hj
    dsimp [blockShift]
    constructor <;> linarith
  · dsimp [blockHeight] at ha
    dsimp [blockShift]
    rw [hlength, hexponent]
    norm_num
    linarith

private theorem shiftedBase_meromorphic {I : Type u}
    (length : I → ℕ) (exponent : I → ℝ) (partner : I → I)
    (base : I → I → ℂ → ℂ) (hb : BasePairConditions partner base)
    (i j : I) (k : ℕ) (t : ℝ) :
    MeromorphicAt (fun z => base i j
      (z + (blockShift length exponent i j k : ℂ))) (t : ℂ) := by
  rw [meromorphicAt_fun_comp_add_const_iff_meromorphicAt]
  simpa only [Complex.ofReal_add] using
    (hb.1 i j (t + blockShift length exponent i j k)).1

private theorem shiftedBase_order {I : Type u}
    (length : I → ℕ) (exponent : I → ℝ) (base : I → I → ℂ → ℂ)
    (i j : I) (k : ℕ) (t : ℝ) :
    meromorphicOrderAt (fun z => base i j
      (z + (blockShift length exponent i j k : ℂ))) (t : ℂ) =
      meromorphicOrderAt (base i j)
        ((t + blockShift length exponent i j k : ℝ) : ℂ) := by
  rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
  rw [Complex.ofReal_add]

private theorem blockLFactor_meromorphic {I : Type u} [Fintype I]
    (length : I → ℕ) (exponent : I → ℝ) (partner : I → I)
    (base : I → I → ℂ → ℂ) (hb : BasePairConditions partner base) (t : ℝ) :
    MeromorphicAt (blockLFactor length exponent base) (t : ℂ) := by
  classical
  apply MeromorphicAt.fun_prod
  intro i hi
  apply MeromorphicAt.fun_prod
  intro j hj
  apply MeromorphicAt.fun_prod
  intro k hk
  exact shiftedBase_meromorphic length exponent partner base hb i j k t

private theorem blockLFactor_order {I : Type u} [Fintype I]
    (length : I → ℕ) (exponent : I → ℝ) (partner : I → I)
    (base : I → I → ℂ → ℂ) (hb : BasePairConditions partner base) (t : ℝ) :
    meromorphicOrderAt (blockLFactor length exponent base) (t : ℂ) =
      ∑ i, ∑ j, ∑ k ∈ Finset.range (min (length i) (length j) + 1),
        meromorphicOrderAt (base i j)
          ((t + blockShift length exponent i j k : ℝ) : ℂ) := by
  classical
  unfold blockLFactor
  rw [meromorphicOrderAt_fun_prod (fun i hi =>
    MeromorphicAt.fun_prod (fun j hj => MeromorphicAt.fun_prod (fun k hk =>
      shiftedBase_meromorphic length exponent partner base hb i j k t)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [meromorphicOrderAt_fun_prod (fun j hj =>
    MeromorphicAt.fun_prod (fun k hk =>
      shiftedBase_meromorphic length exponent partner base hb i j k t))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [meromorphicOrderAt_fun_prod (fun k hk =>
    shiftedBase_meromorphic length exponent partner base hb i j k t)]
  apply Finset.sum_congr rfl
  intro k hk
  exact shiftedBase_order length exponent base i j k t

private theorem reflectedShiftedBase_unit {I : Type u}
    (length : I → ℕ) (exponent : I → ℝ) (partner : I → I)
    (base : I → I → ℂ → ℂ) (hb : BasePairConditions partner base)
    (i j : I) (k : ℕ) (t : ℝ)
    (hpos : 0 < 1 - t + blockShift length exponent i j k) :
    HolomorphicUnitAt (fun z => base i j
      (1 - z + (blockShift length exponent i j k : ℂ))) (t : ℂ) := by
  have hu := hb.2.1 i j (1 - t + blockShift length exponent i j k) hpos
  rw [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one] at hu
  refine ⟨?_, hu.2⟩
  have hf : AnalyticAt ℂ (fun z : ℂ =>
      1 - z + (blockShift length exponent i j k : ℂ)) (t : ℂ) :=
    (analyticAt_const.sub analyticAt_id).add analyticAt_const
  exact hu.1.comp_of_eq hf rfl

private theorem finiteSum_negative {A : Type*} (S : Finset A) (f : A → WithTop ℤ)
    (h : ∀ a ∈ S, f a ≤ 0) (a : A) (ha : a ∈ S) (hneg : f a < 0) :
    ∑ i ∈ S, f i < 0 := by
  classical
  calc
    ∑ i ∈ S, f i ≤ ∑ i ∈ ({a} : Finset A), f i :=
      Finset.sum_le_sum_of_subset_of_nonpos (Finset.singleton_subset_iff.mpr ha)
        (fun i hi _ => h i hi)
    _ = f a := Finset.sum_singleton _ _
    _ < 0 := hneg

theorem appendixExtremePole (I : Type u) [Fintype I] :
    AppendixExtremePoleStatement I := by
  classical
  intro length exponent partner base epsilon h hs hb heps hatt hmax
  obtain ⟨hnonneg, hshift, a, ha⟩ :=
    symmetricBlockShift I length exponent partner h hs hatt hmax
  have hpole :
      meromorphicOrderAt (blockLFactor length exponent base) ((-2 * h : ℝ) : ℂ) < 0 := by
    rw [blockLFactor_order length exponent partner base hb]
    apply finiteSum_negative _ _ (fun i hi =>
      Finset.sum_nonpos (fun j hj =>
        Finset.sum_nonpos (fun k hk => (hb.1 i j _).2))) a (Finset.mem_univ a)
    apply finiteSum_negative _ _ (fun j hj =>
      Finset.sum_nonpos (fun k hk => (hb.1 a j _).2)) (partner a) (Finset.mem_univ _)
    apply finiteSum_negative _ _ (fun k hk =>
      (hb.1 a (partner a) _).2) 0 (by simp)
    rw [ha]
    simpa only [show -2 * h + 2 * h = 0 by ring, Complex.ofReal_zero] using hb.2.2 a
  have hfactor : ∀ i j k, k ∈ Finset.range (min (length i) (length j) + 1) →
      HolomorphicUnitAt (fun z => base i j
        (1 - z + (blockShift length exponent i j k : ℂ))) ((-2 * h : ℝ) : ℂ) := by
    intro i j k hk
    have hk' : k ≤ min (length i) (length j) := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    apply reflectedShiftedBase_unit length exponent partner base hb i j k (-2 * h)
    have := (hshift i j k hk').1
    linarith
  have hreflected : HolomorphicUnitAt
      (fun z => blockLFactor length exponent base (1 - z)) ((-2 * h : ℝ) : ℂ) := by
    constructor
    · exact Finset.analyticAt_fun_prod Finset.univ (fun i hi =>
        Finset.analyticAt_fun_prod Finset.univ (fun j hj =>
          Finset.analyticAt_fun_prod _ (fun k hk => (hfactor i j k hk).1)))
    · apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact Finset.prod_ne_zero_iff.mpr (fun k hk => (hfactor i j k hk).2)
  refine ⟨hpole, hreflected, ?_⟩
  have he := heps (-2 * h)
  change 0 < meromorphicOrderAt
    ((epsilon * (fun z => blockLFactor length exponent base (1 - z))) *
      (blockLFactor length exponent base)⁻¹) ((-2 * h : ℝ) : ℂ)
  rw [meromorphicOrderAt_mul_of_ne_zero
    (he.1.mul hreflected.1) (mul_ne_zero he.2 hreflected.2), meromorphicOrderAt_inv]
  exact LinearOrderedAddCommGroupWithTop.neg_pos.mpr (Or.inl hpole)

theorem appendixBlockRigidity (I : Type u) [Fintype I] [Nonempty I] :
    AppendixBlockRigidityStatement I := by
  classical
  intro length exponent partner base epsilon hs hb heps hzero
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image Finset.univ
    (blockHeight length exponent) Finset.univ_nonempty
  have hmax' : ∀ i, blockHeight length exponent i ≤ blockHeight length exponent a :=
    fun i => hmax i (Finset.mem_univ i)
  have hextreme := appendixExtremePole I length exponent partner base epsilon
    (blockHeight length exponent a) hs hb heps ⟨a, rfl⟩ hmax'
  have hheight : blockHeight length exponent a = 0 := by
    have := hzero (-2 * blockHeight length exponent a) hextreme.2.2
    linarith
  intro i
  have hi := hmax' i
  have hj := hmax' (partner i)
  rw [hheight] at hi hj
  dsimp [blockHeight] at hi hj
  rw [hs.2.1, hs.2.2.1] at hj
  have hlength : (length i : ℝ) = 0 := by
    have := Nat.cast_nonneg (α := ℝ) (length i)
    linarith
  refine ⟨by exact_mod_cast hlength, ?_⟩
  rw [hlength] at hi hj
  linarith

theorem appendixPoleCounting (I : Type u) [Fintype I] [Nonempty I] :
    AppendixPoleCountingStatement I :=
  ⟨symmetricBlockShift I, appendixExtremePole I, appendixBlockRigidity I⟩

end Langlands.Global.PoleComparison
