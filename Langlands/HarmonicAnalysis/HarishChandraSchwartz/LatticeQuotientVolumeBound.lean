import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DoubleCosetIndexBoundsProof
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Lattice index bounds and full-center quotient volumes -/

noncomputable section

universe u v w

open MeasureTheory Topology
open scoped ENNReal BigOperators Pointwise

namespace Langlands.HarishChandraSchwartz

/-- Submultiplicativity bounds any finite natural lattice sum. -/
theorem doubleCosetIndex_lattice_sum
    {G : Type u} [Group G] (K : Subgroup G)
    {X : Type v} [AddCommGroup X] (e : Multiplicative X →* G)
    {I : Type w} [DecidableEq I] (s : Finset I)
    (x : I → X) (r : I → ℝ) (hr : ∀ a, 0 ≤ r a)
    (hx : ∀ a, doubleCosetIndex K (e (.ofAdd (x a))) ≠ 0 ∧
      (doubleCosetIndex K (e (.ofAdd (x a))) : ℝ) ≤ r a)
    (n : I → ℕ) :
    doubleCosetIndex K (e (.ofAdd (∑ a ∈ s, n a • x a))) ≠ 0 ∧
      (doubleCosetIndex K (e (.ofAdd (∑ a ∈ s, n a • x a))) : ℝ) ≤
        ∏ a ∈ s, r a ^ n a := by
  have hcalculus := doubleCosetIndexBounds.{u,u} G K
  induction s using Finset.induction_on with
  | empty =>
    have hc : conjSubgroup (1 : G) K = K := by
      ext y
      simp [mem_conjSubgroup]
    have h1 : doubleCosetIndex K (1 : G) = 1 := by
      rw [doubleCosetIndex, hc, Subgroup.relIndex_self]
    simpa [h1] using (show (1 : ℕ) ≠ 0 ∧ (1 : ℝ) ≤ 1 from ⟨one_ne_zero, le_rfl⟩)
  | @insert a s ha ih =>
    have hpow := hcalculus.2.1 _ (hx a).1 (n a)
    have hmul := hcalculus.1 _ _ hpow.1 ih.1
    have hmap : e (.ofAdd (∑ b ∈ insert a s, n b • x b)) =
        e (.ofAdd (x a)) ^ n a * e (.ofAdd (∑ b ∈ s, n b • x b)) := by
      rw [Finset.sum_insert ha, ofAdd_add, map_mul, ofAdd_nsmul, map_pow]
    rw [hmap, Finset.prod_insert ha]
    refine ⟨hmul.1, ?_⟩
    have hmulR : (doubleCosetIndex K
        (e (.ofAdd (x a)) ^ n a * e (.ofAdd (∑ b ∈ s, n b • x b))) : ℝ) ≤
        (doubleCosetIndex K (e (.ofAdd (x a)) ^ n a) : ℝ) *
          doubleCosetIndex K (e (.ofAdd (∑ b ∈ s, n b • x b))) := by
      exact_mod_cast hmul.2
    have hpowR0 : (doubleCosetIndex K (e (.ofAdd (x a)) ^ n a) : ℝ) ≤
        (doubleCosetIndex K (e (.ofAdd (x a))) : ℝ) ^ n a := by
      exact_mod_cast hpow.2
    have hpowR : (doubleCosetIndex K (e (.ofAdd (x a)) ^ n a) : ℝ) ≤ r a ^ n a :=
      hpowR0.trans (pow_le_pow_left₀ (by positivity) (hx a).2 _)
    exact hmulR.trans (mul_le_mul hpowR ih.2 (by positivity) (pow_nonneg (hr a) _))

section Topological

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An open subgroup has finite relative index in a compact subgroup. -/
theorem relIndex_ne_zero_of_open_compact (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    H.relIndex K ≠ 0 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have := Subgroup.quotient_finite_of_isOpen (H.subgroupOf K)
    (Subgroup.subgroupOf_isOpen K H hH)
  let : (H.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.FiniteIndex.index_ne_zero

/-- Compact open subgroups have finite conjugate-intersection indices. -/
theorem doubleCosetIndex_ne_zero_of_compact_open (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (g : G) :
    doubleCosetIndex K.toSubgroup g ≠ 0 := by
  apply relIndex_ne_zero_of_open_compact _ _ _ hK
  exact K.isOpen.preimage
    (show Continuous (fun x : G => g⁻¹ * x * g) by fun_prop)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The quotient map sends an actual double coset to the double coset of the
image subgroup. -/
theorem map_doubleCoset {H : Type v} [Group H] (f : G →* H)
    (K : Subgroup G) (g : G) :
    f '' DoubleCoset.doubleCoset g K K =
      DoubleCoset.doubleCoset (f g) (K.map f) (K.map f) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨f a, ⟨a, ha, rfl⟩, f b, ⟨b, hb, rfl⟩, by simp only [map_mul]⟩
  · intro hy
    obtain ⟨a', ⟨a, ha, rfl⟩, b', ⟨b, hb, rfl⟩, rfl⟩ :=
      DoubleCoset.mem_doubleCoset.mp hy
    exact ⟨a * g * b, DoubleCoset.mem_doubleCoset.mpr ⟨a, ha, b, hb, rfl⟩,
      by simp only [map_mul]⟩

/-- A common compact open subgroup and ray-index bounds give uniform upper
volumes of lattice cells in the actual full-center quotient. -/
theorem latticeCentralQuotientVolume
    (K L : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hL : IsCompact (L : Set G)) (hLK : L.toSubgroup ≤ K.toSubgroup)
    {X : Type v} [AddCommGroup X] (e : Multiplicative X →* G)
    {I : Type w} [Fintype I] [DecidableEq I]
    (x : I → X) (r : I → ℝ) (hr : ∀ a, 0 ≤ r a)
    (hx : ∀ a, doubleCosetIndex L.toSubgroup (e (.ofAdd (x a))) ≠ 0 ∧
      (doubleCosetIndex L.toSubgroup (e (.ofAdd (x a))) : ℝ) ≤ r a)
    (F₀ : Set G) (hF₀ : F₀.Finite)
    [MeasurableSpace (G ⧸ Subgroup.center G)]
    [BorelSpace (G ⧸ Subgroup.center G)]
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] :
    ∃ D : ℝ, 0 < D ∧ ∀ (n : I → ℕ) (t : G), t ∈ F₀ →
      MeasurableSet ((QuotientGroup.mk : G → G ⧸ Subgroup.center G) ''
        DoubleCoset.doubleCoset (e (.ofAdd (∑ a, n a • x a)) * t) K.toSubgroup K.toSubgroup) ∧
      μ ((QuotientGroup.mk : G → G ⧸ Subgroup.center G) ''
        DoubleCoset.doubleCoset (e (.ofAdd (∑ a, n a • x a)) * t) K.toSubgroup K.toSubgroup) ≤
          ENNReal.ofReal (D * ∏ a, r a ^ n a) := by
  classical
  let q : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' _
  let Kq : Subgroup (G ⧸ Subgroup.center G) := K.toSubgroup.map q
  have hKq : (Kq : Set (G ⧸ Subgroup.center G)) = q '' (K : Set G) := rfl
  have hKqo : IsOpen (Kq : Set (G ⧸ Subgroup.center G)) := by
    rw [hKq]
    exact QuotientGroup.isOpenMap_coe _ K.isOpen
  have hKqc : IsCompact (Kq : Set (G ⧸ Subgroup.center G)) := by
    rw [hKq]
    exact hK.image QuotientGroup.continuous_mk
  have hμK : μ Kq ≠ ⊤ := hKqc.measure_ne_top
  let C : ℕ := 1 + ∑ t ∈ hF₀.toFinset, doubleCosetIndex L.toSubgroup t
  let A : ℝ := (C : ℝ) * (L.toSubgroup.relIndex K.toSubgroup : ℝ) * (μ Kq).toReal
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A + 1, by positivity, ?_⟩
  intro n t ht
  let g := e (.ofAdd (∑ a, n a • x a)) * t
  have hsum := doubleCosetIndex_lattice_sum L.toSubgroup e Finset.univ x r hr hx n
  have htfin := doubleCosetIndex_ne_zero_of_compact_open L hL t
  have hmul := (doubleCosetIndexBounds.{u,u} G L.toSubgroup).1 _ _ hsum.1 htfin
  have hrel := relIndex_ne_zero_of_open_compact L.toSubgroup L.isOpen K.toSubgroup hK
  have henlarge := doubleCosetIndex_le hLK g hmul.1 hrel
  have hmap := (doubleCosetIndexBounds.{u,u} G K.toSubgroup).2.2
    (G ⧸ Subgroup.center G) q g henlarge.1
  have htC : doubleCosetIndex L.toSubgroup t ≤ C := by
    exact (Finset.single_le_sum (fun a _ => Nat.zero_le _) (hF₀.mem_toFinset.mpr ht)).trans
      (Nat.le_add_left _ _)
  have hindex : (doubleCosetIndex Kq (q g) : ℝ) ≤
      ((C : ℝ) * (L.toSubgroup.relIndex K.toSubgroup : ℝ)) * ∏ a, r a ^ n a := by
    have hmapR : (doubleCosetIndex Kq (q g) : ℝ) ≤
        (doubleCosetIndex K.toSubgroup g : ℝ) := by exact_mod_cast hmap.2
    have henlargeR : (doubleCosetIndex K.toSubgroup g : ℝ) ≤
        (doubleCosetIndex L.toSubgroup g : ℝ) *
          (L.toSubgroup.relIndex K.toSubgroup : ℝ) := by exact_mod_cast henlarge.2
    have hmulR : (doubleCosetIndex L.toSubgroup g : ℝ) ≤
        (doubleCosetIndex L.toSubgroup (e (.ofAdd (∑ a, n a • x a))) : ℝ) *
          (doubleCosetIndex L.toSubgroup t : ℝ) := by exact_mod_cast hmul.2
    have htCR : (doubleCosetIndex L.toSubgroup t : ℝ) ≤ C := by exact_mod_cast htC
    calc
      _ ≤ ((∏ a, r a ^ n a) * C) * (L.toSubgroup.relIndex K.toSubgroup : ℝ) :=
        hmapR.trans (henlargeR.trans (mul_le_mul_of_nonneg_right
          (hmulR.trans (mul_le_mul hsum.2 htCR (by positivity)
            (Finset.prod_nonneg fun a _ => pow_nonneg (hr a) _))) (by positivity)))
      _ = _ := by ring
  change MeasurableSet (q '' DoubleCoset.doubleCoset g K.toSubgroup K.toSubgroup) ∧
    μ (q '' DoubleCoset.doubleCoset g K.toSubgroup K.toSubgroup) ≤ _
  rw [map_doubleCoset]
  refine ⟨(hKqo.mul_right.mul_right).measurableSet, ?_⟩
  rw [measure_doubleCoset μ Kq hKqo.measurableSet (q g) hmap.1]
  calc
    (doubleCosetIndex Kq (q g) : ℝ≥0∞) * μ Kq =
        ENNReal.ofReal ((doubleCosetIndex Kq (q g) : ℝ) * (μ Kq).toReal) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_toReal hμK]
    _ ≤ ENNReal.ofReal ((A + 1) * ∏ a, r a ^ n a) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (((C : ℝ) * (L.toSubgroup.relIndex K.toSubgroup : ℝ)) *
            ∏ a, r a ^ n a) * (μ Kq).toReal :=
          mul_le_mul_of_nonneg_right hindex ENNReal.toReal_nonneg
        _ = A * ∏ a, r a ^ n a := by dsimp [A]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
          (Finset.prod_nonneg fun a _ => pow_nonneg (hr a) _)

end Topological

end Langlands.HarishChandraSchwartz
