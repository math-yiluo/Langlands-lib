import Langlands.Representation.RankinSelberg.UnequalRankMirabolicUnitTestStatement
import Langlands.Representation.Whittaker.MirabolicUnitTestProof
import Langlands.Representation.Whittaker.MirabolicUnitTestCompatibility
import Langlands.Analysis.Local.QuotientMass
import Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-!
# Compact mirabolic unit tests for every unequal-rank JPSS block: proof

One positive principal congruence level `a` is used in both ranks. The larger
test is the coset extension of the standard character from the level-`a`
principal congruence subgroup of the mirabolic group. A Schur-complement
computation shows that the block matrix `diag(g, I) (1 + X)` lies in its
support exactly when `g` lies in `N K(a)` and the rectangular entries lie in
`𝔪^a`. A rescaled actual coefficient function of a vector fixed by `K(a)`
then makes the integrand a constant multiple of the indicator of a compact
open quotient orbit times a compact open rectangle.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Topology

universe uF uW

namespace UnequalRankMirabolicUnitTest

section Algebra

variable {F : Type uF} [Field F] [ValuativeRel F]

/-- The image in the field of the ideal `𝔪^a` of the valuation integers. -/
def levelSet (F : Type uF) [Field F] [ValuativeRel F] (a : ℕ) : Set F :=
  {z | ∃ y : (ValuativeRel.valuation F).integer,
    y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ a ∧ (y : F) = z}

theorem zero_mem_levelSet (a : ℕ) : (0 : F) ∈ levelSet F a :=
  ⟨0, Ideal.zero_mem _, rfl⟩

theorem add_mem_levelSet {a : ℕ} {z w : F} (hz : z ∈ levelSet F a)
    (hw : w ∈ levelSet F a) : z + w ∈ levelSet F a := by
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨y', hy', rfl⟩ := hw
  exact ⟨y + y', Ideal.add_mem _ hy hy', by push_cast; rfl⟩

theorem neg_mem_levelSet {a : ℕ} {z : F} (hz : z ∈ levelSet F a) :
    -z ∈ levelSet F a := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨-y, neg_mem hy, by push_cast; rfl⟩

theorem mul_mem_levelSet {a : ℕ} {z o : F} (hz : z ∈ levelSet F a)
    (ho : o ∈ (ValuativeRel.valuation F).integer) : z * o ∈ levelSet F a := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨y * ⟨o, ho⟩, Ideal.mul_mem_right _ _ hy, by push_cast; rfl⟩

theorem sum_mem_levelSet {a : ℕ} {ι : Type*} (s : Finset ι) {f : ι → F}
    (hf : ∀ i ∈ s, f i ∈ levelSet F a) : ∑ i ∈ s, f i ∈ levelSet F a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_levelSet (F := F) a
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add_mem_levelSet (hf i (Finset.mem_insert_self i s))
      (ih fun l hl => hf l (Finset.mem_insert_of_mem hl))

/-- `levelSet F a` is the image of `𝔪^a` under the inclusion of the integers. -/
theorem levelSet_eq_image (a : ℕ) :
    levelSet F a = Subtype.val ''
      ((IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ a :
        Ideal (ValuativeRel.valuation F).integer) : Set (ValuativeRel.valuation F).integer) :=
  rfl

theorem mem_integer_of_mem_levelSet {a : ℕ} {z : F} (hz : z ∈ levelSet F a) :
    z ∈ (ValuativeRel.valuation F).integer := by
  obtain ⟨y, -, rfl⟩ := hz
  exact y.property

/-- An entry congruent to an identity entry modulo `𝔪^a` is integral. -/
theorem mem_integer_of_sub_one_mem_levelSet {a m : ℕ} {z : F}
    {i l : Fin (m + 1)}
    (hz : z - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i l ∈ levelSet F a) :
    z ∈ (ValuativeRel.valuation F).integer := by
  have h := add_mem (mem_integer_of_mem_levelSet hz)
    (Conductor.one_apply_mem_subring (ValuativeRel.valuation F).integer m i l)
  simpa using h

/-- Membership in the principal level subgroup, in terms of `levelSet`. -/
theorem mem_principalLevelSubgroup_iff {m a : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin (m + 1)) F) :
    g ∈ Conductor.principalLevelSubgroup F m a ↔
      (∀ i l, g i l - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i l ∈ levelSet F a) ∧
      (∀ i l, g⁻¹ i l - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i l ∈
        levelSet F a) :=
  Conductor.mem_principalCongruenceSubgroup_iff _ m _ g

/-- A matrix congruent to the identity modulo a positive power of the maximal
ideal is an element of the corresponding principal congruence subgroup. Only
the entries of the matrix itself are assumed; invertibility follows from the
determinant being a unit of the local ring of integers. -/
theorem exists_mem_principalLevelSubgroup {m a : ℕ} (ha : 0 < a)
    (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (hY : ∀ i l, Y i l - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i l ∈ levelSet F a) :
    ∃ E ∈ Conductor.principalLevelSubgroup F m a,
      (E : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Y := by
  classical
  set O := (ValuativeRel.valuation F).integer
  set I : Ideal O := IsLocalRing.maximalIdeal O ^ a
  choose y hyI hy using hY
  let Z : Matrix (Fin (m + 1)) (Fin (m + 1)) O := fun i l =>
    y i l + (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) O) i l
  have hZ : ∀ i l, Z i l - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) O) i l ∈ I := by
    intro i l
    simpa [Z] using hyI i l
  have hZY : ∀ i l, ((Z i l : O) : F) = Y i l := by
    intro i l
    simp only [Z]
    push_cast
    rw [hy i l, Conductor.subring_coe_one_apply]
    ring
  have hdet : Z.det - 1 ∈ I := by
    have h1 : (Ideal.Quotient.mk I).mapMatrix Z = 1 := by
      ext i l
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← map_one (Ideal.Quotient.mk I).mapMatrix,
        RingHom.mapMatrix_apply, Matrix.map_apply]
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 (hZ i l)
    have h2 := RingHom.map_det (Ideal.Quotient.mk I) Z
    rw [h1, Matrix.det_one, ← map_one (Ideal.Quotient.mk I)] at h2
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 h2
  have hunit : IsUnit Z.det := by
    have hle : I ≤ IsLocalRing.maximalIdeal O := Ideal.pow_le_self ha.ne'
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hm
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      simpa using Ideal.sub_mem _ hm (hle hdet)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
      ((Ideal.eq_top_iff_one _).2 h1)
  let Zu : Matrix.GeneralLinearGroup (Fin (m + 1)) O :=
    ((Matrix.isUnit_iff_isUnit_det Z).2 hunit).unit
  refine ⟨Matrix.GeneralLinearGroup.map O.subtype Zu, ?_, ?_⟩
  · exact (Conductor.map_mem_principalCongruenceSubgroup O m I Zu).2
      ((Conductor.mem_integralPrincipalCongruence m I Zu).2 hZ)
  · ext i l
    exact hZY i l

end Algebra

section Blocks

variable {F : Type uF} [Field F] [ValuativeRel F] {n j k a : ℕ}

/-- A sum over a longer initial segment whose terms vanish from index `t` on
is the sum over `Fin t`. -/
theorem sum_dite_lt {M : Type*} [AddCommMonoid M] {N t : ℕ} (h : t ≤ N)
    (f : Fin t → M) :
    ∑ m : Fin N, (if hm : m.val < t then f ⟨m.val, hm⟩ else 0) = ∑ m : Fin t, f m := by
  let f' : ℕ → M := fun m => if hm : m < t then f ⟨m, hm⟩ else 0
  have h3 : ∑ m : Fin t, f m = ∑ m : Fin t, f' m :=
    Finset.sum_congr rfl fun m _ => by simp [f', m.isLt]
  change ∑ m : Fin N, f' m = _
  rw [h3, Fin.sum_univ_eq_sum_range f' N, Fin.sum_univ_eq_sum_range f' t]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 h) fun m _ hm => ?_
  simp only [Finset.mem_range] at hm
  simp [f', hm]

omit [ValuativeRel F] in
/-- The leading rows of the block matrix are `[g, 0, 0]`. -/
theorem unequalRankMatrix_apply_top (g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin j) (Fin (n + 1)) F) (i l : Fin (n + (j + k + 1) + 1))
    (hi : i.val < n + 1) :
    (unequalRankMatrix j k g x).val i l =
      if hl : l.val < n + 1 then g ⟨i.val, hi⟩ ⟨l.val, hl⟩ else 0 := by
  have hr : ¬ (n + 1 ≤ i.val ∧ i.val < n + 1 + j) := by omega
  rw [unequalRankMatrix_val, Matrix.add_apply, appendIdentity_entry, dite_eq_left hi]
  simp only [rectangularEntries, dite_eq_right hr, add_zero]

omit [ValuativeRel F] in
/-- The rectangular rows of the block matrix are `[x, I_j, 0]`. -/
theorem unequalRankMatrix_apply_mid (g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin j) (Fin (n + 1)) F) (i : Fin (n + (j + k + 1) + 1)) (p : Fin j)
    (hip : i.val = n + 1 + p.val) (l : Fin (n + (j + k + 1) + 1)) :
    (unequalRankMatrix j k g x).val i l =
      (if hl : l.val < n + 1 then x p ⟨l.val, hl⟩ else 0) + if i = l then 1 else 0 := by
  have hi : ¬ i.val < n + 1 := by omega
  have hr : n + 1 ≤ i.val ∧ i.val < n + 1 + j := by omega
  rw [unequalRankMatrix_val, Matrix.add_apply, appendIdentity_entry, dite_eq_right hi, add_comm]
  congr 1
  simp only [rectangularEntries, dite_eq_left hr]
  split_ifs with hl
  · congr 1
    exact Fin.ext (by dsimp only; omega)
  · rfl

/-- On principal level-`a` matrices and rectangular entries in `𝔪^a`, the
block matrix lies in the principal level-`a` subgroup of the mirabolic group. -/
theorem unequalRankMatrix_mem (ha : 0 < a) {g : Langlands.GeneralLinear (n + 1) F}
    (hg : g ∈ Conductor.principalLevelSubgroup F n a)
    {x : Matrix (Fin j) (Fin (n + 1)) F} (hx : ∀ p l, x p l ∈ levelSet F a) :
    unequalRankMatrix j k g x ∈ Conductor.principalLevelSubgroup F (n + (j + k + 1)) a ⊓
      GeneralLinear.mirabolic (n + (j + k + 1)) F := by
  have hg' := ((mem_principalLevelSubgroup_iff g).1 hg).1
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · suffices hY : ∀ i l, (unequalRankMatrix j k g x).val i l -
        (1 : Matrix (Fin (n + (j + k + 1) + 1)) (Fin (n + (j + k + 1) + 1)) F) i l ∈
          levelSet F a by
      obtain ⟨E, hE, hEv⟩ := exists_mem_principalLevelSubgroup (m := n + (j + k + 1)) ha _ hY
      rwa [show E = unequalRankMatrix j k g x from Units.ext hEv] at hE
    intro i l
    by_cases hi : i.val < n + 1
    · rw [unequalRankMatrix_apply_top g x i l hi]
      by_cases hl : l.val < n + 1
      · rw [dite_eq_left hl]
        have h1 := hg' ⟨i.val, hi⟩ ⟨l.val, hl⟩
        have h2 : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) ⟨i.val, hi⟩ ⟨l.val, hl⟩ =
            (1 : Matrix (Fin (n + (j + k + 1) + 1)) (Fin (n + (j + k + 1) + 1)) F) i l := by
          simp only [Matrix.one_apply, Fin.ext_iff]
        rwa [h2] at h1
      · have hil : i ≠ l := fun h => hl (h ▸ hi)
        rw [dite_eq_right hl, Matrix.one_apply_ne hil, sub_zero]
        exact zero_mem_levelSet a
    · rw [unequalRankMatrix_val, Matrix.add_apply, appendIdentity_entry, dite_eq_right hi]
      by_cases hl : l.val < n + 1
      · have hil : i ≠ l := fun h => hi (h ▸ hl)
        rw [ite_eq_right hil, Matrix.one_apply_ne hil, zero_add, sub_zero]
        unfold rectangularEntries
        split_ifs
        all_goals first | exact hx _ _ | exact zero_mem_levelSet a
      · have hr : rectangularEntries j k x i l = 0 := by
          simp [rectangularEntries, hl]
        rw [hr, add_zero, Matrix.one_apply, sub_self]
        exact zero_mem_levelSet a
  · intro l
    have hi : ¬ (Fin.last (n + (j + k + 1))).val < n + 1 := by
      simp only [Fin.val_last]
      omega
    have hr : ¬ (n + 1 ≤ (Fin.last (n + (j + k + 1))).val ∧
        (Fin.last (n + (j + k + 1))).val < n + 1 + j) := by
      simp only [Fin.val_last]
      omega
    rw [unequalRankMatrix_val, Matrix.add_apply, appendIdentity_entry, dite_eq_right hi]
    simp only [rectangularEntries, dite_eq_right hr, add_zero]
    by_cases hl : l = Fin.last _
    · simp [hl]
    · rw [ite_eq_right (Ne.symm hl), ite_eq_right hl]

/-- If the block matrix lies in `N K(a)` for the larger rank, then `g` lies in
`N K(a)` for the smaller rank and every rectangular entry lies in `𝔪^a`.
With `e = h⁻¹`, the identity `M e = u` gives `g E = u₁₁` on the leading block
and `x E = -e₂₁` on the rectangular rows, where `E` is the leading block of `e`. -/
theorem exists_of_unequalRankMatrix_eq (ha : 0 < a) {g : Langlands.GeneralLinear (n + 1) F}
    {x : Matrix (Fin j) (Fin (n + 1)) F} (u : upperUnipotent (n + (j + k + 1) + 1) F)
    {h : Langlands.GeneralLinear (n + (j + k + 1) + 1) F}
    (hh : h ∈ Conductor.principalLevelSubgroup F (n + (j + k + 1)) a)
    (hgx : unequalRankMatrix j k g x = u.val * h) :
    (∃ c ∈ Conductor.principalLevelSubgroup F n a, g * c⁻¹ ∈ upperUnipotent (n + 1) F) ∧
      ∀ p l, x p l ∈ levelSet F a := by
  classical
  set M := unequalRankMatrix j k g x with hM
  set e := h⁻¹ with he_def
  have he : e ∈ Conductor.principalLevelSubgroup F (n + (j + k + 1)) a := inv_mem hh
  have he' := ((mem_principalLevelSubgroup_iff e).1 he).1
  have hMe : M * e = u.val := by rw [hgx, he_def, mul_inv_cancel_right]
  have hMe' : ∀ i l, ∑ m, M.val i m * e.val m l = u.val.val i l := by
    intro i l
    rw [← hMe]
    rfl
  let emb : Fin (n + 1) → Fin (n + (j + k + 1) + 1) := fun i => ⟨i.val, by omega⟩
  obtain ⟨E, hE, hEv⟩ := exists_mem_principalLevelSubgroup (m := n) ha
      (fun i l => e.val (emb i) (emb l)) (by
    intro i l
    have h1 := he' (emb i) (emb l)
    have h2 : (1 : Matrix (Fin (n + (j + k + 1) + 1)) (Fin (n + (j + k + 1) + 1)) F)
        (emb i) (emb l) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i l := by
      simp only [Matrix.one_apply, emb, Fin.ext_iff]
    rwa [h2] at h1)
  have htop : ∀ i l : Fin (n + 1), (g * E).val i l = u.val.val (emb i) (emb l) := by
    intro i l
    rw [← hMe']
    have hterm : ∀ m, M.val (emb i) m * e.val m (emb l) =
        if hm : m.val < n + 1 then g i ⟨m.val, hm⟩ * e.val (emb ⟨m.val, hm⟩) (emb l)
        else 0 := by
      intro m
      rw [hM, unequalRankMatrix_apply_top g x (emb i) m i.isLt]
      split_ifs with hm
      · rfl
      · exact zero_mul _
    rw [Finset.sum_congr rfl fun m _ => hterm m]
    refine Eq.trans ?_ (sum_dite_lt (N := n + (j + k + 1) + 1) (t := n + 1) (by omega)
      (fun m => g i m * e.val (emb m) (emb l))).symm
    change (g.val * E.val) i l = _
    rw [Matrix.mul_apply, hEv]
  have hgE : g * E ∈ upperUnipotent (n + 1) F := by
    refine ⟨fun i l hli => ?_, fun i => ?_⟩
    · rw [htop]
      exact UpperUnipotent.entry_eq_zero u (i := emb i) (j := emb l) hli
    · change (g * E).val i i = 1
      rw [htop]
      exact UpperUnipotent.entry_diag u (emb i)
  have hEinv := ((mem_principalLevelSubgroup_iff E).1 hE).2
  have hmid : ∀ (p : Fin j) (l : Fin (n + 1)),
      (x * E.val) p l = -e.val ⟨n + 1 + p.val, by omega⟩ (emb l) := by
    intro p l
    set ip : Fin (n + (j + k + 1) + 1) := ⟨n + 1 + p.val, by omega⟩ with hip
    have hlt : emb l < ip := by
      rw [Fin.lt_def]
      dsimp only [emb, ip]
      omega
    have h0 : u.val.val ip (emb l) = 0 := UpperUnipotent.entry_eq_zero u hlt
    rw [← hMe'] at h0
    have hterm : ∀ m, M.val ip m * e.val m (emb l) =
        (if hm : m.val < n + 1 then x p ⟨m.val, hm⟩ * e.val (emb ⟨m.val, hm⟩) (emb l)
          else 0) + if ip = m then e.val m (emb l) else 0 := by
      intro m
      rw [hM, unequalRankMatrix_apply_mid g x ip p rfl m, add_mul]
      congr 1
      · split_ifs
        · rfl
        · exact zero_mul _
      · split_ifs
        · exact one_mul _
        · exact zero_mul _
    rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_add_distrib,
      sum_dite_lt (N := n + (j + k + 1) + 1) (t := n + 1) (by omega)
        (fun m => x p m * e.val (emb m) (emb l)), Finset.sum_ite_eq] at h0
    simp only [Finset.mem_univ, ite_true] at h0
    rw [Matrix.mul_apply, hEv]
    exact eq_neg_of_add_eq_zero_left h0
  have hxE : x = (x * E.val) * (E⁻¹).val := by
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  refine ⟨⟨E⁻¹, inv_mem hE, by rwa [inv_inv]⟩, fun p l => ?_⟩
  rw [hxE, Matrix.mul_apply]
  refine sum_mem_levelSet _ fun m _ => ?_
  rw [hmid p m]
  refine mul_mem_levelSet (neg_mem_levelSet ?_) (mem_integer_of_sub_one_mem_levelSet (hEinv m l))
  have hm := m.isLt
  have h1 := he' ⟨n + 1 + p.val, by omega⟩ (emb m)
  rwa [Matrix.one_apply_ne (by simp only [ne_eq, Fin.ext_iff, emb]; omega), sub_zero] at h1

end Blocks

section Measure

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F]

/-- The level set is open in the field. -/
theorem isOpen_levelSet (a : ℕ) : IsOpen (levelSet F a) := by
  rw [levelSet_eq_image]
  exact (Valuation.isOpen_integer (v := ValuativeRel.valuation F)).isOpenMap_subtype_val _
    (IsLocalRing.isOpen_maximalIdeal_pow (ValuativeRel.valuation F).integer a)

/-- The level set is compact in the field. -/
theorem isCompact_levelSet (a : ℕ) : IsCompact (levelSet F a) := by
  rw [levelSet_eq_image]
  have hI := IsLocalRing.isOpen_maximalIdeal_pow (ValuativeRel.valuation F).integer a
  exact ((IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ a).toAddSubgroup
    |>.isClosed_of_isOpen hI).isCompact.image continuous_subtype_val

end Measure

section Rectangular

variable {F : Type uF} [AddGroup F] [TopologicalSpace F] [MeasurableSpace F]

omit [AddGroup F] [TopologicalSpace F] [MeasurableSpace F] in
/-- Matrices with every entry in `S`, as a product set. -/
theorem entries_eq_pi (j t : ℕ) (S : Set F) :
    {x : Matrix (Fin j) (Fin t) F | ∀ a b, x a b ∈ S} =
      (Set.univ.pi (fun _ : Fin j => Set.univ.pi (fun _ : Fin t => S)) :
        Set (Fin j → Fin t → F)) := by
  ext x
  change (∀ a b, x a b ∈ S) ↔ (∀ a ∈ Set.univ, ∀ b ∈ Set.univ, x a b ∈ S)
  simp

omit [AddGroup F] [TopologicalSpace F] in
/-- Matrices with every entry in a measurable set form a measurable set. -/
theorem measurableSet_entries {j t : ℕ} {S : Set F} (hS : MeasurableSet S) :
    MeasurableSet {x : Matrix (Fin j) (Fin t) F | ∀ a b, x a b ∈ S} := by
  rw [entries_eq_pi]
  exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => hS

/-- The rectangular product measure of the matrices with all entries in `S`.
For `j = 0` the right side is `1`, the unit mass of the zero-row variable. -/
theorem rectangularMeasure_entries (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure]
    (j t : ℕ) (S : Set F) :
    rectangularMeasure ν j t {x | ∀ a b, x a b ∈ S} = (ν.measure S ^ t) ^ j := by
  rw [entries_eq_pi]
  change (Measure.pi (fun _ : Fin j => Measure.pi (fun _ : Fin t => ν.measure)) :
    Measure (Fin j → Fin t → F)) (Set.univ.pi (fun _ : Fin j =>
      Set.univ.pi (fun _ : Fin t => S))) = _
  simp only [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Rectangular

end UnequalRankMirabolicUnitTest

open UnequalRankMirabolicUnitTest in
/-- Every unequal-rank JPSS block admits a compact mirabolic test function and
an actual smaller coefficient-model vector whose product integral converges and
equals one for every complex parameter. -/
theorem unequalRankMirabolicUnitTest {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n j k : ℕ) :
    UnequalRankMirabolicUnitTestStatement.{uF, uW} F T n j k := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : MeasurableSpace F.Carrier := borel _
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
  have : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
  have : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  have : SigmaCompactSpace F.Carrier := T.sigmaCompactSpace
  intro ψ _ μ hμ ν W _ _ σ hσ ℓ' hℓ'
  -- A vector with nonzero functional value and an open subgroup fixing it.
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hℓ'
  rw [LinearMap.zero_apply] at hw
  obtain ⟨Kw, hKw⟩ := hσ.1.1 w
  have hfix : ∀ g ∈ Kw, σ g w = w := fun g hg =>
    (Representation.mem_invariants _ w).1 hKw ⟨g, hg⟩
  -- A level for the smaller rank: inside `Kw` and the determinant-norm kernel.
  have hU₁ : (Kw : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∩
      ((T.determinantNorm (n + 1)).ker : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∈
        𝓝 (1 : Langlands.GeneralLinear (n + 1) F.Carrier) :=
    Filter.inter_mem (Kw.isOpen.mem_nhds Kw.one_mem)
      ((T.isOpen_ker_determinantNorm (n + 1)).mem_nhds (one_mem _))
  obtain ⟨a₁, ha₁, hK₁⟩ :=
    Conductor.exists_pos_principalLevelOpenSubgroup_subset F.Carrier n hU₁
  -- A level for the larger rank: inside the kernel of the standard character.
  have hker : IsOpen ((standardCharacter ψ (n + (j + k + 1))).ker :
      Set (upperUnipotent (n + (j + k + 1) + 1) F.Carrier)) := by
    let := T.upperUnipotentNonarchimedean (n + (j + k + 1) + 1)
    exact isOpen_ker_of_continuous_complex_character _
      (standardCharacterContinuous ψ (n + (j + k + 1))).continuous
  have hN₁ := hker.mem_nhds (standardCharacter ψ (n + (j + k + 1))).ker.one_mem
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hN₁
  obtain ⟨O, hO, hOK⟩ := hN₁
  obtain ⟨a₂, -, hK₂⟩ :=
    Conductor.exists_pos_principalLevelOpenSubgroup_subset F.Carrier (n + (j + k + 1)) hO
  obtain ⟨a, ha₁a, ha₂a, ha⟩ : ∃ a, a₁ ≤ a ∧ a₂ ≤ a ∧ 0 < a :=
    ⟨max a₁ a₂, le_max_left _ _, le_max_right _ _, lt_max_of_lt_left ha₁⟩
  have hKt : ∀ c ∈ Conductor.principalLevelSubgroup F.Carrier n a,
      c ∈ Kw ∧ T.determinantNorm (n + 1) c = 1 := by
    intro c hc
    have h := hK₁ (Conductor.principalLevelSubgroup_antitone F.Carrier n ha₁a hc)
    exact ⟨h.1, MonoidHom.mem_ker.mp h.2⟩
  -- The larger test: the standard character on `N`-cosets of `H`, extended by zero.
  let H : Subgroup (Langlands.GeneralLinear (n + (j + k + 1) + 1) F.Carrier) :=
    Conductor.principalLevelSubgroup F.Carrier (n + (j + k + 1)) a ⊓
      GeneralLinear.mirabolic (n + (j + k + 1)) F.Carrier
  have hθ : ∀ u : upperUnipotent (n + (j + k + 1) + 1) F.Carrier,
      (u : Langlands.GeneralLinear (n + (j + k + 1) + 1) F.Carrier) ∈ H →
        standardCharacter ψ (n + (j + k + 1)) u = 1 := by
    intro u hu
    have h₁ : (u : Langlands.GeneralLinear (n + (j + k + 1) + 1) F.Carrier) ∈ O :=
      hK₂ (Conductor.principalLevelSubgroup_antitone F.Carrier _ ha₂a (Subgroup.mem_inf.mp hu).1)
    have h₂ : u ∈ Subtype.val ⁻¹' O := h₁
    exact MonoidHom.mem_ker.mp (hOK h₂)
  let φ : WhittakerFunctions ψ (n + (j + k + 1)) :=
    ⟨MirabolicUnitTest.cosetExtension _ H (standardCharacter ψ (n + (j + k + 1))),
      fun u g => MirabolicUnitTest.cosetExtension_left hθ u g⟩
  let Kr : Subgroup (GeneralLinear.mirabolic (n + (j + k + 1)) F.Carrier) :=
    (Conductor.principalLevelSubgroup F.Carrier (n + (j + k + 1)) a).comap
      (GeneralLinear.mirabolic (n + (j + k + 1)) F.Carrier).subtype
  have hH : ∀ m : Kr, m.val.val ∈ H := fun m =>
    Subgroup.mem_inf.mpr ⟨m.property, m.val.property⟩
  have hφ : IsMirabolicTestFunction ψ (n + (j + k + 1)) φ := by
    refine isMirabolicTestFunction_of_compact_mirabolic_support ψ φ Kr ?_
      (Conductor.principalLevelOpenSubgroup F.Carrier (n + (j + k + 1)) a) ?_ ?_ ?_
    · exact (GeneralLinear.Mirabolic.isClosed (F := F.Carrier)
        (n := n + (j + k + 1))).isClosedEmbedding_subtypeVal.isCompact_preimage
        (Conductor.isCompact_principalLevelOpenSubgroup F.Carrier _ a)
    · intro g hg hP
      exact ⟨⟨g, hP⟩, hg, rfl⟩
    · intro g hg
      apply MirabolicUnitTest.cosetExtension_eq_zero
      rintro ⟨u, h, hh, rfl⟩
      exact hg ⟨u, ⟨⟨h, (Subgroup.mem_inf.mp hh).2⟩, (Subgroup.mem_inf.mp hh).1⟩, rfl⟩
    · intro g m
      exact MirabolicUnitTest.cosetExtension_right hθ g (hH m)
  -- The support sets, their masses and the rescaling constant.
  let Ω : Set (LeftUnipotentQuotient n F.Carrier) :=
    compactOpenQuotientOrbit (upperUnipotent (n + 1) F.Carrier)
      (Conductor.principalLevelOpenSubgroup F.Carrier n a)
  let X : Set (Matrix (Fin j) (Fin (n + 1)) F.Carrier) :=
    {x | ∀ p l, x p l ∈ levelSet F.Carrier a}
  obtain ⟨hΩpos, hΩfin⟩ := hμ.compactOpenQuotientOrbit_mass
    (Conductor.principalLevelOpenSubgroup F.Carrier n a)
    (Conductor.isCompact_principalLevelOpenSubgroup F.Carrier n a)
  have hSpos : 0 < ν.measure (levelSet F.Carrier a) :=
    (isOpen_levelSet a).measure_pos _ ⟨0, zero_mem_levelSet a⟩
  have hSfin : ν.measure (levelSet F.Carrier a) < ⊤ := (isCompact_levelSet a).measure_lt_top
  have hXeq := rectangularMeasure_entries ν j (n + 1) (levelSet F.Carrier a)
  have hXpos : 0 < rectangularMeasure ν j (n + 1) X := by
    rw [hXeq]
    exact ENNReal.pow_pos (ENNReal.pow_pos hSpos _) _
  have hXfin : rectangularMeasure ν j (n + 1) X < ⊤ := by
    rw [hXeq]
    exact ENNReal.pow_lt_top (ENNReal.pow_lt_top hSfin)
  have hΩmeas : MeasurableSet Ω := (isOpen_compactOpenQuotientOrbit _ _).measurableSet
  have hXmeas : MeasurableSet X := measurableSet_entries (isOpen_levelSet a).measurableSet
  have hΩ0 : μ.real Ω ≠ 0 := (ENNReal.toReal_pos hΩpos.ne' hΩfin.ne).ne'
  have hX0 : (rectangularMeasure ν j (n + 1)).real X ≠ 0 :=
    (ENNReal.toReal_pos hXpos.ne' hXfin.ne).ne'
  let C : ℂ := ((μ.real Ω * (rectangularMeasure ν j (n + 1)).real X : ℝ) : ℂ)⁻¹
  -- The rescaled actual coefficient vector, constant `C` on the smaller level.
  let f' : (coefficientModel σ ℓ').toSubmodule := (C * (ℓ'.val w)⁻¹) • modelMap σ ℓ' w
  have hf' : ∀ c ∈ Conductor.principalLevelSubgroup F.Carrier n a, f'.val.val c = C := by
    intro c hc
    change (C * (ℓ'.val w)⁻¹) * ℓ'.val (σ c w) = C
    rw [hfix c (hKt c hc).1, mul_assoc, inv_mul_cancel₀ hw, mul_one]
  have hweight : ∀ c ∈ Conductor.principalLevelSubgroup F.Carrier n a, ∀ z : ℂ,
      determinantWeight (normalizedAbsoluteValue T) c z = 1 := by
    intro c hc z
    have h := T.determinantNorm_coe (n + 1) c
    rw [(hKt c hc).2, Units.val_one, NNReal.coe_one] at h
    have h' : T.normalizedAbs (Matrix.det c.val) = 1 := h.symm
    change ((T.normalizedAbs (Matrix.det c.val) : ℝ) : ℂ) ^ z = 1
    rw [h', Complex.ofReal_one, Complex.one_cpow]
  -- The integrand is `C` times the indicator of `Ω × X`.
  have hval : ∀ (s : ℂ) (x : Matrix (Fin j) (Fin (n + 1)) F.Carrier)
      (q : LeftUnipotentQuotient n F.Carrier),
      unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k φ f'.val s x q =
        (Ω ×ˢ X).indicator (fun _ => C) (q, x) := by
    intro s x q
    induction q using Quotient.inductionOn with
    | h g =>
      by_cases hgx : (Quotient.mk _ g, x) ∈ Ω ×ˢ X
      · rw [Set.indicator_of_mem hgx]
        obtain ⟨⟨c, hc, hcg⟩, hx⟩ := hgx
        dsimp only at hcg
        rw [← hcg, leftQuotientMap_apply, unequalRankIntegrand_mk]
        have hM : unequalRankMatrix j k c x ∈ H := unequalRankMatrix_mem ha hc hx
        have h1 : φ.val (unequalRankMatrix j k c x) = 1 := by
          simpa using MirabolicUnitTest.cosetExtension_mul hθ 1 hM
        rw [h1, hf' c hc, hweight c hc, one_mul, mul_one]
      · rw [Set.indicator_of_notMem hgx, unequalRankIntegrand_mk]
        have hz : φ.val (unequalRankMatrix j k g x) = 0 := by
          apply MirabolicUnitTest.cosetExtension_eq_zero
          rintro ⟨u, h, hh, hgxu⟩
          obtain ⟨⟨c, hc, hgc⟩, hx⟩ :=
            exists_of_unequalRankMatrix_eq ha u (Subgroup.mem_inf.mp hh).1 hgxu
          exact hgx ⟨⟨c, hc, Quotient.sound (QuotientGroup.rightRel_apply.mpr hgc)⟩, hx⟩
        rw [hz, zero_mul, zero_mul]
  refine ⟨φ, f', hφ, fun s => ⟨?_, ?_⟩⟩
  · -- Integrability of a constant on a product of finite-measure sets.
    have hint : Integrable ((Ω ×ˢ X).indicator fun _ => C)
        (μ.prod (rectangularMeasure ν j (n + 1))) := by
      rw [integrable_indicator_iff (hΩmeas.prod hXmeas)]
      exact integrableOn_const
        ((Measure.prod_prod_le _ _).trans_lt (ENNReal.mul_lt_top hΩfin hXfin)).ne
    exact hint.congr (Filter.Eventually.of_forall fun qx => (hval s qx.2 qx.1).symm)
  · -- The inner integral over `X`, then the outer integral over `Ω`.
    have hinner : ∀ q, ∫ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k φ
        f'.val s x q ∂(rectangularMeasure ν j (n + 1)) =
          Ω.indicator (fun _ => (rectangularMeasure ν j (n + 1)).real X • C) q := by
      intro q
      by_cases hq : q ∈ Ω
      · rw [Set.indicator_of_mem hq, ← integral_indicator_const C hXmeas]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change _ = X.indicator (fun _ => C) x
        refine (hval s x q).trans ?_
        by_cases hx : x ∈ X
        · rw [Set.indicator_of_mem (Set.mk_mem_prod hq hx), Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem (fun h => hx h.2), Set.indicator_of_notMem hx]
      · rw [Set.indicator_of_notMem hq]
        have h0 : ∀ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k φ
            f'.val s x q = 0 := fun x => by
          rw [hval s x q, Set.indicator_of_notMem (fun h => hq h.1)]
        simp only [h0, integral_zero]
    unfold unequalRankIntegral
    simp only [hinner]
    rw [integral_indicator_const _ hΩmeas, Complex.real_smul, Complex.real_smul,
      ← mul_assoc, ← Complex.ofReal_mul]
    exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (mul_ne_zero hΩ0 hX0))

end Langlands.RankinSelberg
