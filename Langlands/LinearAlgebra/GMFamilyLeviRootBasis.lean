import Langlands.LinearAlgebra.GMFamilyRootBasis
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Topology.Order.LeftRightNhds

/-! # Levi flats and simple-root projections -/

noncomputable section

open scoped RealInnerProductSpace Topology
open Submodule Classical

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {R : Finset E} {a : Submodule ℝ E}

/-- The closed chamber determined by the positive roots of the reference point. -/
def chamberClosure (R : Finset E) (h : E) : Set E :=
  {p | ∀ x ∈ posSet R h, 0 ≤ ⟪x, p⟫}

theorem mem_leviSpaceOf_iff {p y : E} :
    y ∈ leviSpaceOf R p ↔ ∀ x ∈ R, ⟪x, p⟫ = 0 → ⟪x, y⟫ = 0 := by
  simp [leviSpaceOf, Finset.mem_filter, and_imp, mem_orthogonal_singleton_iff_inner_right]

theorem centralSpace_le_leviSpaceOf (p : E) : centralSpace R ≤ leviSpaceOf R p := by
  intro y hy
  simp only [centralSpace, mem_iInf, mem_orthogonal_singleton_iff_inner_right] at hy
  exact mem_leviSpaceOf_iff.mpr fun x hx _ => hy x hx

theorem centralSpace_eq_orthogonal_span :
    centralSpace R = (span ℝ (↑R : Set E))ᗮ := by
  ext y
  simp only [centralSpace, mem_iInf, mem_orthogonal_singleton_iff_inner_right]
  constructor
  · intro h x hx
    have hle : span ℝ (↑R : Set E) ≤ (ℝ ∙ y)ᗮ :=
      span_le.mpr fun r hr => mem_orthogonal_singleton_iff_inner_left.mpr (h r hr)
    exact mem_orthogonal_singleton_iff_inner_left.mp (hle hx)
  · intro h x hx
    exact h x (subset_span hx)

section Projection

variable [FiniteDimensional ℝ E]

theorem inner_restrictedRoot {x y : E} (hy : y ∈ a) :
    ⟪(restrictedRoot a x : E), y⟫ = ⟪x, y⟫ := by
  have h := a.starProjection_inner_eq_zero x y hy
  rw [inner_sub_left, sub_eq_zero] at h
  exact h.symm

theorem restrictedRoot_eq_zero_iff {x : E} : restrictedRoot a x = 0 ↔ x ∈ aᗮ :=
  orthogonalProjectionOnto_eq_zero_iff

theorem restrictedRoot_eq_zero_of_pairing_eq_zero {x p : E} (hp : a = leviSpaceOf R p)
    (hx : x ∈ R) (hxp : ⟪x, p⟫ = 0) : restrictedRoot a x = 0 := by
  rw [restrictedRoot_eq_zero_iff]
  intro y hy
  exact inner_eq_zero_symm.mp (mem_leviSpaceOf_iff.mp (hp ▸ hy) x hx hxp)

theorem isRegular_leviSpaceOf (p : E) : IsRegular R (leviSpaceOf R p) p := by
  refine ⟨mem_leviSpaceOf_iff.mpr (fun _ _ h => h), fun x hx hn he => ?_⟩
  exact hn (restrictedRoot_eq_zero_of_pairing_eq_zero rfl hx he)

theorem leviSpaceOf_eq_of_isRegular (ha : IsLeviSpace R a) {p : E}
    (hp : IsRegular R a p) : leviSpaceOf R p = a := by
  obtain ⟨q, hq⟩ := ha
  have h (x : E) (hx : x ∈ R) : ⟪x, p⟫ = 0 ↔ ⟪x, q⟫ = 0 := by
    have hq' : q ∈ a := hq ▸ (isRegular_leviSpaceOf (R := R) q).1
    constructor
    · intro hz
      have hr : restrictedRoot a x = 0 := by
        by_contra hn
        exact hp.2 x hx hn hz
      simpa [hr] using (inner_restrictedRoot (x := x) hq').symm
    · intro hz
      have hr := restrictedRoot_eq_zero_of_pairing_eq_zero hq hx hz
      simpa [hr] using (inner_restrictedRoot (x := x) hp.1).symm
  rw [hq]
  exact le_antisymm
    (fun _ hy => mem_leviSpaceOf_iff.mpr fun x hx hz => mem_leviSpaceOf_iff.mp hy x hx ((h x hx).2 hz))
    (fun _ hy => mem_leviSpaceOf_iff.mpr fun x hx hz => mem_leviSpaceOf_iff.mp hy x hx ((h x hx).1 hz))

end Projection

theorem exists_regular_ambient (hR : IsRootSet R) : ∃ h : E, ∀ x ∈ R, ⟪x, h⟫ ≠ 0 := by
  obtain ⟨h, hh⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun x : R => innerₗ E (x : E)) (fun x => ⟨x, by
      exact ne_of_gt (real_inner_self_pos.mpr fun he => hR.1 (he ▸ x.prop))⟩)
  exact ⟨h, fun x hx => hh ⟨x, hx⟩⟩

/-- A sufficiently small positive perturbation preserves each specified nonzero sign. -/
theorem exists_pos_perturbation (R : Finset E) (p q : E) :
    ∃ t : ℝ, 0 < t ∧ ∀ x ∈ R,
      (0 < ⟪x, p⟫ → 0 < ⟪x, p + t • q⟫) ∧
      (⟪x, p⟫ < 0 → ⟪x, p + t • q⟫ < 0) := by
  have he : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ x ∈ R,
      (0 < ⟪x, p⟫ → 0 < ⟪x, p + t • q⟫) ∧
      (⟪x, p⟫ < 0 → ⟪x, p + t • q⟫ < 0) := by
    apply (Filter.eventually_all_finset R).2
    intro x _
    have hc : Continuous fun t : ℝ => ⟪x, p + t • q⟫ :=
      continuous_const.inner (continuous_const.add (continuous_id.smul continuous_const))
    have h₁ : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), (0 < ⟪x, p⟫ → 0 < ⟪x, p + t • q⟫) := by
      by_cases hp : 0 < ⟪x, p⟫
      · exact (hc.continuousAt.eventually (isOpen_Ioi.mem_nhds (by simpa using hp))).mono
          (fun _ ht _ => ht)
      · exact Filter.Eventually.of_forall (fun _ h => (hp h).elim)
    have h₂ : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), (⟪x, p⟫ < 0 → ⟪x, p + t • q⟫ < 0) := by
      by_cases hp : ⟪x, p⟫ < 0
      · exact (hc.continuousAt.eventually (isOpen_Iio.mem_nhds (by simpa using hp))).mono
          (fun _ ht _ => ht)
      · exact Filter.Eventually.of_forall (fun _ h => (hp h).elim)
    exact h₁.and h₂
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  exact (hpos.and (he.filter_mono nhdsWithin_le_nhds)).exists

/-- Every point belongs to a closed ambient chamber. -/
theorem exists_regular_ambient_chamber (hR : IsRootSet R) (p : E) :
    ∃ h : E, (∀ x ∈ R, ⟪x, h⟫ ≠ 0) ∧ p ∈ chamberClosure R h := by
  obtain ⟨q, hq⟩ := exists_regular_ambient hR
  obtain ⟨t, ht, hpt⟩ := exists_pos_perturbation R p q
  refine ⟨p + t • q, fun x hx => ?_, fun x hx => ?_⟩
  · rcases lt_trichotomy ⟪x, p⟫ 0 with hn | hz | hp
    · exact ne_of_lt ((hpt x hx).2 hn)
    · rw [inner_add_right, real_inner_smul_right, hz, zero_add]
      exact mul_ne_zero ht.ne' (hq x hx)
    · exact ne_of_gt ((hpt x hx).1 hp)
  · obtain ⟨hxr, hxp⟩ := mem_posSet_iff.mp hx
    exact le_of_not_gt fun hn => (not_lt_of_gt hxp) ((hpt x hxr).2 hn)

theorem posSet_subset_of_mem_chamberClosure (hR : IsRootSet R) {h p : E}
    (hh : ∀ x ∈ R, ⟪x, h⟫ ≠ 0) (hp : p ∈ chamberClosure R h) :
    posSet R p ⊆ posSet R h := by
  intro x hx
  obtain ⟨hxr, hxp⟩ := mem_posSet_iff.mp hx
  refine mem_posSet_iff.mpr ⟨hxr, ?_⟩
  rcases lt_or_gt_of_ne (hh x hxr) with hn | hy
  · have hneg := hp (-x) (mem_posSet_iff.mpr ⟨neg_mem_rootSet hR hxr, by simpa using hn⟩)
    simp only [inner_neg_left, neg_nonneg] at hneg
    exact (hxp.not_ge hneg).elim
  · exact hy

/-- Testing the positive simple roots suffices to test the closed chamber. -/
theorem mem_chamberClosure_iff {h p : E} :
    p ∈ chamberClosure R h ↔ ∀ x ∈ positiveSimpleRoots R h, 0 ≤ ⟪x, p⟫ := by
  refine ⟨fun hp x hx => hp x (Finset.mem_filter.mp hx).1, fun hp x hx => ?_⟩
  exact AddSubmonoid.closure_induction (motive := fun x _ => 0 ≤ ⟪x, p⟫)
    hp (by simp) (fun u v _ _ hu hv => by simpa only [inner_add_left] using add_nonneg hu hv)
    (root_mem_closure_positiveSimpleRoots hx)

/-- The simple roots that vanish at `p` cut out its Levi flat. -/
theorem leviSpaceOf_eq_orthogonal_span_active (hR : IsRootSet R) {h p : E}
    (hh : ∀ x ∈ R, ⟪x, h⟫ ≠ 0) (hp : p ∈ chamberClosure R h) :
    leviSpaceOf R p =
      (span ℝ (↑((positiveSimpleRoots R h).filter (fun x => ⟪x, p⟫ = 0)) : Set E))ᗮ := by
  let B₀ := (positiveSimpleRoots R h).filter fun x => ⟪x, p⟫ = 0
  let W := span ℝ (↑B₀ : Set E)
  have hvan (x : E) (hx : x ∈ posSet R h) (hx0 : ⟪x, p⟫ = 0) : x ∈ W := by
    have h : 0 ≤ ⟪x, p⟫ ∧ (⟪x, p⟫ = 0 → x ∈ W) := by
      refine AddSubmonoid.closure_induction
        (motive := fun x _ => 0 ≤ ⟪x, p⟫ ∧ (⟪x, p⟫ = 0 → x ∈ W)) ?_ ?_ ?_
        (root_mem_closure_positiveSimpleRoots hx)
      · intro y hy
        exact ⟨mem_chamberClosure_iff.mp hp y hy, fun hy0 =>
          subset_span (Finset.mem_filter.mpr ⟨hy, hy0⟩)⟩
      · simp
      · intro u v _ _ hu hv
        rw [inner_add_left]
        exact ⟨add_nonneg hu.1 hv.1, fun he =>
          W.add_mem (hu.2 (by linarith [hu.1, hv.1])) (hv.2 (by linarith [hu.1, hv.1]))⟩
    exact h.2 hx0
  ext y
  change y ∈ leviSpaceOf R p ↔ y ∈ Wᗮ
  rw [mem_leviSpaceOf_iff]
  constructor
  · intro hy
    have hle : W ≤ (ℝ ∙ y)ᗮ := span_le.mpr fun x hx => by
      obtain ⟨hx, hxp⟩ := Finset.mem_filter.mp (show x ∈ B₀ from hx)
      exact mem_orthogonal_singleton_iff_inner_left.mpr
        (hy x (mem_posSet_iff.mp (Finset.mem_filter.mp hx).1).1 hxp)
    exact fun x hx => mem_orthogonal_singleton_iff_inner_left.mp (hle hx)
  · intro hy x hx hxp
    apply hy x
    rcases lt_or_gt_of_ne (hh x hx) with hn | hn
    · refine (Submodule.neg_mem_iff W).mp (hvan (-x) ?_ (by simp [hxp]))
      exact mem_posSet_iff.mpr ⟨neg_mem_rootSet hR hx, by simpa using hn⟩
    · exact hvan x (mem_posSet_iff.mpr ⟨hx, hn⟩) hxp

theorem leviRoots_posSet_eq_filter (hR : IsRootSet R) (p : E) :
    leviRoots R (posSet R p) = R.filter (fun x => ⟪x, p⟫ = 0) := by
  ext x
  simp only [leviRoots, Finset.mem_filter, mem_posSet_iff, neg_mem_rootSet_iff hR, inner_neg_left]
  exact and_congr_right fun hx => by simp [hx, not_lt, le_antisymm_iff]

theorem isRootSet_leviRoots_posSet (hR : IsRootSet R) (p : E) :
    IsRootSet (leviRoots R (posSet R p)) := by
  rw [leviRoots_posSet_eq_filter hR]
  refine ⟨fun h => hR.1 (Finset.mem_filter.mp h).1, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨hx, hx0⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, hy0⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hR.2.1 x hx y hy, by simp [inner_sub_left, real_inner_smul_left,
      hx0, hy0]⟩
  · exact fun x hx y hy => hR.2.2 x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1

theorem leviSpaceOf_le_of_mem (ha : IsLeviSpace R a) {p : E} (hp : p ∈ a) :
    leviSpaceOf R p ≤ a := by
  obtain ⟨q, hq⟩ := ha
  rw [hq] at hp ⊢
  exact fun y hy => mem_leviSpaceOf_iff.mpr fun x hx hq0 =>
    mem_leviSpaceOf_iff.mp hy x hx (mem_leviSpaceOf_iff.mp hp x hx hq0)

theorem faceSpace_posSet_eq (hR : IsRootSet R) (ha : IsLeviSpace R a) {p : E} (hp : p ∈ a) :
    faceSpace R a (posSet R p) = leviSpaceOf R p := by
  unfold faceSpace
  rw [leviRoots_posSet_eq_filter hR]
  exact inf_eq_right.mpr (leviSpaceOf_le_of_mem ha hp)

section Restriction

variable [FiniteDimensional ℝ E]

/-- The nonvanishing ambient simple roots have linearly independent projections to the flat. -/
theorem linearIndependent_projected_positiveSimpleRoots (hR : IsRootSet R) {h p : E}
    (hh : ∀ x ∈ R, ⟪x, h⟫ ≠ 0) (hp : p ∈ chamberClosure R h)
    (ha : a = leviSpaceOf R p) :
    LinearIndependent ℝ (fun x : (positiveSimpleRoots R h).filter (fun x => ⟪x, p⟫ ≠ 0) =>
      restrictedRoot a (x : E)) := by
  let B := positiveSimpleRoots R h
  let A := B.filter (fun x => ⟪x, p⟫ = 0)
  let T := B.filter (fun x => ⟪x, p⟫ ≠ 0)
  have hA : aᗮ = span ℝ (↑A : Set E) := by
    rw [ha, leviSpaceOf_eq_orthogonal_span_active hR hh hp, orthogonal_orthogonal]
  have hd : Disjoint (span ℝ (↑T : Set E)) (span ℝ (↑A : Set E)) := by
    let v : B → E := Subtype.val
    let s : Set B := {x | ⟪(x : E), p⟫ ≠ 0}
    let t : Set B := {x | ⟪(x : E), p⟫ = 0}
    have hds : Disjoint s t := Set.disjoint_left.mpr fun _ hs ht => hs ht
    have hiT : v '' s = (↑T : Set E) := by
      ext x
      simpa [v, s, T] using
        (show (∃ y : B, ⟪(y : E), p⟫ ≠ 0 ∧ (y : E) = x) ↔ x ∈ B ∧ ⟪x, p⟫ ≠ 0 by
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact ⟨y.prop, hy⟩
          · exact fun ⟨hx, hxp⟩ => ⟨⟨x, hx⟩, hxp, rfl⟩)
    have hiA : v '' t = (↑A : Set E) := by
      ext x
      simpa [v, t, A] using
        (show (∃ y : B, ⟪(y : E), p⟫ = 0 ∧ (y : E) = x) ↔ x ∈ B ∧ ⟪x, p⟫ = 0 by
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact ⟨y.prop, hy⟩
          · exact fun ⟨hx, hxp⟩ => ⟨⟨x, hx⟩, hxp, rfl⟩)
    rw [← hiT, ← hiA]
    exact (linearIndependent_positiveSimpleRoots hR hh).disjoint_span_image hds
  let inc : T → B := fun x => ⟨x, (Finset.mem_filter.mp x.prop).1⟩
  have hinc : Function.Injective inc :=
    fun _ _ hxy => Subtype.ext (congrArg (fun x : B => (x : E)) hxy)
  have hli : LinearIndependent ℝ (fun x : T => (x : E)) :=
    (linearIndependent_positiveSimpleRoots hR hh).comp inc hinc
  have hproj : LinearIndependent ℝ
      (a.orthogonalProjectionOnto.toLinearMap ∘ (fun x : T => (x : E))) :=
    hli.map (by
      change Disjoint (span ℝ (Set.range fun x : T => (x : E))) a.orthogonalProjectionOnto.ker
      have hrange : Set.range (fun x : T => (x : E)) = (↑T : Set E) := by
        ext x
        exact ⟨fun ⟨j, hj⟩ => hj ▸ j.prop, fun h => ⟨⟨x, h⟩, rfl⟩⟩
      rwa [hrange, ker_orthogonalProjectionOnto, hA])
  exact hproj

/-- The simple roots of a Levi chamber are the nonzero projections of the ambient simple roots
    from any chamber containing the reference point in its closure. -/
theorem simpleRoots_posSet_eq_image (hR : IsRootSet R) {h p : E}
    (hh : ∀ x ∈ R, ⟪x, h⟫ ≠ 0) (hp : p ∈ chamberClosure R h)
    (ha : a = leviSpaceOf R p) :
    simpleRoots a (posSet R p) =
      ((positiveSimpleRoots R h).filter (fun x => ⟪x, p⟫ ≠ 0)).image (restrictedRoot a) := by
  let T := (positiveSimpleRoots R h).filter (fun x => ⟪x, p⟫ ≠ 0)
  let f : E →L[ℝ] a := a.orthogonalProjectionOnto
  let S := restrictedRoots a (posSet R p)
  have hpa : p ∈ a := ha ▸ (isRegular_leviSpaceOf (R := R) p).1
  have hT (x : T) : x.val ∈ posSet R p := by
    obtain ⟨hx, hx0⟩ := Finset.mem_filter.mp x.prop
    have hhx := (Finset.mem_filter.mp hx).1
    exact mem_posSet_iff.mpr ⟨(mem_posSet_iff.mp hhx).1, lt_of_le_of_ne (hp _ hhx) hx0.symm⟩
  have hlift (u : a) (hu : u ∈ S) : ∃ x ∈ posSet R p, f x = u :=
    Finset.mem_image.mp hu
  have hne (u : a) (hu : u ∈ S) : u ≠ 0 := by
    obtain ⟨x, hx, hxe⟩ := hlift u hu
    have hinner := inner_restrictedRoot (x := x) hpa
    change ⟪(f x : E), p⟫ = ⟪x, p⟫ at hinner
    rw [hxe] at hinner
    intro hzero
    have hn := (mem_posSet_iff.mp hx).2
    simp [hzero] at hinner
    linarith
  have hpreimage (u : a) (hu : u ∈ S) :
      ∃ x ∈ posSet R h, f x = u := by
    obtain ⟨x, hx, hxe⟩ := hlift u hu
    exact ⟨x, posSet_subset_of_mem_chamberClosure hR hh hp hx, hxe⟩
  have hexp (u : a) (hu : u ∈ S) : ∃ m : T → ℕ, u = ∑ j, m j • f (j : E) := by
    obtain ⟨x, hx, rfl⟩ := hpreimage u hu
    have hm : f x ∈ AddSubmonoid.closure (Set.range fun j : T => f (j : E)) := by
      refine AddSubmonoid.closure_induction
        (motive := fun y _ => f y ∈ AddSubmonoid.closure (Set.range fun j : T => f (j : E)))
        ?_ (by simp) (fun y z _ _ hy hz => by simpa only [map_add] using add_mem hy hz)
        (root_mem_closure_positiveSimpleRoots hx)
      intro y hy
      by_cases h : ⟪y, p⟫ = 0
      · have hyR := (mem_posSet_iff.mp (Finset.mem_filter.mp hy).1).1
        change restrictedRoot a y ∈ _
        rw [restrictedRoot_eq_zero_of_pairing_eq_zero ha hyR h]
        exact zero_mem _
      · exact AddSubmonoid.subset_closure ⟨⟨y, Finset.mem_filter.mpr ⟨hy, h⟩⟩, rfl⟩
    exact AddSubmonoid.mem_closure_range_iff_of_fintype.mp hm
  have hli : LinearIndependent ℝ (fun j : T => f (j : E)) :=
    linearIndependent_projected_positiveSimpleRoots hR hh hp ha
  ext v
  constructor
  · intro hv
    obtain ⟨hvs, hvind⟩ := Finset.mem_filter.mp hv
    let C := (posSet R h).filter (fun x => f x = v)
    obtain ⟨x, hx, hxe⟩ := hpreimage v hvs
    have hC : C.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, hxe⟩⟩
    obtain ⟨y, hy, hmin⟩ := C.exists_min_image (fun x => ⟪x, h⟫) hC
    obtain ⟨hypos, hyv⟩ := Finset.mem_filter.mp hy
    have hyp : ⟪y, p⟫ ≠ 0 := fun hz =>
      hne v hvs (hyv ▸ restrictedRoot_eq_zero_of_pairing_eq_zero ha (mem_posSet_iff.mp hypos).1 hz)
    refine Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨?_, hyp⟩, hyv⟩
    refine Finset.mem_filter.mpr ⟨hypos, ?_⟩
    rintro ⟨u, hu, w, hw, he⟩
    have he' : v = f u + f w := by rw [← hyv, he, map_add]
    rcases (hp u hu).eq_or_lt with hu0 | hu0 <;> rcases (hp w hw).eq_or_lt with hw0 | hw0
    · change v = restrictedRoot a u + restrictedRoot a w at he'
      rw [restrictedRoot_eq_zero_of_pairing_eq_zero ha (mem_posSet_iff.mp hu).1 hu0.symm,
        restrictedRoot_eq_zero_of_pairing_eq_zero ha (mem_posSet_iff.mp hw).1 hw0.symm, add_zero]
        at he'
      exact hne v hvs he'
    · have hu0' : f u = 0 :=
        restrictedRoot_eq_zero_of_pairing_eq_zero ha (mem_posSet_iff.mp hu).1 hu0.symm
      have hwv : f w = v := by simpa [hu0'] using he'.symm
      have hle := hmin w (Finset.mem_filter.mpr ⟨hw, hwv⟩)
      rw [he, inner_add_left] at hle
      linarith [(mem_posSet_iff.mp hu).2]
    · have hw0' : f w = 0 :=
        restrictedRoot_eq_zero_of_pairing_eq_zero ha (mem_posSet_iff.mp hw).1 hw0.symm
      have huv : f u = v := by simpa [hw0'] using he'.symm
      have hle := hmin u (Finset.mem_filter.mpr ⟨hu, huv⟩)
      rw [he, inner_add_left] at hle
      linarith [(mem_posSet_iff.mp hw).2]
    · exact hvind ⟨f u, Finset.mem_image.mpr ⟨u, mem_posSet_iff.mpr ⟨(mem_posSet_iff.mp hu).1, hu0⟩, rfl⟩,
        f w, Finset.mem_image.mpr ⟨w, mem_posSet_iff.mpr ⟨(mem_posSet_iff.mp hw).1, hw0⟩, rfl⟩, he'⟩
  · intro hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    let i : T := ⟨x, hx⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hT i, rfl⟩, ?_⟩
    rintro ⟨u, hu, w, hw, he⟩
    obtain ⟨m, hm⟩ := hexp u hu
    obtain ⟨n, hn⟩ := hexp w hw
    let d : T → ℝ := fun j => if j = i then 1 else 0
    have hsum : (∑ j : T, ((m j : ℝ) + (n j : ℝ)) • f (j : E)) =
        ∑ j : T, d j • f (j : E) := by
      simp only [add_smul, Finset.sum_add_distrib, Nat.cast_smul_eq_nsmul, ← hm, ← hn]
      rw [← he, Finset.sum_eq_single i]
      · simp [d, i, f, restrictedRoot]
      · intro j _ hji
        simp [d, hji]
      · simp
    have hc := linearIndependent_iff_injective_fintypeLinearCombination.mp hli
      (show Fintype.linearCombination ℝ (fun j : T => f (j : E)) (fun j => (m j : ℝ) + (n j : ℝ)) =
        Fintype.linearCombination ℝ (fun j : T => f (j : E)) d by
          simpa only [Fintype.linearCombination_apply] using hsum)
    have hcoeff (j : T) : m j + n j = if j = i then 1 else 0 := by
      have hj := congrFun hc j
      by_cases hji : j = i
      · simp only [d, hji, ite_true] at hj ⊢
        exact_mod_cast hj
      · simp only [d, hji, ite_false] at hj ⊢
        exact_mod_cast hj
    have hnpos : (m i = 0) ∨ (n i = 0) := by
      have hi := hcoeff i
      simp only [ite_true] at hi
      omega
    rcases hnpos with hmi | hni
    · have hmzero (j : T) : m j = 0 := by
        by_cases hji : j = i
        · exact hji ▸ hmi
        · have hj := hcoeff j
          simp [hji] at hj
          exact hj.1
      exact hne u hu (by simpa [hmzero] using hm)
    · have hnzero (j : T) : n j = 0 := by
        by_cases hji : j = i
        · exact hji ▸ hni
        · have hj := hcoeff j
          simp [hji] at hj
          exact hj.2
      exact hne w hw (by simpa [hnzero] using hn)

/-- The projected simple roots span the complement of the central space in the Levi flat. -/
theorem span_projected_positiveSimpleRoots (hR : IsRootSet R) {h p : E}
    (hh : ∀ x ∈ R, ⟪x, h⟫ ≠ 0) (ha : a = leviSpaceOf R p) :
    span ℝ (Set.range (fun x : (positiveSimpleRoots R h).filter (fun x => ⟪x, p⟫ ≠ 0) =>
      (restrictedRoot a (x : E) : E))) = a ⊓ (centralSpace R)ᗮ := by
  let B := positiveSimpleRoots R h
  let T := B.filter (fun x => ⟪x, p⟫ ≠ 0)
  let f : E →ₗ[ℝ] E := a.starProjection.toLinearMap
  have hspan : span ℝ (↑B : Set E) = (centralSpace R)ᗮ := by
    rw [centralSpace_eq_orthogonal_span, orthogonal_orthogonal, span_positiveSimpleRoots hR hh]
  have hmap : (span ℝ (↑B : Set E)).map f =
      span ℝ (Set.range fun x : T => (restrictedRoot a (x : E) : E)) := by
    rw [Submodule.map_span]
    apply le_antisymm
    · refine span_le.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      by_cases h : ⟪x, p⟫ = 0
      · have hr := (mem_posSet_iff.mp (Finset.mem_filter.mp hx).1).1
        have hz := restrictedRoot_eq_zero_of_pairing_eq_zero ha hr h
        change (restrictedRoot a x : E) ∈ _
        rw [hz]
        exact zero_mem _
      · exact subset_span ⟨⟨x, Finset.mem_filter.mpr ⟨hx, h⟩⟩, rfl⟩
    · refine span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      exact subset_span ⟨j, (Finset.mem_filter.mp j.prop).1, rfl⟩
  change _ = a ⊓ (centralSpace R)ᗮ
  rw [← hmap, hspan]
  have hz : centralSpace R ≤ a := ha ▸ centralSpace_le_leviSpaceOf p
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨a.starProjection_apply_mem y, fun w hw => ?_⟩
    rw [real_inner_comm]
    change ⟪(restrictedRoot a y : E), w⟫ = 0
    rw [inner_restrictedRoot (hz hw), real_inner_comm]
    exact hy w hw
  · intro hx
    exact ⟨x, hx.2, a.starProjection_eq_self_iff.mpr hx.1⟩

end Restriction

end Langlands.GMFamily
