import Langlands.LinearAlgebra.GMFamilyInducedValues

/-! # Simple-root coordinates of Levi chamber faces -/

noncomputable section

open scoped RealInnerProductSpace
open Classical Submodule Module
open Langlands.LinearAlgebra.FiniteHyperplaneSegment

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {R : Finset E} {a : Submodule ℝ E}

/-- The simple roots of a chamber that vanish at the specified point. -/
def vanishingSimpleRoots (a : Submodule ℝ E) (P : Finset E) (p : E) : Finset a :=
  (simpleRoots a P).filter fun b => ⟪(b : E), p⟫ = 0

theorem exists_regular (R : Finset E) (a : Submodule ℝ E) : ∃ p : E, IsRegular R a p := by
  obtain ⟨p, hp, _⟩ := exists_regular_preserving_signs
    (rootForm (R := R) (a := a)) rootForm_ne_zero 0
  exact ⟨p, (isRegular_iff_rootForm p).mpr hp⟩

omit [FiniteDimensional ℝ E] in
theorem mem_leviSpaces_iff_exists_point (hR : IsRootSet R) (ha : IsLeviSpace R a) {L : Submodule ℝ E} :
    L ∈ leviSpaces R a ↔ ∃ p ∈ a, L = leviSpaceOf R p := by
  constructor
  · intro h
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨p, hp, rfl⟩ := (Finset.mem_filter.mp hQ).2
    exact ⟨p, hp, faceSpace_posSet_eq hR ha hp⟩
  · rintro ⟨p, hp, rfl⟩
    have hsubset : posSet R p ⊆ R := fun x hx => (mem_posSet_iff.mp hx).1
    exact Finset.mem_image.mpr ⟨posSet R p,
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsubset, p, hp, rfl⟩,
      faceSpace_posSet_eq hR ha hp⟩

theorem exists_leviSpace_inter_projected_roots {ι : Type*} (hR : IsRootSet R)
    (ha : IsLeviSpace R a) (r : ι → E) (hr : ∀ i, r i ∈ R) :
    (a ⊓ (span ℝ (Set.range fun i => (restrictedRoot a (r i) : E)))ᗮ : Submodule ℝ E) ∈ leviSpaces R a := by
  let W := span ℝ (Set.range fun i => (restrictedRoot a (r i) : E))
  let L := a ⊓ Wᗮ
  obtain ⟨p, hp⟩ := exists_regular R L
  apply (mem_leviSpaces_iff_exists_point hR ha).mpr
  refine ⟨p, hp.1.1, le_antisymm ?_ ?_⟩
  · intro y hy
    refine mem_leviSpaceOf_iff.mpr fun x hx hxp => ?_
    have h0 : restrictedRoot L x = 0 := by
      by_contra h
      exact hp.2 x hx h hxp
    rw [← inner_restrictedRoot hy, h0]
    simp
  · intro y hy
    have hya := leviSpaceOf_le_of_mem ha hp.1.1 hy
    refine ⟨hya, fun x hx => ?_⟩
    have hs : W ≤ (ℝ ∙ y)ᗮ := by
      apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply mem_orthogonal_singleton_iff_inner_left.mpr
      rw [inner_restrictedRoot hya]
      refine mem_leviSpaceOf_iff.mp hy _ (hr i) ?_
      rw [← inner_restrictedRoot hp.1.1]
      exact hp.1.2 _ (subset_span (Set.mem_range_self i))
    exact mem_orthogonal_singleton_iff_inner_left.mp (hs hx)

private def projectedSimpleEquiv (hR : IsRootSet R) {h p : E}
    (hh : ∀ x ∈ R, ⟪x, h⟫ ≠ 0) (hp : p ∈ chamberClosure R h) (ha : a = leviSpaceOf R p) :
    ((positiveSimpleRoots R h).filter fun x => ⟪x, p⟫ ≠ 0) ≃ simpleRoots a (posSet R p) := by
  let T := (positiveSimpleRoots R h).filter fun x => ⟪x, p⟫ ≠ 0
  have he := simpleRoots_posSet_eq_image hR hh hp ha
  let f (i : T) : simpleRoots a (posSet R p) :=
    ⟨restrictedRoot a i, he ▸ Finset.mem_image.mpr ⟨i, i.prop, rfl⟩⟩
  refine Equiv.ofBijective f ⟨fun i j hij => ?_, fun j => ?_⟩
  · exact (linearIndependent_projected_positiveSimpleRoots hR hh hp ha).injective
      (congrArg Subtype.val hij)
  · have hj : (j : a) ∈ T.image (restrictedRoot a) :=
      (congrArg (fun s : Finset a => (j : a) ∈ s) he).mp j.prop
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
    exact ⟨⟨i, hi⟩, Subtype.ext hij⟩

/-- The simple roots of a Levi chamber form a basis of its noncentral subspace. -/
theorem simpleRoots_basis (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {P : Finset E} (hP : P ∈ parabolics R a) :
    LinearIndependent ℝ (fun b : simpleRoots a P => ((b : a) : E)) ∧
      span ℝ (Set.range fun b : simpleRoots a P => ((b : a) : E)) = a ⊓ (centralSpace R)ᗮ := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hP
  obtain ⟨h, hh, hph⟩ := exists_regular_ambient_chamber hR p
  have ha' := (leviSpaceOf_eq_of_isRegular ha hp).symm
  let e := projectedSimpleEquiv hR hh hph ha'
  have he (i : (positiveSimpleRoots R h).filter fun x => ⟪x, p⟫ ≠ 0) :
      (e i : a) = restrictedRoot a i := rfl
  constructor
  · have hl := linearIndependent_projected_positiveSimpleRoots hR hh hph ha'
    have hl' := hl.map' a.subtype (Submodule.ker_subtype a)
    convert hl'.comp e.symm e.symm.injective using 1
    funext i
    change ((i : a) : E) = (restrictedRoot a (e.symm i) : E)
    rw [← he, e.apply_symm_apply]
  · have hr : (Set.range fun i : simpleRoots a (posSet R p) => ((i : a) : E)) =
        Set.range (fun x : (positiveSimpleRoots R h).filter (fun x => ⟪x, p⟫ ≠ 0) =>
          (restrictedRoot a (x : E) : E)) := by
      ext x
      refine ⟨fun ⟨i, hi⟩ => ⟨e.symm i, ?_⟩, fun ⟨i, hi⟩ => ⟨e i, ?_⟩⟩
      · change (restrictedRoot a (e.symm i) : E) = x
        rw [← he, e.apply_symm_apply]
        exact hi
      · change ((e i : a) : E) = x
        rw [he]
        exact hi
    rw [hr, span_projected_positiveSimpleRoots hR hh ha']

/-- Every positive restricted root belongs to the additive monoid of the chamber normals. -/
theorem restrictedRoot_mem_simpleRoot_closure (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {P : Finset E} (hP : P ∈ parabolics R a) {r : E} (hr : r ∈ P) :
    ((restrictedRoot a r : a) : E) ∈ AddSubmonoid.closure
      (Set.range fun b : simpleRoots a P => ((b : a) : E)) := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hP
  obtain ⟨h, hh, hph⟩ := exists_regular_ambient_chamber hR p
  have ha' := (leviSpaceOf_eq_of_isRegular ha hp).symm
  have hpos := posSet_subset_of_mem_chamberClosure hR hh hph hr
  let S := AddSubmonoid.closure (Set.range fun b : simpleRoots a (posSet R p) => ((b : a) : E))
  change a.starProjection r ∈ S
  refine AddSubmonoid.closure_induction (motive := fun x _ => a.starProjection x ∈ S)
    ?_ (by simp) (fun x y _ _ hx hy => by simpa only [map_add] using S.add_mem hx hy)
    (root_mem_closure_positiveSimpleRoots hpos)
  intro x hx
  by_cases hx0 : ⟪x, p⟫ = 0
  · rw [starProjection_apply]
    have hxR : x ∈ R := (mem_posSet_iff.mp (Finset.mem_filter.mp hx).1).1
    rw [show a.orthogonalProjectionOnto x = 0 from restrictedRoot_eq_zero_of_pairing_eq_zero ha' hxR hx0]
    exact zero_mem S
  · apply AddSubmonoid.subset_closure
    refine ⟨⟨restrictedRoot a x, ?_⟩, rfl⟩
    rw [simpleRoots_posSet_eq_image hR hh hph ha']
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hx0⟩, rfl⟩

theorem exists_root_of_mem_simpleRoots {P : Finset E} (b : simpleRoots a P) :
    ∃ r ∈ P, restrictedRoot a r = (b : a) :=
  Finset.mem_image.mp (Finset.mem_filter.mp b.prop).1

theorem chamberClosure_iff_nonneg_simpleRoots (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {P : Finset E} (hP : P ∈ parabolics R a) {p : E} (hp : p ∈ a) :
    (∀ r ∈ P, 0 ≤ ⟪r, p⟫) ↔ ∀ b : simpleRoots a P, 0 ≤ ⟪((b : a) : E), p⟫ := by
  refine ⟨fun h b => ?_, fun h r hr => ?_⟩
  · obtain ⟨r, hr, he⟩ := exists_root_of_mem_simpleRoots b
    rw [← he, inner_restrictedRoot hp]
    exact h r hr
  · rw [← inner_restrictedRoot hp]
    refine AddSubmonoid.closure_induction (motive := fun x _ => 0 ≤ ⟪x, p⟫) ?_ (by simp)
      (fun x y _ _ hx hy => by rw [inner_add_left]; exact add_nonneg hx hy)
      (restrictedRoot_mem_simpleRoot_closure hR ha hP hr)
    rintro _ ⟨b, rfl⟩
    exact h b

/-- The active simple roots in a closed Levi chamber give its face flat. -/
theorem leviSpaceOf_eq_of_vanishingSimpleRoots (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {P : Finset E} (hP : P ∈ parabolics R a) {p : E} (hp : p ∈ a)
    (hcl : ∀ r ∈ P, 0 ≤ ⟪r, p⟫) :
    leviSpaceOf R p = a ⊓ (span ℝ
      (Set.range fun b : vanishingSimpleRoots a P p => ((b : a) : E)))ᗮ := by
  let W := span ℝ (Set.range fun b : vanishingSimpleRoots a P p => ((b : a) : E))
  have hz (r : E) (hr : r ∈ P) (hr0 : ⟪r, p⟫ = 0) : (restrictedRoot a r : E) ∈ W := by
    have he : 0 ≤ ⟪(restrictedRoot a r : E), p⟫ ∧
        (⟪(restrictedRoot a r : E), p⟫ = 0 → (restrictedRoot a r : E) ∈ W) := by
      refine AddSubmonoid.closure_induction (motive := fun x _ =>
        0 ≤ ⟪x, p⟫ ∧ (⟪x, p⟫ = 0 → x ∈ W)) ?_ (by simp) ?_
        (restrictedRoot_mem_simpleRoot_closure hR ha hP hr)
      · rintro _ ⟨b, rfl⟩
        exact ⟨(chamberClosure_iff_nonneg_simpleRoots hR ha hP hp).mp hcl b,
          fun hb => subset_span ⟨⟨(b : a), Finset.mem_filter.mpr ⟨b.prop, hb⟩⟩, rfl⟩⟩
      · intro x y _ _ hx hy
        rw [inner_add_left]
        exact ⟨add_nonneg hx.1 hy.1, fun hxy => W.add_mem
          (hx.2 (by linarith [hx.1, hy.1])) (hy.2 (by linarith [hx.1, hy.1]))⟩
    exact he.2 (by rwa [inner_restrictedRoot hp])
  obtain ⟨q, hq, hPq⟩ := mem_parabolics_iff.mp hP
  apply le_antisymm
  · intro y hy
    have hya := leviSpaceOf_le_of_mem ha hp hy
    refine ⟨hya, fun x hx => ?_⟩
    have hs : W ≤ (ℝ ∙ y)ᗮ := by
      apply span_le.mpr
      rintro _ ⟨b, rfl⟩
      let b' : simpleRoots a P := ⟨b, (Finset.mem_filter.mp b.prop).1⟩
      obtain ⟨r, hr, hbr⟩ := exists_root_of_mem_simpleRoots b'
      have hrR : r ∈ R := (mem_posSet_iff.mp (hPq ▸ hr)).1
      apply mem_orthogonal_singleton_iff_inner_left.mpr
      change ⟪((b' : a) : E), y⟫ = 0
      rw [← hbr, inner_restrictedRoot hya]
      apply mem_leviSpaceOf_iff.mp hy r hrR
      rw [← inner_restrictedRoot hp, hbr]
      exact (Finset.mem_filter.mp b.prop).2
    exact mem_orthogonal_singleton_iff_inner_left.mp (hs hx)
  · rintro y ⟨hy, hyW⟩
    refine mem_leviSpaceOf_iff.mpr fun r hr hr0 => ?_
    by_cases h0 : restrictedRoot a r = 0
    · rw [← inner_restrictedRoot hy, h0]; simp
    rcases lt_or_gt_of_ne (hq.2 r hr h0) with hn | hb
    · have hm : -r ∈ P := hPq.symm ▸ mem_posSet_iff.mpr ⟨neg_mem_rootSet hR hr, by simpa using hn⟩
      have he := hyW _ (hz (-r) hm (by simp [hr0]))
      rw [inner_restrictedRoot hy, inner_neg_left, neg_eq_zero] at he
      exact he
    · rw [← inner_restrictedRoot hy]
      exact hyW _ (hz r (hPq.symm ▸ mem_posSet_iff.mpr ⟨hr, hb⟩) hr0)

/-- The relative chamber cut from a fine chamber has the vanishing simple roots of that chamber. -/
theorem simpleRoots_inter_leviRoots_of_nonneg (hR : IsRootSet R) {P : Finset E} (hPR : P ⊆ R)
    {p : E} (hp : p ∈ a)
    (hcl : ∀ r ∈ P, 0 ≤ ⟪r, p⟫) :
    simpleRoots a (P ∩ leviRoots R (posSet R p)) = vanishingSimpleRoots a P p := by
  rw [leviRoots_posSet_eq_filter hR]
  have hres : restrictedRoots a (P ∩ R.filter (fun r => ⟪r, p⟫ = 0)) =
      (restrictedRoots a P).filter (fun b : a => ⟪(b : E), p⟫ = 0) := by
    ext b
    simp only [restrictedRoots, Finset.mem_image, Finset.mem_inter, Finset.mem_filter]
    refine ⟨fun ⟨r, ⟨hr, _, hr0⟩, he⟩ => ⟨⟨r, hr, he⟩, ?_⟩, fun ⟨⟨r, hr, he⟩, hb⟩ => ?_⟩
    · rw [← he, inner_restrictedRoot hp, hr0]
    · exact ⟨r, ⟨hr, hPR hr, by rwa [← inner_restrictedRoot hp, he]⟩, he⟩
  have hn (b : a) (hb : b ∈ restrictedRoots a P) : 0 ≤ ⟪(b : E), p⟫ := by
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hb
    rw [inner_restrictedRoot hp]
    exact hcl r hr
  ext b
  simp only [vanishingSimpleRoots, simpleRoots, hres, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hb, hz⟩, h⟩
    refine ⟨⟨hb, ?_⟩, hz⟩
    rintro ⟨x, hx, y, hy, he⟩
    have hs := congrArg (fun u : a => ⟪(u : E), p⟫) he
    change ⟪(b : E), p⟫ = ⟪(x : E) + (y : E), p⟫ at hs
    rw [hz, inner_add_left] at hs
    exact h ⟨x, ⟨hx, by linarith [hn x hx, hn y hy]⟩,
      y, ⟨hy, by linarith [hn x hx, hn y hy]⟩, he⟩
  · rintro ⟨⟨hb, h⟩, hz⟩
    exact ⟨⟨hb, hz⟩, fun ⟨x, hx, y, hy, he⟩ => h ⟨x, hx.1, y, hy.1, he⟩⟩

/-- The fine chamber split into its face signs and its relative Levi chamber. -/
theorem relative_chamber_of_closed (hR : IsRootSet R)
    {P : Finset E} (hP : P ∈ parabolics R a) {p : E} (hp : p ∈ a)
    (hcl : ∀ r ∈ P, 0 ≤ ⟪r, p⟫) :
    P ∩ leviRoots R (posSet R p) ∈ parabolics (leviRoots R (posSet R p)) a ∧
      posSet R p ∪ (P ∩ leviRoots R (posSet R p)) = P := by
  obtain ⟨q, hq, rfl⟩ := mem_parabolics_iff.mp hP
  let T := leviRoots R (posSet R p)
  have hT (r : E) : r ∈ T ↔ r ∈ R ∧ ⟪r, p⟫ = 0 := by
    simp [T, leviRoots_posSet_eq_filter hR]
  have hpos : posSet R q ∩ T = posSet T q := by
    ext r
    simp only [Finset.mem_inter, mem_posSet_iff, hT]
    tauto
  have hsub : posSet R p ⊆ posSet R q := by
    intro r hr
    obtain ⟨hr, hpos⟩ := mem_posSet_iff.mp hr
    have h0 : restrictedRoot a r ≠ 0 := fun h => by
      have hzero := inner_restrictedRoot (x := r) hp
      simp [h] at hzero
      exact hpos.ne' hzero.symm
    refine mem_posSet_iff.mpr ⟨hr, ?_⟩
    rcases lt_or_gt_of_ne (hq.2 r hr h0) with hn | hp'
    · have hc := hcl (-r) (mem_posSet_iff.mpr ⟨neg_mem_rootSet hR hr, by simpa using hn⟩)
      simp only [inner_neg_left, neg_nonneg] at hc
      exact (hpos.not_ge hc).elim
    · exact hp'
  refine ⟨?_, Finset.Subset.antisymm (Finset.union_subset hsub Finset.inter_subset_left) ?_⟩
  · rw [hpos]
    exact mem_parabolics_iff.mpr ⟨q, ⟨hq.1, fun r hr => hq.2 r ((hT r).mp hr).1⟩, rfl⟩
  · intro r hr
    rcases (hcl r hr).eq_or_lt with he | hlt
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hr, (hT r).mpr
        ⟨(mem_posSet_iff.mp hr).1, he.symm⟩⟩)
    · exact Finset.mem_union_left _ (mem_posSet_iff.mpr ⟨(mem_posSet_iff.mp hr).1, hlt⟩)

/-- A relative Levi chamber and the face signs give a fine chamber containing the face. -/
theorem chamber_union_relative (hR : IsRootSet R) {p : E} (hp : p ∈ a) {S : Finset E}
    (hS : S ∈ parabolics (leviRoots R (posSet R p)) a) :
    posSet R p ∪ S ∈ parabolics R a ∧ ∀ r ∈ posSet R p ∪ S, 0 ≤ ⟪r, p⟫ := by
  obtain ⟨q, hq, rfl⟩ := mem_parabolics_iff.mp hS
  let T := leviRoots R (posSet R p)
  have hT (r : E) : r ∈ T ↔ r ∈ R ∧ ⟪r, p⟫ = 0 := by
    simp [T, leviRoots_posSet_eq_filter hR]
  obtain ⟨t, ht, hsign⟩ := exists_pos_perturbation R p q
  let y := p + t • q
  have hy : IsRegular R a y := by
    refine ⟨a.add_mem hp (a.smul_mem t hq.1), fun r hr hn => ?_⟩
    rcases lt_trichotomy ⟪r, p⟫ 0 with hn' | he | hp'
    · exact ((hsign r hr).2 hn').ne
    · change ⟪r, p + t • q⟫ ≠ 0
      rw [inner_add_right, real_inner_smul_right, he, zero_add]
      exact mul_ne_zero ht.ne' (hq.2 r ((hT r).mpr ⟨hr, he⟩) hn)
    · exact ((hsign r hr).1 hp').ne'
  have heq : posSet R p ∪ posSet T q = posSet R y := by
    ext r
    simp only [Finset.mem_union, mem_posSet_iff, hT]
    by_cases hr : r ∈ R
    · simp only [hr, true_and]
      rcases lt_trichotomy ⟪r, p⟫ 0 with hn | he | hp'
      · simp [hn.ne, hn.not_gt, show ¬ 0 < ⟪r, y⟫ from ((hsign r hr).2 hn).not_gt]
      · simp only [y, inner_add_right, real_inner_smul_right, he, lt_irrefl, true_and,
          false_or, zero_add, mul_pos_iff_of_pos_left ht]
      · simp [hp', show 0 < ⟪r, y⟫ from (hsign r hr).1 hp']
    · simp [hr]
  refine ⟨mem_parabolics_iff.mpr ⟨y, hy, heq⟩, fun r hr => ?_⟩
  rcases Finset.mem_union.mp hr with hr | hr
  · exact (mem_posSet_iff.mp hr).2.le
  · exact le_of_eq ((hT r).mp (mem_posSet_iff.mp hr).1).2.symm

end Langlands.GMFamily
