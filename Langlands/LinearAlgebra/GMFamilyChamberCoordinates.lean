import Langlands.LinearAlgebra.GMFamilyLeviRootBasis
import Langlands.LinearAlgebra.GMFamilySplittingGeometry
import Langlands.LinearAlgebra.GMFamilyOrthogonalSetLimitStatement

/-! # Obtuse simple roots and chamber coordinates

The simple restricted roots of a chamber of a Levi space are pairwise obtuse. For `t ≥ 0`, the
coordinates in the basis of simple roots of a point `Y ∈ 𝔞_M^G` with `⟪v, Y⟫ ≥ t` for all simple
roots `v` are at least `c t`, for a constant `c > 0` depending only on the chamber. -/

noncomputable section

open scoped RealInnerProductSpace
open Finset Classical

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a linearly independent pairwise obtuse family, a combination whose inner products with
all members are nonnegative has nonnegative coefficients. -/
theorem coeff_nonneg_of_obtuse {ι : Type*} [Fintype ι] {v : ι → E} (hv : LinearIndependent ℝ v)
    (hobt : ∀ i j, i ≠ j → ⟪v i, v j⟫ ≤ 0) (c : ι → ℝ)
    (hc : ∀ j, 0 ≤ ⟪v j, ∑ i, c i • v i⟫) : ∀ i, 0 ≤ c i := by
  classical
  let p : ι → ℝ := fun i => max (c i) 0
  let m : ι → ℝ := fun i => max (-c i) 0
  have hp0 (i : ι) : 0 ≤ p i := le_max_right _ _
  have hm0 (i : ι) : 0 ≤ m i := le_max_right _ _
  have hcpm (i : ι) : c i = p i - m i := by
    simp only [p, m]
    rcases le_total (c i) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  have hpm (i : ι) : m i * p i = 0 := by
    simp only [p, m]
    rcases le_total (c i) 0 with h | h
    · rw [max_eq_right h]; ring
    · rw [max_eq_right (neg_nonpos.mpr h)]; ring
  let wp := ∑ i, p i • v i
  let wm := ∑ i, m i • v i
  have hw : ∑ i, c i • v i = wp - wm := by
    simp only [wp, wm, ← Finset.sum_sub_distrib, ← sub_smul, hcpm]
  have h1 : 0 ≤ ⟪wm, wp - wm⟫ := by
    rw [← hw]
    simp only [wm, sum_inner, real_inner_smul_left]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hm0 i) (hc i)
  have h2 : ⟪wm, wp⟫ ≤ 0 := by
    have hexp : ⟪wm, wp⟫ = ∑ i, ∑ j, m i * (p j * ⟪v i, v j⟫) := by
      simp only [wm, wp]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_smul_right]
    rw [hexp]
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      rw [← mul_assoc, hpm i, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (hm0 i)
        (mul_nonpos_of_nonneg_of_nonpos (hp0 j) (hobt i j hij))
  have h3 : ⟪wm, wm⟫ ≤ 0 := by
    rw [inner_sub_right] at h1
    linarith
  have hwm : wm = 0 := real_inner_self_nonpos.mp h3
  have hm : ∀ i, m i = 0 := Fintype.linearIndependent_iff.mp hv m hwm
  intro i
  have hi := hm i
  simp only [m] at hi
  have : -c i ≤ 0 := hi ▸ le_max_left (-c i) 0
  linarith

/-- The indecomposable positive roots at a regular point are pairwise obtuse. -/
theorem positiveSimpleRoots_inner_nonpos {R : Finset E} (hR : IsRootSet R) {h : E}
    (hh : ∀ x ∈ R, ⟪x, h⟫ ≠ 0) {x y : E} (hx : x ∈ positiveSimpleRoots R h)
    (hy : y ∈ positiveSimpleRoots R h) (hne : x ≠ y) : ⟪x, y⟫ ≤ 0 := by
  by_contra! hp
  have hi := Finset.mem_filter.mp hx
  have hj := Finset.mem_filter.mp hy
  have hd := hR.sub_mem_of_inner_pos (mem_posSet_iff.mp hi.1).1 (mem_posSet_iff.mp hj.1).1 hne hp
  rcases lt_or_gt_of_ne (hh _ hd) with hn | hn
  · have hj' : y - x ∈ posSet R h := by
      refine mem_posSet_iff.mpr ⟨?_, ?_⟩
      · simpa only [neg_sub] using neg_mem_rootSet hR hd
      · rw [inner_sub_left] at hn ⊢
        linarith
    exact hj.2 ⟨x, hi.1, y - x, hj', by abel⟩
  · have hi' : x - y ∈ posSet R h := mem_posSet_iff.mpr ⟨hd, hn⟩
    exact hi.2 ⟨y, hj.1, x - y, hi', by abel⟩

variable [FiniteDimensional ℝ E] {R : Finset E} {a : Submodule ℝ E}

/-- **The simple roots of a chamber of a Levi space are pairwise obtuse.** They are the
projections of ambient simple roots, and the projection removes a combination with
nonpositive coefficients of the ambient simple roots vanishing on the Levi space. -/
theorem simpleRoots_inner_nonpos (hR : IsRootSet R) (ha : IsLeviSpace R a) {P : Finset E}
    (hP : P ∈ parabolics R a) {u v : a} (hu : u ∈ simpleRoots a P) (hv : v ∈ simpleRoots a P)
    (hne : u ≠ v) : ⟪(u : E), (v : E)⟫ ≤ 0 := by
  classical
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hP
  have hap : a = leviSpaceOf R p := ha.eq_leviSpaceOf_of_regular hp
  obtain ⟨h, hh, hph⟩ := exists_regular_ambient_chamber hR p
  have himg := simpleRoots_posSet_eq_image (a := a) hR hh hph hap
  rw [himg] at hu hv
  obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨y, hyT, rfl⟩ := Finset.mem_image.mp hv
  have hxy : x ≠ y := fun he => hne (he ▸ rfl)
  obtain ⟨hxB, hx0⟩ := Finset.mem_filter.mp hxT
  obtain ⟨hyB, hy0⟩ := Finset.mem_filter.mp hyT
  let B₀ := (positiveSimpleRoots R h).filter (fun z => ⟪z, p⟫ = 0)
  have hperp : aᗮ = Submodule.span ℝ (↑B₀ : Set E) := by
    rw [hap, leviSpaceOf_eq_orthogonal_span_active hR hh hph, Submodule.orthogonal_orthogonal]
  -- the component of `y` orthogonal to `a`
  let z : E := y - (restrictedRoot a y : E)
  have hz : z ∈ aᗮ := by
    simp only [z, restrictedRoot]
    exact a.sub_starProjection_mem_orthogonal y
  rw [hperp] at hz
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hz
  -- inner products of `z` with the vanishing simple roots
  have hB₀a (b : E) (hb : b ∈ B₀) : b ∈ aᗮ := by
    rw [hperp]; exact Submodule.subset_span hb
  have hzb (b : E) (hb : b ∈ B₀) : ⟪b, z⟫ ≤ 0 := by
    have h0 : ⟪b, (restrictedRoot a y : E)⟫ = 0 :=
      (Submodule.mem_orthogonal' a b).mp (hB₀a b hb) _ (restrictedRoot a y).property
    simp only [z, inner_sub_right, h0, sub_zero]
    obtain ⟨hbB, hb0⟩ := Finset.mem_filter.mp hb
    exact positiveSimpleRoots_inner_nonpos hR hh hbB hyB (fun he => hy0 (he ▸ hb0))
  -- the coefficients of `z` are nonpositive
  have hli : LinearIndependent ℝ (fun b : B₀ => (b : E)) :=
    (linearIndependent_positiveSimpleRoots hR hh).comp
      (fun b : B₀ => (⟨b, (Finset.mem_filter.mp b.property).1⟩ : positiveSimpleRoots R h))
      (fun b b' he => Subtype.ext (congrArg Subtype.val he : _))
  have hcneg : ∀ b : B₀, 0 ≤ -c b := by
    refine coeff_nonneg_of_obtuse hli ?_ (fun b => -c b) ?_
    · intro b b' hbb'
      exact positiveSimpleRoots_inner_nonpos hR hh (Finset.mem_filter.mp b.property).1
        (Finset.mem_filter.mp b'.property).1 (fun he => hbb' (Subtype.ext he))
    · intro b
      have hsum : ∑ i : B₀, -c i • (i : E) = -z := by
        rw [← hc, ← Finset.sum_coe_sort B₀, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => neg_smul _ _
      rw [hsum, inner_neg_right]
      exact neg_nonneg.mpr (hzb b b.property)
  -- conclude
  have hxz : 0 ≤ ⟪x, z⟫ := by
    rw [← hc, inner_sum]
    refine Finset.sum_nonneg fun b hb => ?_
    rw [real_inner_smul_right]
    have hcb : c b ≤ 0 := by have := hcneg ⟨b, hb⟩; simpa using this
    exact mul_nonneg_of_nonpos_of_nonpos hcb
      (positiveSimpleRoots_inner_nonpos hR hh hxB (Finset.mem_filter.mp hb).1
        (fun he => hx0 (he ▸ (Finset.mem_filter.mp hb).2)))
  have hxyB := positiveSimpleRoots_inner_nonpos hR hh hxB hyB hxy
  have hval : ⟪((restrictedRoot a x : a) : E), ((restrictedRoot a y : a) : E)⟫ =
      ⟪x, y⟫ - ⟪x, z⟫ := by
    have h1 : ⟪((restrictedRoot a x : a) : E), ((restrictedRoot a y : a) : E)⟫ =
        ⟪x, ((restrictedRoot a y : a) : E)⟫ := by
      have := inner_restrictedRoot_subtype a x (restrictedRoot a y)
      simpa using this
    rw [h1]
    simp only [z, inner_sub_right]
    ring
  rw [hval]
  linarith

/-- A simple root of a chamber, as a vector of `relativeSpace R a`. -/
def chamberVector (hR : IsRootSet R) (ha : IsLeviSpace R a) {P : Finset E}
    (hP : P ∈ parabolics R a) (i : simpleRoots a P) : relativeSpace R a :=
  ⟨((i : a) : E), by
    change ((i : a) : E) ∈ a ⊓ (centralSpace R)ᗮ
    rw [← span_simpleRoots_eq hR ha hP]
    exact Submodule.subset_span (Set.mem_range_self i)⟩

theorem chamberVector_linearIndependent (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {P : Finset E} (hP : P ∈ parabolics R a) : LinearIndependent ℝ (chamberVector hR ha hP) := by
  apply LinearIndependent.of_comp (relativeSpace R a).subtype
  exact (linearIndependent_simpleRoots hR ha hP).map' a.subtype
    (LinearMap.ker_eq_bot.mpr a.injective_subtype)

theorem chamberVector_span (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {P : Finset E} (hP : P ∈ parabolics R a) :
    ⊤ ≤ Submodule.span ℝ (Set.range (chamberVector hR ha hP)) := by
  apply le_of_eq
  apply Submodule.map_injective_of_injective (relativeSpace R a).injective_subtype
  rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span, ← Set.range_comp]
  exact (span_simpleRoots_eq hR ha hP).symm

/-- The simple roots of a chamber, as a basis of `relativeSpace R a`. -/
def chamberBasis (hR : IsRootSet R) (ha : IsLeviSpace R a) {P : Finset E}
    (hP : P ∈ parabolics R a) : Module.Basis (simpleRoots a P) ℝ (relativeSpace R a) :=
  Module.Basis.mk (chamberVector_linearIndependent hR ha hP) (chamberVector_span hR ha hP)

theorem chamberBasis_apply (hR : IsRootSet R) (ha : IsLeviSpace R a) {P : Finset E}
    (hP : P ∈ parabolics R a) (i : simpleRoots a P) :
    ((chamberBasis hR ha hP i : relativeSpace R a) : E) = ((i : a) : E) := by
  rw [chamberBasis, Module.Basis.coe_mk]
  rfl

/-- **Chamber coordinates grow with the distance to the walls.** There is `c > 0` such that
every point `y` of `relativeSpace R a` with `⟪v, y⟫ ≥ t ≥ 0` for all simple roots `v` of the
chamber has all its coordinates in the basis of simple roots at least `c t`. -/
theorem exists_chamber_coord_lower (hR : IsRootSet R) (ha : IsLeviSpace R a) {P : Finset E}
    (hP : P ∈ parabolics R a) :
    ∃ c > 0, ∀ (y : relativeSpace R a) (t : ℝ), 0 ≤ t →
      (∀ i : simpleRoots a P, t ≤ ⟪((i : a) : E), (y : E)⟫) →
        ∀ i, c * t ≤ (chamberBasis hR ha hP).repr y i := by
  classical
  let b := chamberBasis hR ha hP
  let w : simpleRoots a P → E := fun i => ((i : a) : E)
  have hwb (i : simpleRoots a P) : ((b i : relativeSpace R a) : E) = w i :=
    chamberBasis_apply hR ha hP i
  have hli : LinearIndependent ℝ w := by
    have := (b.linearIndependent).map' (relativeSpace R a).subtype
      (LinearMap.ker_eq_bot.mpr (relativeSpace R a).injective_subtype)
    convert this using 1
    funext i
    exact (hwb i).symm
  have hobt : ∀ i j, i ≠ j → ⟪w i, w j⟫ ≤ 0 := fun i j hij =>
    simpleRoots_inner_nonpos hR ha hP i.property j.property (fun he => hij (Subtype.ext he))
  -- expansion of a vector of `relativeSpace R a` in the basis
  have hexp (y : relativeSpace R a) : (y : E) = ∑ i, b.repr y i • w i := by
    conv_lhs => rw [← b.sum_repr y]
    simp [hwb]
  -- the vector `ρ` with `⟪v, ρ⟫ = 1`
  obtain ⟨ρ, hρ⟩ := exists_inner_values b.linearIndependent (fun _ => (1 : ℝ))
  have hρE (i : simpleRoots a P) : ⟪w i, (ρ : E)⟫ = 1 := by
    rw [← hwb i]; exact hρ i
  have hcoeff (y : relativeSpace R a) (j : simpleRoots a P) :
      ⟪w j, ∑ i, b.repr y i • w i⟫ = ⟪w j, (y : E)⟫ := by rw [← hexp y]
  let r := b.repr ρ
  have hr0 : ∀ i, 0 ≤ r i := coeff_nonneg_of_obtuse hli hobt r (fun j => by
    rw [hcoeff ρ j, hρE j]; exact zero_le_one)
  have hrpos : ∀ i, 0 < r i := by
    intro i
    refine lt_of_le_of_ne (hr0 i) (fun hri => ?_)
    have h1 := hρE i
    rw [hexp ρ, inner_sum] at h1
    have hle : ∑ j, ⟪w i, r j • w j⟫ ≤ 0 := by
      refine Finset.sum_nonpos fun j _ => ?_
      rw [real_inner_smul_right]
      by_cases hij : i = j
      · subst hij; rw [← hri]; simp
      · exact mul_nonpos_of_nonneg_of_nonpos (hr0 j) (hobt i j hij)
    change ∑ j, ⟪w i, r j • w j⟫ = 1 at h1
    linarith
  obtain ⟨c, hc, hcr⟩ : ∃ c > 0, ∀ i, c ≤ r i := by
    rcases isEmpty_or_nonempty (simpleRoots a P) with he | hne
    · exact ⟨1, one_pos, fun i => (he.false i).elim⟩
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_min r
      exact ⟨r i₀, hrpos i₀, hi₀⟩
  refine ⟨c, hc, fun y t ht hy i => ?_⟩
  have hnn := coeff_nonneg_of_obtuse hli hobt (fun i => b.repr y i - t * r i) (fun j => by
    have hs : ∑ i, (b.repr y i - t * r i) • w i = (y : E) - t • (ρ : E) := by
      rw [hexp y, hexp ρ, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sub_smul, smul_smul]
    rw [hs, inner_sub_right, real_inner_smul_right, hρE j]
    linarith [hy j])
  have := hnn i
  nlinarith [hcr i]

end Langlands.GMFamily
