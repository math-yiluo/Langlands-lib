import Langlands.LinearAlgebra.GMFamilyLeviRootBasis
import Mathlib.Algebra.Group.Irreducible.Indecomposable
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.QuadraticForm.Dual

/-! # Positive roots and Levi flats for `(G, M)`-families -/

noncomputable section

open scoped RealInnerProductSpace Topology
open Classical Filter

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
@[simp] theorem mem_posSet {R : Finset E} {x r : E} :
    r ∈ posSet R x ↔ r ∈ R ∧ 0 < ⟪r, x⟫ := Finset.mem_filter

omit [FiniteDimensional ℝ E] in
theorem IsRootSet.neg_mem {R : Finset E} (hR : IsRootSet R) {r : E} (hr : r ∈ R) : -r ∈ R := by
  have h0 : ⟪r, r⟫ ≠ 0 := (real_inner_self_pos.mpr (fun h => hR.1 (h ▸ hr))).ne'
  have hdiv : 2 * ⟪r, r⟫ / ⟪r, r⟫ = 2 := by field_simp
  have h := hR.2.1 r hr r hr
  rw [hdiv, two_smul] at h
  convert h using 1
  abel

omit [FiniteDimensional ℝ E] in
private theorem root_sub_mem {R : Finset E} (hR : IsRootSet R) {r s : E}
    (hr : r ∈ R) (hs : s ∈ R) (hrs : r ≠ s) (h : 0 < ⟪r, s⟫) : r - s ∈ R := by
  obtain ⟨n, hn⟩ := hR.2.2 s hs r hr
  obtain ⟨m, hm⟩ := hR.2.2 r hr s hs
  have hspos : 0 < ⟪s, s⟫ := real_inner_self_pos.mpr (fun h => hR.1 (h ▸ hs))
  have hrpos : 0 < ⟪r, r⟫ := real_inner_self_pos.mpr (fun h => hR.1 (h ▸ hr))
  rw [real_inner_comm r s] at hm
  have hnpos : 0 < n := by exact_mod_cast (hn ▸ div_pos (by positivity) hspos : 0 < (n : ℝ))
  have hmpos : 0 < m := by exact_mod_cast (hm ▸ div_pos (by positivity) hrpos : 0 < (m : ℝ))
  by_cases h1 : n = 1
  · have h' := hR.2.1 s hs r hr
    rwa [hn, h1, Int.cast_one, one_smul] at h'
  by_cases h2 : m = 1
  · have h' := hR.neg_mem (hR.2.1 r hr s hs)
    rw [real_inner_comm r s, hm, h2, Int.cast_one, one_smul, neg_sub] at h'
    exact h'
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show (2 : ℤ) ≤ n by omega)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show (2 : ℤ) ≤ m by omega)
  have hns := (le_div_iff₀ hspos).mp (hn.trans_ge hn2)
  have hmr := (le_div_iff₀ hrpos).mp (hm.trans_ge hm2)
  have hpos := real_inner_self_pos.mpr (sub_ne_zero.mpr hrs)
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm r s] at hpos
  linarith

/-- Indecomposables in a finite set of positive vectors. -/
def positiveSimple {V : Type*} [Add V] (S : Finset V) : Finset V :=
  S.filter fun v => ¬ ∃ u ∈ S, ∃ w ∈ S, v = u + w

@[simp] theorem mem_positiveSimple {V : Type*} [Add V] {S : Finset V} {v : V} :
    v ∈ positiveSimple S ↔ v ∈ S ∧ ¬ ∃ u ∈ S, ∃ w ∈ S, v = u + w := Finset.mem_filter

theorem simpleRoots_eq (a : Submodule ℝ E) (S : Finset E) :
    simpleRoots a S = positiveSimple (restrictedRoots a S) := by
  ext v
  simp [simpleRoots]

/-- Positive members of a finite set are sums of its positive indecomposables. -/
theorem positiveSimple_generates {V : Type*} [AddCommMonoid V] (S : Finset V)
    (f : V →+ ℝ) (hf : ∀ v ∈ S, 0 < f v) (v : V) (hv : v ∈ S) :
    ∃ c : positiveSimple S → ℕ, ∑ i, c i • (i : V) = v := by
  have hpos : Subtype.val '' {i : S | 0 < f i} = (S : Set V) := by
    ext x
    exact ⟨fun ⟨i, _, hi⟩ => hi ▸ i.property, fun hx => ⟨⟨x, hx⟩, hf x hx, rfl⟩⟩
  have hsimple : Subtype.val '' IsAddIndecomposable.baseOf ((↑) : S → V) f =
      (positiveSimple S : Set V) := by
    ext x
    simp only [Set.mem_image, Finset.mem_coe, mem_positiveSimple]
    constructor
    · rintro ⟨i, ⟨hi, h⟩, rfl⟩
      refine ⟨i.property, ?_⟩
      rintro ⟨y, hy, z, hz, he⟩
      rcases h ⟨y, hy⟩ (hf y hy) ⟨z, hz⟩ (hf z hz) he with hy0 | hz0
      · exact (ne_of_gt (hf y hy)) (congrArg f hy0 |>.trans (map_zero f))
      · exact (ne_of_gt (hf z hz)) (congrArg f hz0 |>.trans (map_zero f))
    · rintro ⟨hx, h⟩
      refine ⟨⟨x, hx⟩, ⟨hf x hx, ?_⟩, rfl⟩
      intro y _ z _ he
      exact (h ⟨y, y.property, z, z.property, he⟩).elim
  have hc := AddSubmonoid.closure_image_isAddIndecomposable_baseOf ((↑) : S → V) f
  rw [hpos, hsimple] at hc
  obtain ⟨c, hc'⟩ := AddSubmonoid.mem_closure_finset'.1 (hc.symm ▸ AddSubmonoid.subset_closure hv)
  exact ⟨c, hc'.symm⟩

omit [FiniteDimensional ℝ E] in
private theorem positiveSimple_posSet_independent (R : Finset E) (hR : IsRootSet R) (x : E)
    (hx : ∀ r ∈ R, ⟪r, x⟫ ≠ 0) :
    LinearIndependent ℝ (fun i : positiveSimple (posSet R x) => (i : E)) := by
  apply LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero (innerₗ E)
    (fun v hv => real_inner_self_pos.mpr hv) ((innerₗ E) x)
  · intro i
    rw [innerₗ_apply_apply, real_inner_comm]
    exact (mem_posSet.mp (mem_positiveSimple.mp i.property).1).2
  · intro i j hij
    change ⟪(i : E), (j : E)⟫ ≤ 0
    by_contra! h
    have hi := mem_positiveSimple.mp i.property
    have hj := mem_positiveSimple.mp j.property
    have him := mem_posSet.mp hi.1
    have hjm := mem_posSet.mp hj.1
    have hr := root_sub_mem hR him.1 hjm.1 (fun he => hij (Subtype.ext he)) h
    have hne : ⟪(i : E), x⟫ ≠ ⟪(j : E), x⟫ := fun he => hx _ hr (by rw [inner_sub_left, he, sub_self])
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hj.2 ⟨i, hi.1, (j : E) - (i : E),
        mem_posSet.mpr ⟨by simpa only [neg_sub] using hR.neg_mem hr,
          by rw [inner_sub_left]; linarith⟩, by abel⟩
    · exact hi.2 ⟨j, hj.1, (i : E) - (j : E),
        mem_posSet.mpr ⟨hr, by rw [inner_sub_left]; linarith⟩, by abel⟩

omit [FiniteDimensional ℝ E] in
/-- A small displacement along a line preserves all the strict root signs at its origin. -/
theorem exists_pos_perturb (R : Finset E) (x y : E) :
    ∃ t : ℝ, 0 < t ∧ ∀ r ∈ R,
      (0 < ⟪r, x⟫ → 0 < ⟪r, x + t • y⟫) ∧ (⟪r, x⟫ < 0 → ⟪r, x + t • y⟫ < 0) := by
  have h : ∀ r ∈ R, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (0 < ⟪r, x⟫ → 0 < ⟪r, x + t • y⟫) ∧ (⟪r, x⟫ < 0 → ⟪r, x + t • y⟫ < 0) := by
    intro r _
    have hc : ContinuousAt (fun t : ℝ => ⟪r, x + t • y⟫) 0 := by fun_prop
    have ht : Tendsto (fun t : ℝ => ⟪r, x + t • y⟫) (𝓝[>] (0 : ℝ)) (𝓝 ⟪r, x⟫) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    refine (eventually_imp_distrib_left.mpr ?_).and (eventually_imp_distrib_left.mpr ?_)
    · exact fun hp => ht.eventually (lt_mem_nhds hp)
    · exact fun hn => ht.eventually (gt_mem_nhds hn)
  have ht : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  exact (ht.and ((eventually_all_finset R).mpr h)).exists

theorem restrictedRoot_eq_zero_iff_forall_inner (a : Submodule ℝ E) (r : E) :
    restrictedRoot a r = 0 ↔ ∀ x ∈ a, ⟪r, x⟫ = 0 := by
  rw [restrictedRoot, Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.mem_orthogonal']

@[simp] theorem inner_restrictedRoot_subtype (a : Submodule ℝ E) (r : E) (x : a) :
    ⟪restrictedRoot a r, x⟫ = ⟪r, (x : E)⟫ :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right x r

/-- Regular points exist in every subspace of the finite arrangement. -/
theorem exists_isRegular (R : Finset E) (a : Submodule ℝ E) : ∃ p, IsRegular R a p := by
  induction R using Finset.induction_on with
  | empty => exact ⟨0, a.zero_mem, by simp⟩
  | @insert r S _ ih =>
    obtain ⟨p, hp, hreg⟩ := ih
    by_cases hr : restrictedRoot a r = 0 ∨ ⟪r, p⟫ ≠ 0
    · refine ⟨p, hp, ?_⟩
      intro x hx hx0
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hr.resolve_left hx0
      · exact hreg x hx hx0
    push Not at hr
    obtain ⟨t, ht, hsign⟩ := exists_pos_perturb S p (restrictedRoot a r : E)
    refine ⟨p + t • (restrictedRoot a r : E), a.add_mem hp (a.smul_mem t (Subtype.property _)), ?_⟩
    intro x hx hx0
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rw [inner_add_right, real_inner_smul_right, hr.2, zero_add]
      have hpos : 0 < ⟪x, (restrictedRoot a x : E)⟫ := by
        rw [← inner_restrictedRoot_subtype a x (restrictedRoot a x)]
        exact real_inner_self_pos.mpr hx0
      exact (mul_pos ht hpos).ne'
    · rcases lt_or_gt_of_ne (hreg x hx hx0) with h | h
      · exact ((hsign x hx).2 h).ne
      · exact ((hsign x hx).1 h).ne'

theorem mem_parabolics_iff {R : Finset E} {a : Submodule ℝ E} {P : Finset E} :
    P ∈ parabolics R a ↔ ∃ p, IsRegular R a p ∧ P = posSet R p := by
  simp only [parabolics, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨And.right, fun ⟨p, hp, he⟩ => ⟨he ▸ Finset.filter_subset _ _, p, hp, he⟩⟩

omit [FiniteDimensional ℝ E] in
theorem mem_faces_iff {R : Finset E} {a : Submodule ℝ E} {Q : Finset E} :
    Q ∈ faces R a ↔ ∃ q ∈ a, Q = posSet R q := by
  simp only [faces, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨And.right, fun ⟨q, hq, he⟩ => ⟨he ▸ Finset.filter_subset _ _, q, hq, he⟩⟩

theorem parabolics_subset_faces (R : Finset E) (a : Submodule ℝ E) :
    parabolics R a ⊆ faces R a := by
  intro P hP
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hP
  exact mem_faces_iff.mpr ⟨p, hp.1, rfl⟩

omit [FiniteDimensional ℝ E] in
@[simp] theorem mem_leviRoots_posSet {R : Finset E} (hR : IsRootSet R) {q r : E} :
    r ∈ leviRoots R (posSet R q) ↔ r ∈ R ∧ ⟪r, q⟫ = 0 := by
  simp only [leviRoots, Finset.mem_filter, mem_posSet, inner_neg_left]
  constructor
  · rintro ⟨hr, hp, hn⟩
    exact ⟨hr, le_antisymm (not_lt.mp fun h => hp ⟨hr, h⟩)
      (neg_nonpos.mp (not_lt.mp fun h => hn ⟨hR.neg_mem hr, h⟩))⟩
  · rintro ⟨hr, hq⟩
    simp [hr, hq]

omit [FiniteDimensional ℝ E] in
theorem mem_faceSpace_posSet {R : Finset E} (hR : IsRootSet R) (a : Submodule ℝ E) {q x : E} :
    x ∈ faceSpace R a (posSet R q) ↔ x ∈ a ∧ ∀ r ∈ R, ⟪r, q⟫ = 0 → ⟪r, x⟫ = 0 := by
  simp [faceSpace, Submodule.mem_iInf, Submodule.mem_orthogonal_singleton_iff_inner_right,
    mem_leviRoots_posSet hR, and_imp]

omit [FiniteDimensional ℝ E] in
private theorem mem_leviSpaceOf (R : Finset E) (p x : E) :
    x ∈ leviSpaceOf R p ↔ ∀ r ∈ R, ⟪r, p⟫ = 0 → ⟪r, x⟫ = 0 := by
  simp [leviSpaceOf, Submodule.mem_iInf, Submodule.mem_orthogonal_singleton_iff_inner_right, and_imp]

section PositiveProjection

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- After quotienting by the span of part of an independent family, the surviving vectors
remain linearly independent. -/
theorem linearIndependent_project {ι : Type*} {v : ι → V} (hv : LinearIndependent ℝ v)
    (f : V →ₗ[ℝ] W) (hf : f.ker ≤ Submodule.span ℝ (v '' {i | f (v i) = 0})) :
    LinearIndependent ℝ (fun i : {i // f (v i) ≠ 0} => f (v i)) := by
  have hd : Disjoint {i | f (v i) ≠ 0} {i | f (v i) = 0} := Set.disjoint_left.2 fun _ hn hz => hn hz
  have hspan := hv.disjoint_span_image hd
  rw [← Set.range_domRestrict] at hspan
  exact (hv.comp Subtype.val Subtype.val_injective).map (f := f) (hspan.mono_right hf)

omit [Module ℝ V] in
private theorem mem_positiveSimple_filter_zero (S : Finset V) (f : V →+ ℝ)
    (hf : ∀ v ∈ S, 0 ≤ f v) (v : V) :
    v ∈ positiveSimple (S.filter fun x => f x = 0) ↔ v ∈ positiveSimple S ∧ f v = 0 := by
  simp only [mem_positiveSimple, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hv, hz⟩, hd⟩
    refine ⟨⟨hv, ?_⟩, hz⟩
    rintro ⟨y, hy, z, hz', he⟩
    have hx : f y + f z = 0 := by rw [← map_add, ← he, hz]
    exact hd ⟨y, ⟨hy, by linarith [hf y hy, hf z hz']⟩,
      z, ⟨hz', by linarith [hf y hy, hf z hz']⟩, he⟩
  · rintro ⟨⟨hv, hd⟩, hz⟩
    refine ⟨⟨hv, hz⟩, ?_⟩
    rintro ⟨y, ⟨hy, _⟩, z, ⟨hz', _⟩, he⟩
    exact hd ⟨y, hy, z, hz', he⟩

omit [Module ℝ V] in
theorem positiveSimple_filter_zero (S : Finset V) (f : V →+ ℝ) (hf : ∀ v ∈ S, 0 ≤ f v) :
    positiveSimple (S.filter fun x => f x = 0) = (positiveSimple S).filter fun x => f x = 0 := by
  ext v
  rw [Finset.mem_filter]
  exact mem_positiveSimple_filter_zero S f hf v

/-- The indecomposable projected vectors are the nonzero images of the original
indecomposables when those images are independent. -/
theorem positiveSimple_image_erase_zero [DecidableEq W] (S : Finset V) (g : V →+ ℝ)
    (hg : ∀ v ∈ S, 0 < g v) (f : V →ₗ[ℝ] W)
    (hi : LinearIndependent ℝ (fun i : {i : positiveSimple S // f (i : V) ≠ 0} => f (i.1 : V))) :
    positiveSimple ((S.image f).erase 0) = ((positiveSimple S).image f).erase 0 := by
  let I := {i : positiveSimple S // f (i : V) ≠ 0}
  let v : I → W := fun i => f (i.1 : V)
  have hgen (w : W) (hw : w ∈ (S.image f).erase 0) : ∃ c : I → ℕ, ∑ j, c j • v j = w := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hw).2
    obtain ⟨c, hc⟩ := positiveSimple_generates S g hg x hx
    refine ⟨fun j => c j.1, ?_⟩
    rw [← hc, map_sum]
    simp only [map_nsmul]
    have hsum := Fintype.sum_subtype_add_sum_subtype (fun i : positiveSimple S => f (i : V) ≠ 0)
      (fun i => c i • f (i : V))
    have hz : (∑ j : {i : positiveSimple S // ¬ f (i : V) ≠ 0}, c j.1 • f (j.1 : V)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [not_ne_iff.mp j.property]
    simpa only [v, hz, add_zero] using hsum
  ext w
  simp only [mem_positiveSimple, Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨⟨hw0, x, hx, hxw⟩, hw⟩
    let preimages := S.filter fun y => f y = w
    obtain ⟨y, hy, hmin⟩ := preimages.exists_min_image g ⟨x, Finset.mem_filter.mpr ⟨hx, hxw⟩⟩
    obtain ⟨hyS, hyw⟩ := Finset.mem_filter.mp hy
    refine ⟨hw0, y, ⟨hyS, ?_⟩, hyw⟩
    rintro ⟨x₁, h₁, x₂, h₂, he⟩
    have hsum : w = f x₁ + f x₂ := by rw [← map_add, ← he, hyw]
    have hsmall₁ : g x₁ < g y := by rw [he, map_add]; linarith [hg x₂ h₂]
    have hsmall₂ : g x₂ < g y := by rw [he, map_add]; linarith [hg x₁ h₁]
    by_cases h0₁ : f x₁ = 0
    · rw [h0₁, zero_add] at hsum
      exact hsmall₂.not_ge (hmin x₂ (Finset.mem_filter.mpr ⟨h₂, hsum.symm⟩))
    by_cases h0₂ : f x₂ = 0
    · rw [h0₂, add_zero] at hsum
      exact hsmall₁.not_ge (hmin x₁ (Finset.mem_filter.mpr ⟨h₁, hsum.symm⟩))
    exact hw ⟨f x₁, ⟨h0₁, x₁, h₁, rfl⟩, f x₂, ⟨h0₂, x₂, h₂, rfl⟩, hsum⟩
  · rintro ⟨hw0, x, hx, rfl⟩
    refine ⟨⟨hw0, x, hx.1, rfl⟩, ?_⟩
    let i : I := ⟨⟨x, mem_positiveSimple.mpr hx⟩, hw0⟩
    rintro ⟨y, hy, z, hz, he⟩
    obtain ⟨c, hc⟩ := hgen y (by simpa only [Finset.mem_erase, Finset.mem_image] using hy)
    obtain ⟨d, hd⟩ := hgen z (by simpa only [Finset.mem_erase, Finset.mem_image] using hz)
    have hcoeff : ∀ j, c j + d j = if j = i then 1 else 0 := by
      intro j
      have hj := Fintype.linearIndependent_iffₛ.mp hi
        (fun k : I => ((c k + d k : ℕ) : ℝ)) (fun k : I => if k = i then 1 else 0) ?_ j
      · split_ifs at hj ⊢ <;> exact_mod_cast hj
      change (∑ k : I, ((c k + d k : ℕ) : ℝ) • v k) = ∑ k : I, (if k = i then (1 : ℝ) else 0) • v k
      simp only [Nat.cast_smul_eq_nsmul ℝ, add_nsmul, Finset.sum_add_distrib, hc, hd, ite_smul,
        one_smul, zero_smul]
      rw [Finset.sum_eq_single i]
      · simpa [v, i] using he.symm
      · intro j _ hj
        simp [hj]
      · simp
    have hother (j : I) (hj : j ≠ i) : c j = 0 ∧ d j = 0 := by
      simpa [hj] using hcoeff j
    have hii : c i + d i = 1 := by simpa using hcoeff i
    by_cases ci : c i = 0
    · have cz (j : I) : c j = 0 := if h : j = i then h ▸ ci else (hother j h).1
      exact hy.1 (by simpa [cz] using hc.symm)
    · have dz (j : I) : d j = 0 := by
        by_cases h : j = i
        · subst j
          omega
        · exact (hother j h).2
      exact hz.1 (by simpa [dz] using hd.symm)

end PositiveProjection

section PositiveChamber

omit [FiniteDimensional ℝ E] in
/-- Evaluation on a point, viewed as a real linear functional on the root vectors. -/
def rootEval (p : E) : E →ₗ[ℝ] ℝ := (innerₗ E) p

omit [FiniteDimensional ℝ E] in
@[simp] theorem rootEval_apply (p r : E) : rootEval p r = ⟪r, p⟫ := real_inner_comm r p

omit [FiniteDimensional ℝ E] in
theorem inner_eq_zero_of_mem_positiveSimple (S : Finset E) {p x : E}
    (hp : ∀ v ∈ S, 0 < ⟪v, p⟫) (hx : ∀ v ∈ positiveSimple S, ⟪v, x⟫ = 0)
    {r : E} (hr : r ∈ S) : ⟪r, x⟫ = 0 := by
  obtain ⟨c, hc⟩ := positiveSimple_generates S (rootEval p).toAddMonoidHom
    (by simpa only [LinearMap.toAddMonoidHom_coe, rootEval_apply] using hp) r hr
  rw [← rootEval_apply, ← hc, map_sum]
  simp [hx]

omit [FiniteDimensional ℝ E] in
/-- The span of positive roots vanishing on a face is generated by the simple roots vanishing
on that face. -/
theorem mem_orthogonal_span_zero_simple (S : Finset E) {p q x : E}
    (hp : ∀ v ∈ S, 0 < ⟪v, p⟫) (hq : ∀ v ∈ S, 0 ≤ ⟪v, q⟫) :
    x ∈ (Submodule.span ℝ {v | v ∈ positiveSimple S ∧ ⟪v, q⟫ = 0})ᗮ ↔
      ∀ v ∈ S, ⟪v, q⟫ = 0 → ⟪v, x⟫ = 0 := by
  rw [Submodule.mem_orthogonal]
  have hzero := positiveSimple_filter_zero S (rootEval q).toAddMonoidHom
    (by simpa only [LinearMap.toAddMonoidHom_coe, rootEval_apply] using hq)
  simp only [LinearMap.toAddMonoidHom_coe, rootEval_apply] at hzero
  constructor
  · intro h v hv hvq
    refine inner_eq_zero_of_mem_positiveSimple (S.filter fun r => ⟪r, q⟫ = 0)
      (p := p) (fun r hr => hp r (Finset.mem_filter.mp hr).1) ?_ (Finset.mem_filter.mpr ⟨hv, hvq⟩)
    intro r hr
    rw [hzero] at hr
    exact h r (Submodule.subset_span (Finset.mem_filter.mp hr))
  · intro h v hv
    have hle : Submodule.span ℝ {v | v ∈ positiveSimple S ∧ ⟪v, q⟫ = 0} ≤ (rootEval x).ker := by
      rw [Submodule.span_le]
      rintro r ⟨hr, hrq⟩
      simpa using h r (mem_positiveSimple.mp hr).1 hrq
    simpa using hle hv

/-- A point admits an ambient regular perturbation preserving its strict root signs. -/
theorem exists_ambient_regular (R : Finset E) (hR : IsRootSet R) {p : E} :
    ∃ x, (∀ r ∈ R, ⟪r, x⟫ ≠ 0) ∧ ∀ r ∈ R,
      (0 < ⟪r, p⟫ → 0 < ⟪r, x⟫) ∧ (⟪r, p⟫ < 0 → ⟪r, x⟫ < 0) := by
  obtain ⟨y, hy⟩ := exists_isRegular R (⊤ : Submodule ℝ E)
  obtain ⟨t, ht, hsign⟩ := exists_pos_perturb R p y
  refine ⟨p + t • y, ?_, hsign⟩
  intro r hr
  rcases lt_trichotomy ⟪r, p⟫ 0 with hn | hz | hp
  · exact ((hsign r hr).2 hn).ne
  · rw [inner_add_right, real_inner_smul_right, hz, zero_add]
    refine mul_ne_zero ht.ne' (hy.2 r hr ?_)
    intro h
    have h0 := (restrictedRoot_eq_zero_iff_forall_inner _ _).mp h r Submodule.mem_top
    exact hR.1 ((inner_self_eq_zero.mp h0) ▸ hr)
  · exact ((hsign r hr).1 hp).ne'

/-- The simple restricted roots of a regular chamber in a Levi flat are independent. -/
theorem simpleRoots_independent {R : Finset E} {a : Submodule ℝ E} (hR : IsRootSet R)
    (ha : IsLeviSpace R a) {P : Finset E} (hP : P ∈ parabolics R a) :
    LinearIndependent ℝ (fun i : simpleRoots a P => (i : a)) := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hP
  obtain ⟨x, hx, hsign⟩ := exists_ambient_regular R hR (p := p)
  let S := posSet R x
  let A := positiveSimple S
  let f := (a.orthogonalProjectionOnto : E →ₗ[ℝ] a)
  have hvanish (r : E) (hr : r ∈ R) : f r = 0 ↔ ⟪r, p⟫ = 0 := by
    exact ⟨fun h => (restrictedRoot_eq_zero_iff_forall_inner a r).mp h p hp.1,
      fun h => not_ne_iff.mp (fun hn => hp.2 r hr hn h)⟩
  have hspos : ∀ r ∈ S, 0 < ⟪r, x⟫ := fun _ hr => (mem_posSet.mp hr).2
  have hsnonneg : ∀ r ∈ S, 0 ≤ ⟪r, p⟫ := by
    intro r hr
    obtain ⟨hrR, hrx⟩ := mem_posSet.mp hr
    exact not_lt.mp fun hn => (hsign r hrR).2 hn |>.not_gt hrx
  have ha' : a = (Submodule.span ℝ {r | r ∈ A ∧ ⟪r, p⟫ = 0})ᗮ := by
    ext y
    rw [← leviSpaceOf_eq_of_isRegular ha hp, mem_leviSpaceOf, mem_orthogonal_span_zero_simple S hspos hsnonneg]
    refine ⟨fun h r hr => h r (mem_posSet.mp hr).1, ?_⟩
    intro h r hr hrp
    rcases lt_or_gt_of_ne (hx r hr) with ht | ht
    · have hn : -r ∈ S := mem_posSet.mpr ⟨hR.neg_mem hr, by simp [inner_neg_left, ht]⟩
      simpa only [inner_neg_left, neg_eq_zero] using h (-r) hn (by simp [inner_neg_left, hrp])
    · exact h r (mem_posSet.mpr ⟨hr, ht⟩) hrp
  have hfker : f.ker = Submodule.span ℝ (((↑) : A → E) '' {i | f (i : E) = 0}) := by
    change a.orthogonalProjectionOnto.ker = _
    rw [Submodule.ker_orthogonalProjectionOnto, show aᗮ = _ from
      (congrArg Submodule.orthogonal ha').trans (Submodule.orthogonal_orthogonal _)]
    congr 1
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    refine ⟨fun ⟨hr, hz⟩ => ⟨⟨r, hr⟩, (hvanish r (mem_posSet.mp (mem_positiveSimple.mp hr).1).1).mpr hz, rfl⟩, ?_⟩
    rintro ⟨i, hi, rfl⟩
    exact ⟨i.property, (hvanish _ (mem_posSet.mp (mem_positiveSimple.mp i.property).1).1).mp hi⟩
  have hi := linearIndependent_project (positiveSimple_posSet_independent R hR x hx) f hfker.le
  have hs : restrictedRoots a (posSet R p) = (S.image f).erase 0 := by
    ext v
    simp only [restrictedRoots, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨hrR, hrp⟩ := mem_posSet.mp hr
      exact ⟨fun h => hrp.ne' ((hvanish r hrR).mp h), r,
        mem_posSet.mpr ⟨hrR, (hsign r hrR).1 hrp⟩, rfl⟩
    · rintro ⟨hn, r, hr, rfl⟩
      have hrR := (mem_posSet.mp hr).1
      exact ⟨r, mem_posSet.mpr ⟨hrR, lt_of_le_of_ne (hsnonneg r hr)
        (fun he => hn ((hvanish r hrR).mpr he.symm))⟩, rfl⟩
  have he := positiveSimple_image_erase_zero S (rootEval x).toAddMonoidHom
    (by simpa only [LinearMap.toAddMonoidHom_coe, rootEval_apply] using hspos) f hi
  let v : {i : A // f (i : E) ≠ 0} → a := fun i => f (i.1 : E)
  have hrange : ∀ j : simpleRoots a (posSet R p), ∃ i, v i = (j : a) := by
    intro j
    have he' : simpleRoots a (posSet R p) = (A.image f).erase 0 := by
      rw [simpleRoots_eq, hs]
      exact he
    have hj : (j : a) ∈ (A.image f).erase 0 := he' ▸ j.property
    obtain ⟨h0, hr⟩ := Finset.mem_erase.mp hj
    obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hr
    exact ⟨⟨⟨r, hr⟩, heq ▸ h0⟩, heq⟩
  choose g hg using hrange
  have hg' : Function.Injective g := fun j k h => Subtype.ext ((hg j).symm.trans ((congrArg v h).trans (hg k)))
  convert hi.comp g hg' using 1
  exact (funext hg).symm

omit [FiniteDimensional ℝ E] in
/-- Chamber roots are nonnegative on any incident face. -/
theorem inner_nonneg_of_face_subset {R : Finset E} (hR : IsRootSet R) {p q r : E}
    (h : posSet R q ⊆ posSet R p) (hr : r ∈ posSet R p) : 0 ≤ ⟪r, q⟫ := by
  obtain ⟨hrR, hrp⟩ := mem_posSet.mp hr
  by_contra! hn
  have hnq : -r ∈ posSet R q := mem_posSet.mpr ⟨hR.neg_mem hrR, by simp [inner_neg_left, hn]⟩
  have hnp := (mem_posSet.mp (h hnq)).2
  rw [inner_neg_left] at hnp
  linarith

end PositiveChamber

end Langlands.GMFamily
