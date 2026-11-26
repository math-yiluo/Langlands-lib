import Langlands.LinearAlgebra.GMFamiliesRoots
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Faces and parameters of a Levi chamber -/

noncomputable section

open scoped RealInnerProductSpace
open Classical Module

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {R : Finset E} {a : Submodule ℝ E}

/-- Among chambers containing a regular chamber's positive roots, the only choice is that
chamber. -/
theorem parabolic_eq_of_subset (hR : IsRootSet R) {P P' : Finset E}
    (hP : P ∈ parabolics R a) (hP' : P' ∈ faces R a) (h : P ⊆ P') : P = P' := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hP
  obtain ⟨q, hq, rfl⟩ := mem_faces_iff.mp hP'
  apply Finset.Subset.antisymm h
  intro r hr
  obtain ⟨hrR, hrq⟩ := mem_posSet.mp hr
  have hr0 : restrictedRoot a r ≠ 0 := fun h0 => hrq.ne' ((restrictedRoot_eq_zero_iff_forall_inner a r).mp h0 q hq)
  refine mem_posSet.mpr ⟨hrR, ?_⟩
  rcases lt_or_gt_of_ne (hp.2 r hrR hr0) with hn | ht
  · have hnegP : -r ∈ posSet R p := mem_posSet.mpr ⟨hR.neg_mem hrR, by simp [inner_neg_left, hn]⟩
    have hneg := h hnegP
    have hnq := (mem_posSet.mp hneg).2
    rw [inner_neg_left] at hnq
    linarith
  · exact ht

omit [FiniteDimensional ℝ E] in
theorem faceSpace_le (Q : Finset E) : faceSpace R a Q ≤ a := inf_le_left

omit [FiniteDimensional ℝ E] in
theorem faceSpace_mono {Q Q' : Finset E} (h : Q' ⊆ Q) : faceSpace R a Q' ≤ faceSpace R a Q := by
  have hlevi : leviRoots R Q ⊆ leviRoots R Q' := by
    intro r hr
    simp only [leviRoots, Finset.mem_filter] at hr ⊢
    exact ⟨hr.1, fun h' => hr.2.1 (h h'), fun h' => hr.2.2 (h h')⟩
  refine inf_le_inf_left _ (le_iInf₂ fun r hr => ?_)
  exact iInf₂_le r (hlevi hr)

theorem faceSpace_parabolic (hR : IsRootSet R) {P : Finset E} (hP : P ∈ parabolics R a) :
    faceSpace R a P = a := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hP
  ext x
  rw [mem_faceSpace_posSet hR]
  exact ⟨And.left, fun hx => ⟨hx, fun r hr hz => (restrictedRoot_eq_zero_iff_forall_inner a r).mp
    (not_ne_iff.mp (fun hn => hp.2 r hr hn hz)) x hx⟩⟩

omit [FiniteDimensional ℝ E] in
theorem union_inter_leviRoots_of_subset {P Q : Finset E}
    (hP : ∃ p, P = posSet R p) (h : Q ⊆ P) : Q ∪ (P ∩ leviRoots R Q) = P := by
  obtain ⟨p, rfl⟩ := hP
  ext r
  simp only [Finset.mem_union, Finset.mem_inter]
  refine ⟨fun hr => hr.elim (fun hq => h hq) And.left, fun hr => ?_⟩
  by_cases hq : r ∈ Q
  · exact Or.inl hq
  refine Or.inr ⟨hr, Finset.mem_filter.mpr ⟨(mem_posSet.mp hr).1, hq, ?_⟩⟩
  intro hn
  have hn' := (mem_posSet.mp (h hn)).2
  rw [inner_neg_left] at hn'
  linarith [(mem_posSet.mp hr).2]

theorem inter_leviRoots_mem_parabolics {P Q : Finset E} (hP : P ∈ parabolics R a) :
    P ∩ leviRoots R Q ∈ parabolics (leviRoots R Q) a := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hP
  refine mem_parabolics_iff.mpr ⟨p, ⟨hp.1, fun r hr => hp.2 r (Finset.mem_filter.mp hr).1⟩, ?_⟩
  ext r
  simp only [Finset.mem_inter, mem_posSet]
  exact ⟨fun ⟨⟨_, ht⟩, hr⟩ => ⟨hr, ht⟩,
    fun ⟨hr, ht⟩ => ⟨⟨(Finset.mem_filter.mp hr).1, ht⟩, hr⟩⟩

/-- Perturbing a point of a face into a chamber of its Levi root arrangement extends that
chamber to a chamber above the face. -/
theorem union_mem_parabolics (hR : IsRootSet R) {Q S : Finset E} (hQ : Q ∈ faces R a)
    (hS : S ∈ parabolics (leviRoots R Q) a) : Q ∪ S ∈ parabolics R a := by
  obtain ⟨q, hq, rfl⟩ := mem_faces_iff.mp hQ
  obtain ⟨s, hs, rfl⟩ := mem_parabolics_iff.mp hS
  obtain ⟨t, ht, hsign⟩ := exists_pos_perturb R q s
  refine mem_parabolics_iff.mpr ⟨q + t • s, ⟨a.add_mem hq (a.smul_mem t hs.1), ?_⟩, ?_⟩
  · intro r hr hr0
    rcases lt_trichotomy ⟪r, q⟫ 0 with hn | hz | hp
    · exact ((hsign r hr).2 hn).ne
    · rw [inner_add_right, real_inner_smul_right, hz, zero_add]
      exact mul_ne_zero ht.ne' (hs.2 r ((mem_leviRoots_posSet hR).mpr ⟨hr, hz⟩) hr0)
    · exact ((hsign r hr).1 hp).ne'
  · ext r
    simp only [Finset.mem_union, mem_posSet, mem_leviRoots_posSet hR]
    by_cases hr : r ∈ R
    · simp only [hr, true_and]
      rcases lt_trichotomy ⟪r, q⟫ 0 with hn | hz | hp
      · simp [hn.not_gt, hn.ne, ((hsign r hr).2 hn).not_gt]
      · simp [hz, inner_add_right, real_inner_smul_right, ht]
      · simp [hp, (hsign r hr).1 hp]
    · simp [hr]

theorem union_inter_leviRoots_left {Q S : Finset E} (hS : S ∈ parabolics (leviRoots R Q) a) :
    (Q ∪ S) ∩ leviRoots R Q = S := by
  obtain ⟨s, _, rfl⟩ := mem_parabolics_iff.mp hS
  ext r
  simp only [Finset.mem_inter, Finset.mem_union, mem_posSet]
  constructor
  · rintro ⟨hr | hr, hl⟩
    · exact ((Finset.mem_filter.mp hl).2.1 hr).elim
    · exact hr
  · exact fun hr => ⟨Or.inr hr, hr.1⟩

/-- The chamber sum in the Levi of `Q`, indexed by the chambers incident to `Q`. -/
theorem cQM_eq_sum_chambers (hR : IsRootSet R) {Q : Finset E} (hQ : Q ∈ faces R a)
    (c : Finset E → StrongDual ℝ a → ℂ) (Λ : StrongDual ℝ a) :
    cQM R a c Q Λ = ∑ P ∈ (parabolics R a).filter (Q ⊆ ·),
      c P Λ * (theta a (P ∩ leviRoots R Q) Λ)⁻¹ := by
  unfold cQM
  refine Finset.sum_bij (fun S _ => Q ∪ S) (fun S hS => Finset.mem_filter.mpr
    ⟨union_mem_parabolics hR hQ hS, Finset.subset_union_left⟩) ?_ ?_ ?_
  · intro S hS T hT he
    rw [← union_inter_leviRoots_left hS, he, union_inter_leviRoots_left hT]
  · intro P hP
    have ⟨hch, hs⟩ := Finset.mem_filter.mp hP
    obtain ⟨p, _, hp⟩ := mem_parabolics_iff.mp hch
    exact ⟨P ∩ leviRoots R Q, inter_leviRoots_mem_parabolics hch,
      union_inter_leviRoots_of_subset ⟨p, hp⟩ hs⟩
  · intro S hS
    rw [union_inter_leviRoots_left hS]

section Parameter

variable {b b' : Submodule ℝ E}

theorem restrictedRoot_starProjection (h : b' ≤ b) (v : E) :
    restrictedRoot b' (b.starProjection v) = restrictedRoot b' v := by
  apply Subtype.ext
  exact DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le h) v

theorem restrictParam_apply_inclusion (h : b ≤ a) (Λ : StrongDual ℝ a) (v : b) :
    restrictParam a b Λ v = Λ (Submodule.inclusion h v) := by
  change Λ (a.orthogonalProjectionOnto (v : E)) = Λ (Submodule.inclusion h v)
  rw [show a.orthogonalProjectionOnto (v : E) = Submodule.inclusion h v from
    a.orthogonalProjectionOnto_mem_subspace_eq_self (Submodule.inclusion h v)]

theorem paramProj_apply_inclusion (h : b ≤ a) (Λ : StrongDual ℝ a) (v : a) :
    paramProj a b Λ v = Λ (Submodule.inclusion h (restrictedRoot b (v : E))) :=
  restrictParam_apply_inclusion h Λ (restrictedRoot b (v : E))

theorem restrictParam_paramProj (h : b ≤ a) (h' : b' ≤ b) (Λ : StrongDual ℝ a) :
    restrictParam a b' (paramProj a b Λ) = restrictParam a b' Λ := by
  ext v
  rw [restrictParam_apply_inclusion (h'.trans h), paramProj_apply_inclusion h,
    restrictParam_apply_inclusion (h'.trans h)]
  congr 1
  exact Subtype.ext (Submodule.starProjection_eq_self_iff.mpr (h' v.property))

theorem paramProj_paramProj (h : b ≤ a) (h' : b' ≤ b) (Λ : StrongDual ℝ a) :
    paramProj a b' (paramProj a b Λ) = paramProj a b' Λ := by
  ext v
  exact DFunLike.congr_fun (restrictParam_paramProj h h' Λ) (restrictedRoot b' (v : E))

@[simp] theorem paramProj_self (Λ : StrongDual ℝ a) : paramProj a a Λ = Λ := by
  ext v
  rw [paramProj_apply_inclusion le_rfl, restrictedRoot, a.orthogonalProjectionOnto_mem_subspace_eq_self]
  rfl

theorem famRestrict_paramProj (Λ : StrongDual ℝ a) (d : Finset E → StrongDual ℝ a → ℂ)
    {Q Q' : Finset E} (h : Q' ⊆ Q) :
    famRestrict R a d Q' (paramProj a (faceSpace R a Q) Λ) = famRestrict R a d Q' Λ := by
  unfold famRestrict
  split_ifs
  · rw [paramProj_paramProj (faceSpace_le Q) (faceSpace_mono h)]
  · rfl

theorem famRestrict_parabolic (hR : IsRootSet R) {P : Finset E} (hP : P ∈ parabolics R a)
    (d : Finset E → StrongDual ℝ a → ℂ) (Λ : StrongDual ℝ a) :
    famRestrict R a d P Λ = d P Λ := by
  have he : ∃ P' ∈ parabolics R a, P ⊆ P' := ⟨P, hP, Finset.Subset.refl _⟩
  have hi : P = he.choose := parabolic_eq_of_subset hR hP
    (parabolics_subset_faces R a he.choose_spec.1) he.choose_spec.2
  rw [famRestrict, dite_eq_left he, ← hi, faceSpace_parabolic hR hP, paramProj_self]

end Parameter

section FaceIndices

variable {P Q Q' : Finset E}

/-- A face incident to a chamber is indexed by the chamber's simple roots vanishing on it. -/
def faceIndices (a : Submodule ℝ E) (P Q : Finset E) : Finset (simpleRoots a P) :=
  Finset.univ.filter fun i => (i : a) ∉ restrictedRoots a Q

theorem faceIndices_subset (h : Q' ⊆ Q) : faceIndices a P Q ⊆ faceIndices a P Q' := by
  simp only [faceIndices, Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun _ hn hr => hn (Finset.image_mono (restrictedRoot a) h hr)

private theorem mem_restrictedRoots_posSet {q : a} {v : a} :
    v ∈ restrictedRoots a (posSet R (q : E)) ↔ v ∈ R.image (restrictedRoot a) ∧ 0 < ⟪v, q⟫ := by
  simp only [restrictedRoots, Finset.mem_image, mem_posSet]
  constructor
  · rintro ⟨r, ⟨hr, hpos⟩, rfl⟩
    exact ⟨⟨r, hr, rfl⟩, by simpa only [inner_restrictedRoot_subtype] using hpos⟩
  · rintro ⟨⟨r, hr, rfl⟩, hpos⟩
    exact ⟨r, ⟨hr, by simpa only [inner_restrictedRoot_subtype] using hpos⟩, rfl⟩

private theorem simple_mem_restrictedRoots (i : simpleRoots a P) : (i : a) ∈ restrictedRoots a P := by
  exact (Finset.mem_filter.mp i.property).1

private theorem simple_mem_root_image (hP : P ⊆ R) (i : simpleRoots a P) :
    (i : a) ∈ R.image (restrictedRoot a) := Finset.image_mono (restrictedRoot a) hP (simple_mem_restrictedRoots i)

theorem inner_nonneg_simpleRoots (hR : IsRootSet R) (hP : P ∈ parabolics R a) (q : a)
    (hQ : posSet R (q : E) ⊆ P) (i : simpleRoots a P) : 0 ≤ ⟪(i : a), q⟫ := by
  obtain ⟨p, _, rfl⟩ := mem_parabolics_iff.mp hP
  obtain ⟨r, hr, he⟩ := Finset.mem_image.mp (simple_mem_restrictedRoots i)
  rw [← he, inner_restrictedRoot_subtype]
  exact inner_nonneg_of_face_subset hR hQ hr

theorem mem_faceIndices_posSet (hR : IsRootSet R) (hP : P ∈ parabolics R a)
    (q : a) (hQ : posSet R (q : E) ⊆ P) (i : simpleRoots a P) :
    i ∈ faceIndices a P (posSet R (q : E)) ↔ ⟪(i : a), q⟫ = 0 := by
  have hPR : P ⊆ R := Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1
  simp only [faceIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_restrictedRoots_posSet, simple_mem_root_image hPR, not_lt]
  exact ⟨fun hi => le_antisymm hi (inner_nonneg_simpleRoots hR hP q hQ i), fun h => h.le⟩

/-- Each positive restricted root is a nonnegative integral combination of chamber simple
roots. -/
theorem restrictedRoot_eq_sum_simpleRoots (hP : P ∈ parabolics R a) {r : E} (hr : r ∈ P) :
    ∃ c : simpleRoots a P → ℕ, ∑ i, c i • (i : a) = restrictedRoot a r := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hP
  let p' : a := ⟨p, hp.1⟩
  rw [simpleRoots_eq]
  refine positiveSimple_generates _ (rootEval p').toAddMonoidHom ?_ _ (Finset.mem_image_of_mem _ hr)
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  simpa only [LinearMap.toAddMonoidHom_coe, rootEval_apply, inner_restrictedRoot_subtype] using (mem_posSet.mp hu).2

private theorem inner_eq_sum_simpleRoots (hP : P ∈ parabolics R a) {r : E} (hr : r ∈ P) :
    ∃ c : simpleRoots a P → ℕ, ∀ q : a,
      ⟪r, (q : E)⟫ = ∑ i, (c i : ℝ) * ⟪(i : a), q⟫ := by
  obtain ⟨c, hc⟩ := restrictedRoot_eq_sum_simpleRoots hP hr
  refine ⟨c, fun q => ?_⟩
  have he := congrArg (rootEval q) hc
  simp only [map_sum, ← Nat.cast_smul_eq_nsmul ℝ, map_smul, rootEval_apply, smul_eq_mul,
    inner_restrictedRoot_subtype] at he
  exact he.symm

/-- A point where all the simple roots of a regular chamber are nonnegative is incident to
that chamber. -/
theorem posSet_subset_of_simpleRoots_nonneg (hR : IsRootSet R) (hP : P ∈ parabolics R a)
    (q : a) (hq : ∀ i : simpleRoots a P, 0 ≤ ⟪(i : a), q⟫) : posSet R (q : E) ⊆ P := by
  obtain ⟨p, hp, hpeq⟩ := mem_parabolics_iff.mp hP
  intro r hr
  obtain ⟨hrR, hrq⟩ := mem_posSet.mp hr
  have hr0 : restrictedRoot a r ≠ 0 := fun h0 => hrq.ne'
    ((restrictedRoot_eq_zero_iff_forall_inner a r).mp h0 q q.property)
  rcases lt_or_gt_of_ne (hp.2 r hrR hr0) with hn | ht
  · have hnP : -r ∈ P := hpeq ▸ mem_posSet.mpr ⟨hR.neg_mem hrR, by simp [inner_neg_left, hn]⟩
    obtain ⟨c, hc⟩ := inner_eq_sum_simpleRoots hP hnP
    have hnn : 0 ≤ ⟪-r, (q : E)⟫ := hc q ▸ Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hq i)
    rw [inner_neg_left] at hnn
    linarith
  · exact hpeq ▸ mem_posSet.mpr ⟨hrR, ht⟩

private theorem inner_eq_zero_of_simple_zeros_subset (hP : P ∈ parabolics R a) {r : E} (hr : r ∈ P)
    (q x : a) (hq : ∀ i : simpleRoots a P, 0 ≤ ⟪(i : a), q⟫)
    (h : ∀ i : simpleRoots a P, ⟪(i : a), q⟫ = 0 → ⟪(i : a), x⟫ = 0)
    (hrq : ⟪r, (q : E)⟫ = 0) : ⟪r, (x : E)⟫ = 0 := by
  obtain ⟨c, hc⟩ := inner_eq_sum_simpleRoots hP hr
  have hi : ∀ i : simpleRoots a P, (c i : ℝ) * ⟪(i : a), q⟫ = 0 := by
    have hsum := (hc q).symm.trans hrq
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hq i))).mp
      hsum i (Finset.mem_univ i)
  rw [hc x]
  exact Finset.sum_eq_zero fun i _ => (mul_eq_zero.mp (hi i)).elim (fun hz => by rw [hz, zero_mul])
    (fun hz => by rw [h i hz, mul_zero])

theorem posSet_subset_of_faceIndices_subset (hR : IsRootSet R) (hP : P ∈ parabolics R a)
    (q q' : a) (hq : posSet R (q : E) ⊆ P) (hq' : posSet R (q' : E) ⊆ P)
    (h : faceIndices a P (posSet R (q : E)) ⊆ faceIndices a P (posSet R (q' : E))) :
    posSet R (q' : E) ⊆ posSet R (q : E) := by
  intro r hr
  have hrP := hq' hr
  have hnonneg : 0 ≤ ⟪r, (q : E)⟫ := by
    obtain ⟨p, _, hpeq⟩ := mem_parabolics_iff.mp hP
    exact inner_nonneg_of_face_subset hR (hpeq ▸ hq) (hpeq ▸ hrP)
  refine mem_posSet.mpr ⟨(mem_posSet.mp hr).1, lt_of_le_of_ne hnonneg ?_⟩
  intro he
  have he' := inner_eq_zero_of_simple_zeros_subset hP hrP q q'
    (inner_nonneg_simpleRoots hR hP q hq)
    (fun i hi => (mem_faceIndices_posSet hR hP q' hq' i).mp
      (h ((mem_faceIndices_posSet hR hP q hq i).mpr hi))) he.symm
  exact (mem_posSet.mp hr).2.ne' he'

/-- The interval of incident faces has the reverse order of the corresponding subsets of simple
roots. -/
theorem faceIndices_subset_iff (hR : IsRootSet R) (hP : P ∈ parabolics R a)
    (hQ : Q ∈ faces R a) (hQ' : Q' ∈ faces R a) (hQP : Q ⊆ P) (hQ'P : Q' ⊆ P) :
    faceIndices a P Q ⊆ faceIndices a P Q' ↔ Q' ⊆ Q := by
  obtain ⟨q, hq, rfl⟩ := mem_faces_iff.mp hQ
  obtain ⟨q', hq', rfl⟩ := mem_faces_iff.mp hQ'
  exact ⟨posSet_subset_of_faceIndices_subset hR hP ⟨q, hq⟩ ⟨q', hq'⟩ hQP hQ'P, faceIndices_subset⟩

/-- Every subset of the simple roots occurs as a vanishing set on an incident face. -/
theorem exists_faceIndices (hR : IsRootSet R) (ha : IsLeviSpace R a) (hP : P ∈ parabolics R a)
    (J : Finset (simpleRoots a P)) : ∃ Q ∈ faces R a, Q ⊆ P ∧ faceIndices a P Q = J := by
  let v : simpleRoots a P → a := Subtype.val
  let U : Submodule ℝ a := Submodule.span ℝ (Set.range v)
  let B : Basis (simpleRoots a P) ℝ U := Basis.span (simpleRoots_independent hR ha hP)
  let c (i : simpleRoots a P) : ℝ := if i ∈ J then 0 else 1
  let x : U := (InnerProductSpace.toDual ℝ U).symm (LinearMap.toContinuousLinearMap (B.constr ℝ c))
  let q : a := x
  have hq (i : simpleRoots a P) : ⟪(i : a), q⟫ = c i := by
    change ⟪v i, (x : a)⟫ = c i
    have he : (B i : a) = v i := Basis.coe_span_apply _ i
    rw [← he, ← Submodule.coe_inner, real_inner_comm x (B i)]
    change ⟪x, B i⟫ = c i
    rw [InnerProductSpace.toDual_symm_apply]
    simp
  have hQP := posSet_subset_of_simpleRoots_nonneg hR hP q (fun i => by rw [hq]; dsimp [c]; split <;> norm_num)
  refine ⟨posSet R (q : E), mem_faces_iff.mpr ⟨q, q.property, rfl⟩, hQP, ?_⟩
  ext i
  rw [mem_faceIndices_posSet hR hP q hQP i, hq]
  by_cases hi : i ∈ J <;> simp [c, hi]

/-- The ambient span of the simple roots indexed by `J`. -/
def chamberSpan (J : Finset (simpleRoots a P)) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun i : J => ((i.1 : a) : E))

theorem chamberSpan_le (J : Finset (simpleRoots a P)) : chamberSpan J ≤ a := by
  rw [chamberSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact (i.1 : a).property

omit [FiniteDimensional ℝ E] in
theorem mem_orthogonal_span_range {ι : Type*} (v : ι → E) (x : E) :
    x ∈ (Submodule.span ℝ (Set.range v))ᗮ ↔ ∀ i, ⟪v i, x⟫ = 0 := by
  rw [Submodule.mem_orthogonal]
  refine ⟨fun h i => h _ (Submodule.subset_span (Set.mem_range_self i)), ?_⟩
  intro h r hr
  have hle : Submodule.span ℝ (Set.range v) ≤ (rootEval x).ker := by
    rw [Submodule.span_le]
    rintro r ⟨i, rfl⟩
    simpa using h i
  simpa using hle hr

/-- The face space is the orthogonal complement in the Levi flat of its vanishing simple
roots. -/
theorem faceSpace_eq_chamberSpan_orthogonal (hR : IsRootSet R) (hP : P ∈ parabolics R a)
    (hQ : Q ∈ faces R a) (hQP : Q ⊆ P) :
    faceSpace R a Q = a ⊓ (chamberSpan (faceIndices a P Q))ᗮ := by
  obtain ⟨q, hq, rfl⟩ := mem_faces_iff.mp hQ
  let q' : a := ⟨q, hq⟩
  ext x
  rw [mem_faceSpace_posSet hR, Submodule.mem_inf, chamberSpan, mem_orthogonal_span_range]
  refine and_congr_right fun hx => ?_
  constructor
  · intro h i
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp (simple_mem_restrictedRoots i.1)
    have hrR : r ∈ R := Finset.mem_powerset.mp (Finset.mem_filter.mp hP).1 hr
    change ⟪((i.1 : a) : E), x⟫ = 0
    rw [← he]
    change ⟪restrictedRoot a r, (⟨x, hx⟩ : a)⟫ = 0
    rw [inner_restrictedRoot_subtype]
    apply h r hrR
    have hz := (mem_faceIndices_posSet hR hP q' hQP i.1).mp i.property
    rwa [← he, inner_restrictedRoot_subtype] at hz
  · intro h r hr hzero
    obtain ⟨p, hp, hpeq⟩ := mem_parabolics_iff.mp hP
    by_cases hr0 : restrictedRoot a r = 0
    · exact (restrictedRoot_eq_zero_iff_forall_inner a r).mp hr0 x hx
    have htest (s : E) (hs : s ∈ P) (hsq : ⟪s, q⟫ = 0) : ⟪s, x⟫ = 0 :=
      inner_eq_zero_of_simple_zeros_subset hP hs q' ⟨x, hx⟩
        (inner_nonneg_simpleRoots hR hP q' hQP)
        (fun i hi => h ⟨i, (mem_faceIndices_posSet hR hP q' hQP i).mpr hi⟩) hsq
    rcases lt_or_gt_of_ne (hp.2 r hr hr0) with hn | ht
    · have hnP : -r ∈ P := hpeq ▸ mem_posSet.mpr ⟨hR.neg_mem hr, by simp [inner_neg_left, hn]⟩
      simpa [inner_neg_left] using htest (-r) hnP (by simp [inner_neg_left, hzero])
    · exact htest r (hpeq ▸ mem_posSet.mpr ⟨hr, ht⟩) hzero

theorem finrank_faceSpace_add_card (hR : IsRootSet R) (ha : IsLeviSpace R a)
    (hP : P ∈ parabolics R a) (hQ : Q ∈ faces R a) (hQP : Q ⊆ P) :
    Module.finrank ℝ (faceSpace R a Q) + (faceIndices a P Q).card = Module.finrank ℝ a := by
  let J := faceIndices a P Q
  have hi : LinearIndependent ℝ (fun i : J => ((i.1 : a) : E)) := by
    refine ((simpleRoots_independent hR ha hP).comp _ Subtype.val_injective).map' a.subtype ?_
    exact LinearMap.ker_eq_bot.mpr Subtype.val_injective
  rw [faceSpace_eq_chamberSpan_orthogonal hR hP hQ hQP, inf_comm, add_comm]
  have hc : Module.finrank ℝ (chamberSpan J) = J.card := by
    rw [chamberSpan, finrank_span_eq_card hi, Fintype.card_coe]
  rw [← hc]
  exact Submodule.finrank_add_inf_finrank_orthogonal (chamberSpan_le J)

end FaceIndices

end Langlands.GMFamily
