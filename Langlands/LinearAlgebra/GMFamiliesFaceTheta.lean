import Langlands.LinearAlgebra.GMFamiliesFaces
import Langlands.LinearAlgebra.GMFamiliesTheta

/-! # Theta factors on a chamber interval -/

noncomputable section

open scoped RealInnerProductSpace Matrix
open Classical

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {R : Finset E} {a : Submodule ℝ E} {P Q Q' : Finset E}

@[simp] theorem faceIndices_self (a : Submodule ℝ E) (P : Finset E) : faceIndices a P P = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have h := (Finset.mem_filter.mp hi).2
  exact h (Finset.mem_filter.mp i.property).1

/-- The Levi simple roots in a chamber are exactly the simple roots vanishing on the face. -/
private theorem mem_leviSimple_iff (hR : IsRootSet R) (hP : P ∈ parabolics R a)
    (hQ : Q ∈ faces R a) (hQP : Q ⊆ P) (v : a) :
    v ∈ simpleRoots a (P ∩ leviRoots R Q) ↔
      ∃ i : faceIndices a P Q, (i.1 : a) = v := by
  obtain ⟨p, _, hp⟩ := mem_parabolics_iff.mp hP
  obtain ⟨q, hq, rfl⟩ := mem_faces_iff.mp hQ
  let q' : a := ⟨q, hq⟩
  let S := restrictedRoots a P
  have hres : restrictedRoots a (P ∩ leviRoots R (posSet R q)) = S.filter (fun u => ⟪u, q'⟫ = 0) := by
    ext u
    simp only [S, restrictedRoots, Finset.mem_image, Finset.mem_inter, Finset.mem_filter, mem_leviRoots_posSet hR]
    constructor
    · rintro ⟨r, ⟨hr, hrR, hz⟩, rfl⟩
      exact ⟨⟨r, hr, rfl⟩, by simpa only [inner_restrictedRoot_subtype] using hz⟩
    · rintro ⟨⟨r, hr, rfl⟩, hz⟩
      have hrR := (mem_posSet.mp (hp ▸ hr)).1
      exact ⟨r, ⟨hr, hrR, by simpa only [inner_restrictedRoot_subtype] using hz⟩, rfl⟩
  have hn : ∀ u ∈ S, 0 ≤ (rootEval q').toAddMonoidHom u := by
    intro u hu
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
    simpa only [LinearMap.toAddMonoidHom_coe, rootEval_apply, inner_restrictedRoot_subtype] using
      inner_nonneg_of_face_subset hR (hp ▸ hQP) (hp ▸ hr)
  have he := positiveSimple_filter_zero S (rootEval q').toAddMonoidHom hn
  simp only [LinearMap.toAddMonoidHom_coe, rootEval_apply] at he
  rw [simpleRoots_eq, hres, he, Finset.mem_filter]
  constructor
  · rintro ⟨hv, hz⟩
    let i : simpleRoots a P := ⟨v, (simpleRoots_eq a P).symm ▸ hv⟩
    exact ⟨⟨i, (mem_faceIndices_posSet hR hP q' hQP i).mpr hz⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨simpleRoots_eq a P ▸ i.1.property,
      (mem_faceIndices_posSet hR hP q' hQP i.1).mp i.property⟩

private def leviSimpleEquiv (hR : IsRootSet R) (hP : P ∈ parabolics R a)
    (hQ : Q ∈ faces R a) (hQP : Q ⊆ P) : faceIndices a P Q ≃ simpleRoots a (P ∩ leviRoots R Q) :=
  Equiv.ofBijective (fun i => ⟨(i.1 : a), (mem_leviSimple_iff hR hP hQ hQP (i.1 : a)).mpr ⟨i, rfl⟩⟩)
    ⟨fun i j h => Subtype.ext (Subtype.ext
      (congrArg (fun s : simpleRoots a (P ∩ leviRoots R Q) => (s : a)) h)),
      fun s => by
        obtain ⟨i, hi⟩ := (mem_leviSimple_iff hR hP hQ hQP (s : a)).mp s.property
        exact ⟨i, Subtype.ext hi⟩⟩

/-- The ordinary theta factor of the Levi slice uses the vanishing simple roots of the
ambient chamber. -/
theorem theta_inter_leviRoots (hR : IsRootSet R) (hP : P ∈ parabolics R a) (hQ : Q ∈ faces R a)
    (hQP : Q ⊆ P) (Λ : StrongDual ℝ a) :
    theta a (P ∩ leviRoots R Q) Λ = thetaOf a (fun i : faceIndices a P Q => (i.1 : a)) Λ := by
  exact (thetaOf_reindex a (leviSimpleEquiv hR hP hQ hQP) _ Λ).symm

private theorem orthogonal_face_inter (hR : IsRootSet R) (hP : P ∈ parabolics R a)
    (hQ : Q ∈ faces R a) (hQP : Q ⊆ P) :
    (faceSpace R a Q)ᗮ ⊓ a = chamberSpan (faceIndices a P Q) := by
  rw [faceSpace_eq_chamberSpan_orthogonal hR hP hQ hQP, inf_comm a]
  exact Submodule.orthogonal_inf_orthogonal_inf_of_le (chamberSpan_le _)

private theorem restrictedRoot_simple_eq_zero_iff (hR : IsRootSet R) (ha : IsLeviSpace R a)
    (hP : P ∈ parabolics R a) (hQ : Q ∈ faces R a) (hQP : Q ⊆ P) (i : simpleRoots a P) :
    restrictedRoot (faceSpace R a Q) ((i : a) : E) = 0 ↔ i ∈ faceIndices a P Q := by
  let J := faceIndices a P Q
  let v : simpleRoots a P → E := fun i => ((i : a) : E)
  have hv : LinearIndependent ℝ v := (simpleRoots_independent hR ha hP).map' a.subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have horth : (v i) ∈ (faceSpace R a Q)ᗮ ↔ (v i) ∈ chamberSpan J := by
    rw [← orthogonal_face_inter hR hP hQ hQP, Submodule.mem_inf]
    exact ⟨fun h => ⟨h, (i : a).property⟩, And.left⟩
  change (faceSpace R a Q).orthogonalProjectionOnto (v i) = 0 ↔ i ∈ J
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, horth]
  have he : chamberSpan J = Submodule.span ℝ (v '' (J : Set (simpleRoots a P))) := by
    unfold chamberSpan
    exact congrArg (Submodule.span ℝ) (Set.range_domRestrict v (J : Set _))
  rw [he]
  exact ⟨fun h => Classical.byContradiction fun hn => hv.notMem_span_image hn h,
    fun h => Submodule.subset_span ⟨i, h, rfl⟩⟩

private theorem projectedSimple_independent (hR : IsRootSet R) (ha : IsLeviSpace R a)
    (hP : P ∈ parabolics R a) (hQ : Q ∈ faces R a) (hQP : Q ⊆ P) (K : Finset (simpleRoots a P))
    (hK : Disjoint K (faceIndices a P Q)) :
    LinearIndependent ℝ (fun i : K => restrictedRoot (faceSpace R a Q) ((i.1 : a) : E)) := by
  let J := faceIndices a P Q
  let v : simpleRoots a P → E := fun i => ((i : a) : E)
  have hv : LinearIndependent ℝ v := (simpleRoots_independent hR ha hP).map' a.subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hd : Disjoint (chamberSpan K) (chamberSpan J) := by
    have hset : Disjoint (K : Set (simpleRoots a P)) (J : Set (simpleRoots a P)) := by simpa using hK
    have he (L : Finset (simpleRoots a P)) : chamberSpan L = Submodule.span ℝ (v '' (L : Set _)) :=
      congrArg (Submodule.span ℝ) (Set.range_domRestrict v (L : Set _))
    rw [he K, he J]
    exact hv.disjoint_span_image hset
  have hspan : Disjoint (chamberSpan K) (faceSpace R a Q)ᗮ := by
    apply Submodule.disjoint_def.mpr
    intro x hx h'x
    exact Submodule.disjoint_def.mp hd x hx
      (orthogonal_face_inter hR hP hQ hQP ▸ (show x ∈ (faceSpace R a Q)ᗮ ⊓ a from ⟨h'x, chamberSpan_le _ hx⟩))
  apply (hv.comp (fun i : K => i.1) Subtype.val_injective).map (f := (faceSpace R a Q).orthogonalProjectionOnto.toLinearMap)
  change Disjoint (chamberSpan K) (faceSpace R a Q).orthogonalProjectionOnto.ker
  simpa only [Submodule.ker_orthogonalProjectionOnto] using hspan

private theorem mem_projected_leviSimple_iff (hR : IsRootSet R) (ha : IsLeviSpace R a)
    (hP : P ∈ parabolics R a) (hQ : Q ∈ faces R a) (hQ' : Q' ∈ faces R a) (hQP : Q ⊆ P)
    (hQQ' : Q' ⊆ Q) (v : faceSpace R a Q) :
    v ∈ simpleRoots (faceSpace R a Q) (Q ∩ leviRoots R Q') ↔
      ∃ i : ↥(faceIndices a P Q' \ faceIndices a P Q),
        restrictedRoot (faceSpace R a Q) ((i.1 : a) : E) = v := by
  let I := faceIndices a P Q'
  let J := faceIndices a P Q
  let K := I \ J
  let b := faceSpace R a Q
  let S := restrictedRoots a (P ∩ leviRoots R Q')
  let f : a →ₗ[ℝ] b := b.orthogonalProjectionOnto.toLinearMap.comp a.subtype
  have hpre (i : positiveSimple S) : ∃ j : I, (j.1 : a) = (i : a) := by
    have hi : (i : a) ∈ simpleRoots a (P ∩ leviRoots R Q') := (simpleRoots_eq a _).symm ▸ i.property
    exact (mem_leviSimple_iff hR hP hQ' (hQQ'.trans hQP) _).mp hi
  let u : K → b := fun i => restrictedRoot b ((i.1 : a) : E)
  have hu : LinearIndependent ℝ u := projectedSimple_independent hR ha hP hQ hQP K
    (Finset.disjoint_left.mpr fun _ hK hJ => (Finset.mem_sdiff.mp hK).2 hJ)
  have hfind (i : {i : positiveSimple S // f (i : a) ≠ 0}) : ∃ k : K, (k.1 : a) = (i.1 : a) := by
    obtain ⟨j, hj⟩ := hpre i.1
    have hn : j.1 ∉ J := fun hm => i.property (by
      change restrictedRoot b (((i.1 : a) : E)) = 0
      rw [← hj]
      exact (restrictedRoot_simple_eq_zero_iff hR ha hP hQ hQP j.1).mpr hm)
    exact ⟨⟨j.1, Finset.mem_sdiff.mpr ⟨j.property, hn⟩⟩, hj⟩
  choose g hg using hfind
  have hgi : Function.Injective g := by
    intro i j h
    exact Subtype.ext (Subtype.ext ((hg i).symm.trans ((congrArg (fun k : K => (k.1 : a)) h).trans (hg j))))
  have hi : LinearIndependent ℝ (fun i : {i : positiveSimple S // f (i : a) ≠ 0} => f (i.1 : a)) := by
    have hf : (fun i : {i : positiveSimple S // f (i : a) ≠ 0} => f (i.1 : a)) = u ∘ g := by
      funext i
      change restrictedRoot b ((i.1 : a) : E) = restrictedRoot b (((g i).1 : a) : E)
      rw [hg]
    rw [hf]
    exact hu.comp g hgi
  obtain ⟨p, hp, hpeq⟩ := mem_parabolics_iff.mp hP
  let p' : a := ⟨p, hp.1⟩
  have hpos : ∀ x ∈ S, 0 < (rootEval p').toAddMonoidHom x := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    simpa only [LinearMap.toAddMonoidHom_coe, rootEval_apply, inner_restrictedRoot_subtype] using
      (mem_posSet.mp (hpeq ▸ (Finset.mem_inter.mp hr).1)).2
  have hproj (r : E) : f (restrictedRoot a r) = restrictedRoot b r := restrictedRoot_starProjection (faceSpace_le Q) r
  have hres : restrictedRoots b (Q ∩ leviRoots R Q') = (S.image f).erase 0 := by
    obtain ⟨q, hq, hqeq⟩ := mem_faces_iff.mp hQ
    have hqb : q ∈ b := by
      change q ∈ faceSpace R a Q
      exact hqeq ▸ (mem_faceSpace_posSet hR a).mpr ⟨hq, fun _ _ h => h⟩
    ext x
    simp only [restrictedRoots, S, Finset.mem_erase, Finset.mem_image, Finset.mem_inter]
    constructor
    · rintro ⟨r, ⟨hr, hrl⟩, rfl⟩
      have hrq := (mem_posSet.mp (hqeq ▸ hr)).2
      refine ⟨fun hn => hrq.ne' ((restrictedRoot_eq_zero_iff_forall_inner b r).mp hn q hqb),
        restrictedRoot a r, ⟨r, ⟨hQP hr, hrl⟩, rfl⟩, hproj r⟩
    · rintro ⟨hx, _, ⟨r, ⟨hr, hrl⟩, rfl⟩, rfl⟩
      rw [hproj r] at hx ⊢
      refine ⟨r, ⟨?_, hrl⟩, rfl⟩
      have hrp := mem_posSet.mp (hpeq ▸ hr)
      have hnonneg := inner_nonneg_of_face_subset hR (hpeq ▸ hqeq ▸ hQP) (hpeq ▸ hr)
      refine hqeq ▸ mem_posSet.mpr ⟨hrp.1, lt_of_le_of_ne hnonneg (fun hz => hx ?_)⟩
      refine (restrictedRoot_eq_zero_iff_forall_inner b r).mpr fun y hy => ?_
      have hy' : y ∈ faceSpace R a (posSet R q) := by
        change y ∈ faceSpace R a Q at hy
        exact hqeq ▸ hy
      exact ((mem_faceSpace_posSet hR a).mp hy').2 r hrp.1 hz.symm
  have hsimp := positiveSimple_image_erase_zero S (rootEval p').toAddMonoidHom hpos f hi
  change v ∈ simpleRoots b (Q ∩ leviRoots R Q') ↔ ∃ i : K, u i = v
  rw [simpleRoots_eq, hres, hsimp, Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hv, x, hx, rfl⟩
    let i : {i : positiveSimple S // f (i : a) ≠ 0} := ⟨⟨x, hx⟩, hv⟩
    exact ⟨g i, congrArg f (hg i)⟩
  · rintro ⟨k, rfl⟩
    have hk := Finset.mem_sdiff.mp k.property
    let j : I := ⟨k.1, hk.1⟩
    refine ⟨fun hz => hk.2 ((restrictedRoot_simple_eq_zero_iff hR ha hP hQ hQP k.1).mp hz), (k.1 : a), ?_, rfl⟩
    have hm := (mem_leviSimple_iff hR hP hQ' (hQQ'.trans hQP) (k.1 : a)).mpr ⟨j, rfl⟩
    exact simpleRoots_eq a _ ▸ hm

set_option maxHeartbeats 450000 in
/-- On a face interval, the hatted factor uses the duals of the complementary simple roots
inside the larger Levi root span. -/
theorem thetaHat_face_leviRoots (hR : IsRootSet R) (ha : IsLeviSpace R a)
    (hP : P ∈ parabolics R a) (hQ : Q ∈ faces R a) (hQ' : Q' ∈ faces R a) (hQP : Q ⊆ P)
    (hQQ' : Q' ⊆ Q) (Λ : StrongDual ℝ a) :
    thetaHat (Q ∩ leviRoots R Q') (restrictParam a (faceSpace R a Q) Λ) =
      thetaOf a (fun i : ↥(faceIndices a P Q' \ faceIndices a P Q) =>
        gramDual (fun j : faceIndices a P Q' => (j.1 : a)) ⟨i.1, (Finset.mem_sdiff.mp i.property).1⟩) Λ := by
  let I := faceIndices a P Q'
  let J := faceIndices a P Q
  let K := I \ J
  let b := faceSpace R a Q
  let T := Q ∩ leviRoots R Q'
  let v : I → a := fun i => (i.1 : a)
  let u : K → b := fun i => restrictedRoot b ((i.1 : a) : E)
  let kI (i : K) : I := ⟨i.1, (Finset.mem_sdiff.mp i.property).1⟩
  let w (i : K) : a := gramDual v (kI i)
  have hJI : J ⊆ I := faceIndices_subset hQQ'
  have hv : LinearIndependent ℝ v := (simpleRoots_independent hR ha hP).comp _ Subtype.val_injective
  have hu : LinearIndependent ℝ u := projectedSimple_independent hR ha hP hQ hQP K
    (Finset.disjoint_left.mpr fun _ hk hj => (Finset.mem_sdiff.mp hk).2 hj)
  have hw (i : K) : (w i : E) ∈ b := by
    change (w i : E) ∈ faceSpace R a Q
    rw [faceSpace_eq_chamberSpan_orthogonal hR hP hQ hQP, Submodule.mem_inf, chamberSpan,
      mem_orthogonal_span_range]
    refine ⟨(w i).property, fun j => ?_⟩
    let jI : I := ⟨j.1, hJI j.property⟩
    change ⟪v jI, gramDual v (kI i)⟫ = 0
    rw [real_inner_comm (gramDual v (kI i)) (v jI)]
    exact inner_gramDual_ne v hv (fun e => (Finset.mem_sdiff.mp i.property).2
      (show i.1 ∈ J from (congrArg (fun j : I => j.1) e).symm ▸ j.property))
  let wb (i : K) : b := ⟨(w i : E), hw i⟩
  let f : a →ₗ[ℝ] b := b.orthogonalProjectionOnto.toLinearMap.comp a.subtype
  have hfw (i : K) : f (w i) = wb i :=
    b.orthogonalProjectionOnto_mem_subspace_eq_self (wb i)
  have hpair (i j : K) : ⟪wb i, u j⟫ = ⟪gramDual v (kI i), v (kI j)⟫ := by
    change ⟪wb i, b.orthogonalProjectionOnto ((j.1 : a) : E)⟫ = _
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    rfl
  have hdual (i : K) : wb i = gramDual u i := by
    apply eq_gramDual_of_pairings u hu i
    · rw [← hfw i]
      change f (gramDual v (kI i)) ∈ _
      rw [gramDual, map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [map_smul]
      apply Submodule.smul_mem
      by_cases hj : j.1 ∈ J
      · have hzero : f (v j) = 0 := (restrictedRoot_simple_eq_zero_iff hR ha hP hQ hQP j.1).mpr hj
        rw [hzero]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨j.1, Finset.mem_sdiff.mpr ⟨j.property, hj⟩⟩, rfl⟩
    · exact (hpair i i).trans (inner_gramDual_self v hv (kI i))
    · intro j hij
      exact (hpair i j).trans (inner_gramDual_ne v hv
        (fun h => hij (Subtype.ext (congrArg (fun j : I => j.1) h))))
  have hex (s : b) : s ∈ simpleRoots b T ↔ ∃ i : K, u i = s :=
    mem_projected_leviSimple_iff hR ha hP hQ hQ' hQP hQQ' s
  let e : K ≃ simpleRoots b T := Equiv.ofBijective (fun i => ⟨u i, (hex _).mpr ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => hu.injective (congrArg (fun s : simpleRoots b T => (s : b)) h),
      fun s => by obtain ⟨i, hi⟩ := (hex (s : b)).mp s.property; exact ⟨i, Subtype.ext hi⟩⟩
  let t : simpleRoots b T → b := Subtype.val
  have ht : LinearIndependent ℝ t := by
    have h : t = u ∘ e.symm := by
      funext s
      change (s : b) = (e (e.symm s) : b)
      rw [Equiv.apply_symm_apply]
    rw [h]
    exact hu.comp e.symm e.symm.injective
  let Λb := restrictParam a b Λ
  change thetaHat T Λb = thetaOf a w Λ
  rw [thetaHat_eq_thetaOf_gramDual, ← thetaOf_reindex b e (gramDual t) Λb]
  have hw' : (fun i => gramDual t (e i)) = wb := by
    funext i
    rw [hdual i]
    exact (gramDual_reindex e t ht i).symm
  rw [hw']
  have hwb (i : K) : Λb (wb i) = Λ (w i) := restrictParam_apply_inclusion (faceSpace_le Q) Λ (wb i)
  simp only [thetaOf, hwb]
  rfl

end Langlands.GMFamily
