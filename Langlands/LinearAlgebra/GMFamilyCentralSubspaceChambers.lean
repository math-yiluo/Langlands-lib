import Langlands.LinearAlgebra.GMFamilySliceCoarse
import Langlands.LinearAlgebra.GMFamilyCentralSubspaceVertices

/-! # Coarse chambers and the affine vertex sum -/

noncomputable section

open scoped RealInnerProductSpace
open Classical Module Submodule
open Langlands.LinearAlgebra.AffineVertexWeights

namespace Langlands.GMFamily.CentralSubspaceDescent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {R : Finset E} {a a₁ : Submodule ℝ E} {ξ : E} {P S : Finset E}

/-- The nonzero projected simple roots of a fine extension biject with the coarse simple roots. -/
theorem exists_coarseSimpleEquiv (D : DescentPosition R a a₁ ξ) (ha : IsLeviSpace R a)
    (hS : S ∈ parabolics R a) (hP : P ∈ parabolics R a₁) (hSP : S ⊆ P) :
    ∃ e : nonzeroSliceIndices R a a₁ P ≃ simpleRoots a S,
      ∀ i : nonzeroSliceIndices R a a₁ P,
        ((sliceNormal R a a₁ i.val : noncentral R a) : E) = ((e i : a) : E) := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hS
  obtain ⟨q, hq, rfl⟩ := mem_parabolics_iff.mp hP
  have hpa₁ : p ∈ a₁ := D.le_fine hp.1
  obtain ⟨h, hh, hqh⟩ := exists_regular_ambient_chamber D.roots q
  have hc := closure_of_positive_subset D.roots hP hSP
  have hph : p ∈ chamberClosure R h := by
    intro r hr
    have hrR := (mem_posSet_iff.mp hr).1
    by_cases hr1 : restrictedRoot a₁ r = 0
    · rw [pairing_zero_of_projection_zero hr1 hpa₁]
    · exact hc r (mem_posSet_iff.mpr ⟨hrR, lt_of_le_of_ne (hqh r hr) (hq.2 r hrR hr1).symm⟩)
  have ha := (leviSpaceOf_eq_of_isRegular ha hp).symm
  have ha₁ := (leviSpaceOf_eq_of_isRegular D.fine hq).symm
  let B := positiveSimpleRoots R h
  let T := B.filter (fun x => ⟪x, p⟫ ≠ 0)
  let T₁ := B.filter (fun x => ⟪x, q⟫ ≠ 0)
  let J := nonzeroSliceIndices R a a₁ (posSet R q)
  have hcoarse := simpleRoots_posSet_eq_image D.roots hh hph ha
  have hfine := simpleRoots_posSet_eq_image D.roots hh hqh ha₁
  have hfine_lift (i : simpleRoots a₁ (posSet R q)) :
      ∃ r ∈ T₁, restrictedRoot a₁ r = (i : a₁) := by
    have hi : (i : a₁) ∈ T₁.image (restrictedRoot a₁) :=
      (congrArg (fun s : Finset a₁ => (i : a₁) ∈ s) hfine).mp i.prop
    exact Finset.mem_image.mp hi
  have hcompat (i : simpleRoots a₁ (posSet R q)) {r : E} (he : restrictedRoot a₁ r = (i : a₁)) :
      restrictedRoot a ((i : a₁) : E) = restrictedRoot a r := by
    rw [← he, restrictedRoot_nested D.le_fine]
  have hmem (i : J) : restrictedRoot a ((i.val : a₁) : E) ∈ simpleRoots a (posSet R p) := by
    obtain ⟨r, hr, he⟩ := hfine_lift i.val
    have hB := (Finset.mem_filter.mp hr).1
    have hRr := (mem_posSet_iff.mp (Finset.mem_filter.mp hB).1).1
    have hrp : ⟪r, p⟫ ≠ 0 := by
      intro h0
      have hproj := restrictedRoot_eq_zero_of_pairing_eq_zero ha hRr h0
      exact (mem_nonzeroSliceIndices_iff.mp i.prop)
        ((sliceNormal_eq_zero_iff D hP i.val).mpr ((hcompat i.val he).trans hproj))
    rw [hcoarse, hcompat i.val he]
    exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hB, hrp⟩, rfl⟩
  let f (i : J) : simpleRoots a (posSet R p) := ⟨restrictedRoot a ((i.val : a₁) : E), hmem i⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    obtain ⟨ri, hri, hei⟩ := hfine_lift i.val
    obtain ⟨rj, hrj, hej⟩ := hfine_lift j.val
    have hm (k : J) {r : E} (hr : r ∈ T₁) (he : restrictedRoot a₁ r = (k.val : a₁)) : r ∈ T := by
      have hB := (Finset.mem_filter.mp hr).1
      have hRr := (mem_posSet_iff.mp (Finset.mem_filter.mp hB).1).1
      refine Finset.mem_filter.mpr ⟨hB, fun hz => (mem_nonzeroSliceIndices_iff.mp k.prop) ?_⟩
      exact (sliceNormal_eq_zero_iff D hP k.val).mpr ((hcompat k.val he).trans
        (restrictedRoot_eq_zero_of_pairing_eq_zero ha hRr hz))
    have heq : restrictedRoot a ri = restrictedRoot a rj := by
      have heq' := congrArg (fun x : simpleRoots a (posSet R p) => (x : a)) hij
      change restrictedRoot a ((i.val : a₁) : E) = restrictedRoot a ((j.val : a₁) : E) at heq'
      rwa [hcompat i.val hei, hcompat j.val hej] at heq'
    have heqr : ri = rj := congrArg Subtype.val
      ((linearIndependent_projected_positiveSimpleRoots D.roots hh hph ha).injective
        (show restrictedRoot a ((⟨ri, hm i hri hei⟩ : T) : E) =
          restrictedRoot a ((⟨rj, hm j hrj hej⟩ : T) : E) from heq))
    exact Subtype.ext (Subtype.ext (hei.symm.trans (heqr ▸ hej)))
  have hfsurj : Function.Surjective f := by
    intro b
    have hb : (b : a) ∈ T.image (restrictedRoot a) :=
      (congrArg (fun s : Finset a => (b : a) ∈ s) hcoarse).mp b.prop
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hb
    obtain ⟨hB, hrp⟩ := Finset.mem_filter.mp hr
    have hrR := (mem_posSet_iff.mp (Finset.mem_filter.mp hB).1).1
    have hrq : ⟪r, q⟫ ≠ 0 := fun hz => hrp (pairing_zero_of_projection_zero
      (restrictedRoot_eq_zero_of_pairing_eq_zero ha₁ hrR hz) hpa₁)
    let i : simpleRoots a₁ (posSet R q) := ⟨restrictedRoot a₁ r,
      hfine ▸ Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hB, hrq⟩, rfl⟩⟩
    have hi : i ∈ J := mem_nonzeroSliceIndices_iff.mpr fun hzero => hrp
      (pairing_zero_of_projection_zero ((hcompat i rfl).symm.trans
        ((sliceNormal_eq_zero_iff D hP i).mp hzero)) hp.1)
    exact ⟨⟨i, hi⟩, Subtype.ext ((hcompat i rfl).trans he)⟩
  refine ⟨Equiv.ofBijective f ⟨hfinj, hfsurj⟩, fun i => ?_⟩
  exact coe_sliceNormal_eq_restrictedRoot D hP i.val

/-- In a fine extension, the nonzero projected normals give the unique candidate basis. -/
def coarseSliceBasis (D : DescentPosition R a a₁ ξ) (ha : IsLeviSpace R a)
    (hS : S ∈ parabolics R a) (hP : P ∈ parabolics R a₁) (hSP : S ⊆ P) :
    BasisIndex (sliceNormal R a a₁ (P := P)) := by
  let J := nonzeroSliceIndices R a a₁ P
  let v : J → noncentral R a := fun i => sliceNormal R a a₁ i.val
  let e := (exists_coarseSimpleEquiv D ha hS hP hSP).choose
  have he := (exists_coarseSimpleEquiv D ha hS hP hSP).choose_spec
  have hfun : (noncentral R a).subtype ∘ v = (fun b : simpleRoots a S => ((b : a) : E)) ∘ e :=
    funext he
  have hB := simpleRoots_basis D.roots ha hS
  have hli : LinearIndependent ℝ v := LinearIndependent.of_comp (noncentral R a).subtype
    (by rw [hfun]; exact hB.1.comp e e.injective)
  have hs : (span ℝ (Set.range v)).map (noncentral R a).subtype = noncentral R a := by
    rw [Submodule.map_span, ← Set.range_comp, hfun, e.surjective.range_comp, hB.2]
  have hsp : span ℝ (Set.range v) = ⊤ :=
    (Submodule.map_injective_of_injective (noncentral R a).injective_subtype) (by simpa using hs)
  let b : Basis J ℝ (noncentral R a) := Basis.mk hli hsp.ge
  exact ⟨J, hli, by simpa using (finrank_eq_card_basis b).symm⟩

theorem eq_coarseSliceBasis (D : DescentPosition R a a₁ ξ) (ha : IsLeviSpace R a)
    (hS : S ∈ parabolics R a) (hP : P ∈ parabolics R a₁) (hSP : S ⊆ P)
    (J : BasisIndex (sliceNormal R a a₁ (P := P))) : J = coarseSliceBasis D ha hS hP hSP := by
  let J₀ := coarseSliceBasis D ha hS hP hSP
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    exact mem_nonzeroSliceIndices_iff.mpr (J.prop.1.ne_zero ⟨i, hi⟩)
  · exact (J₀.prop.2.trans J.prop.2.symm).le

theorem vertexSum_eq_of_coarse_extension (D : DescentPosition R a a₁ ξ) (ha : IsLeviSpace R a)
    (hS : S ∈ parabolics R a) (hP : P ∈ parabolics R a₁) (hSP : S ⊆ P) (Λ : StrongDual ℝ a) :
    vertexSum (sliceNormal R a a₁ (P := P)) (sliceParameter R Λ) (sliceOffset ξ) =
      if isSliceLift R a a₁ ξ S P then (theta a S Λ)⁻¹ else 0 := by
  let J := coarseSliceBasis D ha hS hP hSP
  unfold vertexSum
  rw [Finset.sum_eq_single J]
  · have hcond : (∀ j ∉ J.val, 0 < J.slack j (sliceOffset ξ)) ↔ isSliceLift R a a₁ ξ S P := by
      have hzero (i : simpleRoots a₁ P) : i ∉ J.val ↔ sliceNormal R a a₁ i = 0 :=
        (not_congr mem_nonzeroSliceIndices_iff).trans not_ne_iff
      refine ⟨fun h => ⟨hSP, fun i hi => ?_⟩, fun h i hi => ?_⟩
      · have he := h i ((hzero i).mpr hi)
        rwa [slack_of_normal_eq_zero J hi] at he
      · have hz := (hzero i).mp hi
        rw [slack_of_normal_eq_zero J hz]
        exact h.2 i hz
    simp only [hcond]
    congr 1
    rw [theta_inv_eq_gram_div]
    let e := (exists_coarseSimpleEquiv D ha hS hP hSP).choose
    have he := (exists_coarseSimpleEquiv D ha hS hP hSP).choose_spec
    have hv : gramVolume (fun i : J.val => sliceNormal R a a₁ i.val) =
        gramVolume (fun j : simpleRoots a S => ((j : a) : E)) := by
      rw [← gramVolume_subtype (noncentral R a), ← gramVolume_reindex e]
      exact congrArg gramVolume (funext he)
    have hp : (∏ i ∈ J.val, sliceParameter R Λ (sliceNormal R a a₁ i)) =
        ∏ j : simpleRoots a S, (Complex.I * (Λ (j : a) : ℂ)) := by
      rw [← Finset.prod_coe_sort]
      apply Fintype.prod_equiv e
      intro i
      change Complex.I * (Λ (Submodule.inclusion inf_le_left (sliceNormal R a a₁ i.val)) : ℂ) = _
      rw [show Submodule.inclusion inf_le_left (sliceNormal R a a₁ i.val) = (e i : a) from
        Subtype.ext (he i)]
    unfold weight
    rw [hv, hp]
  · intro i _ hi
    exact (hi (eq_coarseSliceBasis D ha hS hP hSP i)).elim
  · simp

private theorem projected_root_of_sliceNormal {P : Finset E} (D : DescentPosition R a a₁ ξ)
    (hP : P ∈ parabolics R a₁) {i : simpleRoots a₁ P} {r : E}
    (hr : restrictedRoot a₁ r = (i : a₁)) :
    sliceNormal R a a₁ i = 0 ↔ restrictedRoot a r = 0 := by
  rw [sliceNormal_eq_zero_iff D hP i, ← hr, restrictedRoot_nested D.le_fine]

theorem sliceParameter_ne_zero (D : DescentPosition R a a₁ ξ)
    (hP : P ∈ parabolics R a₁) (Λ : StrongDual ℝ a)
    (hΛ : ∀ r ∈ R, restrictedRoot a r ≠ 0 → Λ (restrictedRoot a r) ≠ 0)
    (i : simpleRoots a₁ P) (hi : sliceNormal R a a₁ i ≠ 0) :
    sliceParameter R Λ (sliceNormal R a a₁ i) ≠ 0 := by
  obtain ⟨r, hr, he⟩ := exists_root_of_mem_simpleRoots i
  have hn : restrictedRoot a r ≠ 0 := fun h =>
    hi ((projected_root_of_sliceNormal D hP he).mpr h)
  have hl := hΛ r (parabolic_subset_rootSet hP hr) hn
  rw [sliceParameter_apply_normal D hP]
  apply mul_ne_zero Complex.I_ne_zero
  apply Complex.ofReal_ne_zero.mpr
  change Λ (restrictedRoot a ((i : a₁) : E)) ≠ 0
  rwa [← he, restrictedRoot_nested D.le_fine]

/-- The fine vertex sum vanishes when the closed fine chamber contains no coarse chamber. -/
theorem vertexSum_eq_zero_of_no_coarse (D : DescentPosition R a a₁ ξ)
    (hP : P ∈ parabolics R a₁) (Λ : StrongDual ℝ a)
    (hΛ : ∀ r ∈ R, restrictedRoot a r ≠ 0 → Λ (restrictedRoot a r) ≠ 0)
    (hn : ¬ ∃ S ∈ parabolics R a, S ⊆ P) :
    vertexSum (sliceNormal R a a₁ (P := P)) (sliceParameter R Λ) (sliceOffset ξ) = 0 := by
  apply vertexSum_eq_zero_of_no_strict_direction
    (sliceParameter R Λ) (sliceParameter_ne_zero D hP Λ hΛ) (sliceOffset_regular D hP)
  rintro ⟨f, hf⟩
  obtain ⟨x, hx⟩ := exists_inner_eq_dual f
  let p : E := x
  have hpa : p ∈ a := x.prop.1
  have hpa₁ : p ∈ a₁ := D.le_fine hpa
  have hpair (i : simpleRoots a₁ P) :
      ⟪((i : a₁) : E), p⟫ = f (sliceNormal R a a₁ i) :=
    (sliceNormal_inner i x).symm.trans (hx _)
  have hle (i : simpleRoots a₁ P) : 0 ≤ ⟪((i : a₁) : E), p⟫ := by
    rw [hpair]
    by_cases h : sliceNormal R a a₁ i = 0
    · rw [h, map_zero]
    · exact (hf i h).le
  have hcl := (chamberClosure_iff_nonneg_simpleRoots D.roots D.fine hP hpa₁).mpr hle
  have hpos {r : E} (hr : r ∈ P) (hra : restrictedRoot a r ≠ 0) : 0 < ⟪r, p⟫ := by
    have h : 0 ≤ ⟪(restrictedRoot a₁ r : E), p⟫ ∧
        (restrictedRoot a (restrictedRoot a₁ r : E) ≠ 0 → 0 < ⟪(restrictedRoot a₁ r : E), p⟫) := by
      refine AddSubmonoid.closure_induction
        (motive := fun v _ => 0 ≤ ⟪v, p⟫ ∧ (restrictedRoot a v ≠ 0 → 0 < ⟪v, p⟫))
        ?_ ?_ ?_ (restrictedRoot_mem_simpleRoot_closure D.roots D.fine hP hr)
      · rintro _ ⟨i, rfl⟩
        refine ⟨hle i, fun hi => ?_⟩
        rw [hpair]
        exact hf i fun h0 => hi ((sliceNormal_eq_zero_iff D hP i).mp h0)
      · refine ⟨by rw [inner_zero_left], fun h0 => (h0 ?_).elim⟩
        simp [restrictedRoot]
      · intro u v _ _ hu hv
        refine ⟨by rw [inner_add_left]; exact add_nonneg hu.1 hv.1, fun huv => ?_⟩
        rw [inner_add_left]
        by_cases hu0 : restrictedRoot a u = 0
        · have hv0 : restrictedRoot a v ≠ 0 := by
            intro hv0
            apply huv
            simp only [restrictedRoot, map_add] at hu0 hv0 ⊢
            rw [hu0, hv0, add_zero]
          exact add_pos_of_nonneg_of_pos hu.1 (hv.2 hv0)
        · exact add_pos_of_pos_of_nonneg (hu.2 hu0) hv.1
    rw [← inner_restrictedRoot hpa₁]
    exact h.2 (by rwa [restrictedRoot_nested D.le_fine])
  have hreg : IsRegular R a p := by
    refine ⟨hpa, fun r hrR hra => ?_⟩
    obtain ⟨q, hq, hPq⟩ := mem_parabolics_iff.mp hP
    have hr₁ : restrictedRoot a₁ r ≠ 0 := by
      intro h
      apply hra
      rw [← restrictedRoot_nested D.le_fine r, h, Submodule.coe_zero]
      simp [restrictedRoot]
    rcases lt_or_gt_of_ne (hq.2 r hrR hr₁) with hneg | hpos'
    · have hmem : -r ∈ P := hPq ▸ mem_posSet_iff.mpr ⟨neg_mem_rootSet D.roots hrR,
        by rw [inner_neg_left]; linarith⟩
      have hra' : restrictedRoot a (-r) ≠ 0 := by
        intro h
        apply hra
        simpa [restrictedRoot] using h
      have h := hpos hmem hra'
      rw [inner_neg_left] at h
      linarith
    · exact (hpos (hPq ▸ mem_posSet_iff.mpr ⟨hrR, hpos'⟩) hra).ne'
  have hsub : posSet R p ⊆ P := by
    have hu := (relative_chamber_of_closed D.roots hP hpa₁ hcl).2
    rw [← hu]
    exact Finset.subset_union_left
  exact hn ⟨posSet R p, mem_parabolics_iff.mpr ⟨p, hreg, rfl⟩, hsub⟩

/-- The projected fine simple roots span the noncentral part of the coarse space. -/
theorem span_sliceNormal_eq_top (D : DescentPosition R a a₁ ξ) (hP : P ∈ parabolics R a₁) :
    span ℝ (Set.range (sliceNormal R a a₁ (P := P))) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  have hy : (y : E) ∈ span ℝ (Set.range fun b : simpleRoots a₁ P => ((b : a₁) : E)) := by
    rw [(simpleRoots_basis D.roots D.fine hP).2]
    exact ⟨D.le_fine y.prop.1, y.prop.2⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy
  have hy' : y = (noncentral R a).orthogonalProjectionOnto (y : E) :=
    (orthogonalProjectionOnto_mem_subspace_eq_self y).symm
  rw [hy', ← hc, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  exact Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)

/-- Some subset of the projected fine simple roots of a fine chamber is a basis. -/
theorem nonempty_basisIndex (D : DescentPosition R a a₁ ξ) (hP : P ∈ parabolics R a₁) :
    Nonempty (BasisIndex (sliceNormal R a a₁ (P := P))) := by
  let v := sliceNormal R a a₁ (P := P)
  obtain ⟨b, -, -, hspan, hli⟩ := exists_linearIndepOn_extension (K := ℝ) (v := v)
    (linearIndepOn_empty ℝ v) (Set.empty_subset Set.univ)
  let J : Finset (simpleRoots a₁ P) := b.toFinset
  have hli' : LinearIndependent ℝ (fun j : J => v j) :=
    hli.comp (fun j : J => ⟨j.1, Set.mem_toFinset.mp j.2⟩)
      (fun i j h => Subtype.ext (by simpa using congrArg Subtype.val h))
  have hrange : Set.range (fun j : J => v j) = v '' b := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.1, Set.mem_toFinset.mp j.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, Set.mem_toFinset.mpr hi⟩, rfl⟩
  have hsp : span ℝ (Set.range fun j : J => v j) = ⊤ := by
    rw [eq_top_iff, ← span_sliceNormal_eq_top D hP, hrange, span_le, ← Set.image_univ]
    exact hspan
  refine ⟨⟨J, hli', ?_⟩⟩
  have hc := finrank_span_eq_card hli'
  rw [hsp, finrank_top, Fintype.card_coe] at hc
  exact hc.symm

private theorem exists_transverseLevi (D : DescentPosition R a a₁ ξ) :
    Nonempty (transverseLevis R a a₁) := by
  obtain ⟨q, hq⟩ := exists_regular R a₁
  have hP : posSet R q ∈ parabolics R a₁ := mem_parabolics_iff.mpr ⟨q, hq, rfl⟩
  obtain ⟨J⟩ := nonempty_basisIndex D hP
  exact ⟨basisTransverseLevi D hP J⟩

private theorem offset_ne_zero_of_fine_active (D : DescentPosition R a a₁ ξ) {r : E}
    (hr : r ∈ R) (hz : restrictedRoot a r = 0) (hn : restrictedRoot a₁ r ≠ 0) :
    ⟪r, ξ⟫ ≠ 0 := by
  intro hi
  obtain ⟨L⟩ := exists_transverseLevi D
  let p := transversePoint D L
  have hp : ⟪r, p⟫ = 0 := by
    have he := pairing_zero_of_projection_zero hz (transversePoint_spec D L).2.1
    change ⟪r, p - ξ⟫ = 0 at he
    rwa [inner_sub_right, hi, sub_zero] at he
  have hL : restrictedRoot (L : Submodule ℝ E) r = 0 := by
    by_contra h
    exact (transversePoint_regular D L).2 r hr h hp
  have horth : (restrictedRoot a₁ r : E) ∈ (L : Submodule ℝ E)ᗮ := by
    intro y hy
    rw [real_inner_comm, inner_restrictedRoot (transverseLevi_le_fine D L hy)]
    exact pairing_zero_of_projection_zero hL hy
  let w : (a₁ ⊓ (L : Submodule ℝ E)ᗮ : Submodule ℝ E) :=
    ⟨(restrictedRoot a₁ r : E), (restrictedRoot a₁ r).prop, horth⟩
  let f := descentProjection a (centralSpace R) a₁ (L : Submodule ℝ E)
  have hf := (dDescent_ne_zero_iff D.central D.le_fine
    (centralSpace_le_of_levi (transverseLevi_isLevi D L))).mp (Finset.mem_filter.mp L.prop).2
  have hw : f w = 0 := by
    change (noncentral R a).orthogonalProjectionOnto (restrictedRoot a₁ r : E) = 0
    apply orthogonalProjectionOnto_eq_zero_iff.mpr
    apply orthogonal_le (show noncentral R a ≤ a from inf_le_left)
    apply restrictedRoot_eq_zero_iff.mp
    rwa [restrictedRoot_nested D.le_fine]
  have hzero : w = 0 := hf.1 (hw.trans (map_zero f).symm)
  apply hn
  apply Subtype.ext
  exact congrArg (fun x : (a₁ ⊓ (L : Submodule ℝ E)ᗮ : Submodule ℝ E) => (x : E)) hzero

private theorem posSet_eq_of_pos_simpleRoots (D : DescentPosition R a a₁ ξ)
    (hP : P ∈ parabolics R a₁) {y : E} (hy : y ∈ a₁)
    (hs : ∀ i : simpleRoots a₁ P, 0 < ⟪((i : a₁) : E), y⟫) : posSet R y = P := by
  obtain ⟨q, hq, hPq⟩ := mem_parabolics_iff.mp hP
  have hp (r : E) (hr : r ∈ P) : 0 < ⟪r, y⟫ := by
    have h : (restrictedRoot a₁ r : E) = 0 ∨ 0 < ⟪(restrictedRoot a₁ r : E), y⟫ := by
      refine AddSubmonoid.closure_induction (motive := fun v _ => v = 0 ∨ 0 < ⟪v, y⟫)
        ?_ (Or.inl rfl) ?_ (restrictedRoot_mem_simpleRoot_closure D.roots D.fine hP hr)
      · rintro _ ⟨i, rfl⟩
        exact Or.inr (hs i)
      · intro u v _ _ hu hv
        rcases hu with rfl | hu
        · simpa only [zero_add] using hv
        rcases hv with rfl | hv
        · simpa only [add_zero] using Or.inr hu
        exact Or.inr (by rw [inner_add_left]; exact add_pos hu hv)
    rw [← inner_restrictedRoot hy]
    apply h.resolve_left
    intro h0
    have hqpos := (mem_posSet_iff.mp (hPq ▸ hr)).2
    exact hqpos.ne' (pairing_zero_of_projection_zero (Subtype.ext h0) hq.1)
  apply Finset.Subset.antisymm
  · intro r hr
    obtain ⟨hrR, hry⟩ := mem_posSet_iff.mp hr
    have hn : restrictedRoot a₁ r ≠ 0 := fun h => hry.ne' (pairing_zero_of_projection_zero h hy)
    rcases lt_or_gt_of_ne (hq.2 r hrR hn) with hneg | hpos
    · have hmem : -r ∈ P := hPq.symm ▸ mem_posSet_iff.mpr ⟨neg_mem_rootSet D.roots hrR,
        by simpa using hneg⟩
      have he := hp (-r) hmem
      simp only [inner_neg_left, neg_pos] at he
      exact (hry.not_gt he).elim
    · exact hPq.symm ▸ mem_posSet_iff.mpr ⟨hrR, hpos⟩
  · exact fun r hr => mem_posSet_iff.mpr ⟨parabolic_subset_rootSet hP hr, hp r hr⟩

/-- Each coarse chamber has exactly one fine lift selected by the displacement. -/
theorem existsUnique_sliceLift (D : DescentPosition R a a₁ ξ) (hS : S ∈ parabolics R a) :
    ∃! P : Finset E, P ∈ parabolics R a₁ ∧ isSliceLift R a a₁ ξ S P := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hS
  obtain ⟨t, ht, hsign⟩ := exists_pos_perturbation R p ξ
  let y := p + t • ξ
  have hy : IsRegular R a₁ y := by
    refine ⟨a₁.add_mem (D.le_fine hp.1) (a₁.smul_mem t D.offset.1), fun r hr hactive => ?_⟩
    rcases lt_trichotomy ⟪r, p⟫ 0 with hn | he | hp'
    · exact ((hsign r hr).2 hn).ne
    · have hz : restrictedRoot a r = 0 := by
        by_contra h
        exact hp.2 r hr h he
      change ⟪r, p + t • ξ⟫ ≠ 0
      rw [inner_add_right, real_inner_smul_right, he, zero_add]
      exact mul_ne_zero ht.ne' (offset_ne_zero_of_fine_active D hr hz hactive)
    · exact ((hsign r hr).1 hp').ne'
  have hY : posSet R y ∈ parabolics R a₁ := mem_parabolics_iff.mpr ⟨y, hy, rfl⟩
  have hsub : posSet R p ⊆ posSet R y := fun r h => mem_posSet_iff.mpr
    ⟨(mem_posSet_iff.mp h).1, (hsign r (mem_posSet_iff.mp h).1).1 (mem_posSet_iff.mp h).2⟩
  refine ⟨posSet R y, ⟨hY, hsub, ?_⟩, ?_⟩
  · intro i hi
    obtain ⟨r, hr, he⟩ := exists_root_of_mem_simpleRoots i
    have hzero := (projected_root_of_sliceNormal D hY he).mp hi
    have hzp := pairing_zero_of_projection_zero hzero hp.1
    have hry := (mem_posSet_iff.mp hr).2
    change 0 < ⟪r, p + t • ξ⟫ at hry
    rw [inner_add_right, real_inner_smul_right, hzp, zero_add] at hry
    change 0 < ⟪((i : a₁) : E), ξ⟫
    rw [← he, inner_restrictedRoot D.offset.1]
    exact pos_of_mul_pos_right hry ht.le
  · rintro P ⟨hP, hSP, hθ⟩
    apply (posSet_eq_of_pos_simpleRoots D hP hy.1 ?_).symm
    intro i
    obtain ⟨r, hr, he⟩ := exists_root_of_mem_simpleRoots i
    have hrR := parabolic_subset_rootSet hP hr
    rw [← he, inner_restrictedRoot hy.1]
    by_cases hi : sliceNormal R a a₁ i = 0
    · have hz := pairing_zero_of_projection_zero ((projected_root_of_sliceNormal D hP he).mp hi) hp.1
      have hf := hθ i hi
      change 0 < ⟪((i : a₁) : E), ξ⟫ at hf
      rw [← he, inner_restrictedRoot D.offset.1] at hf
      change 0 < ⟪r, p + t • ξ⟫
      rw [inner_add_right, real_inner_smul_right, hz, zero_add]
      exact mul_pos ht hf
    · have hz : restrictedRoot a r ≠ 0 := fun he' => hi ((projected_root_of_sliceNormal D hP he).mpr he')
      exact (hsign r hrR).1 (lt_of_le_of_ne (closure_of_positive_subset D.roots hP hSP r hr)
        (hp.2 r hrR hz).symm)

/-- A fine chamber can extend at most one coarse chamber. -/
theorem coarse_chamber_unique (D : DescentPosition R a a₁ ξ) {T : Finset E}
    (hS : S ∈ parabolics R a) (hT : T ∈ parabolics R a) (hP : P ∈ parabolics R a₁)
    (hSP : S ⊆ P) (hTP : T ⊆ P) : S = T :=
  (coarse_eq_inter_active D.roots hS hP hSP).trans (coarse_eq_inter_active D.roots hT hP hTP).symm

end Langlands.GMFamily.CentralSubspaceDescent
