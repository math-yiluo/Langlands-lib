/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement

/-! # Detecting sheaves on the twisted action category

Source: original twisted-site step 3, motivated by Stacks Tag 00W0.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.TwistedActionRingedSite

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

private theorem sheafFor_image {D : Type u} [SmallCategory D] (F : C ⥤ D)
    (G : Dᵒᵖ ⥤ Type u) {X : C} (T : Sieve X)
    (hG : Presieve.IsSheafFor (F.op ⋙ G) T.arrows) :
    Presieve.IsSheafFor G (T.functorPushforward F).arrows := by
  intro x hx
  let y : Presieve.FamilyOfElements (F.op ⋙ G) T.arrows :=
    fun Y f hf ↦ x (F.map f) (Sieve.image_mem_functorPushforward F T hf)
  have hy : y.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ he
    exact hx (F.map g₁) (F.map g₂) _ _ (by
      simpa only [← F.map_comp] using F.congr_map he)
  obtain ⟨t, ht, hu⟩ := hG y hy
  refine ⟨t, ?_, ?_⟩
  · intro Y f hf
    obtain ⟨Z, g, k, hg, rfl⟩ := hf
    simp only [op_comp, Functor.map_comp, types_comp_apply]
    rw [show G.map (F.map g).op t = y g hg from ht g hg]
    exact (hx k (𝟙 _) (Sieve.image_mem_functorPushforward F T hg)
      ⟨Z, g, k, hg, rfl⟩ (by simp)).trans (by simp)
  · intro t' ht'
    apply hu t'
    intro Y f hf
    exact ht' (F.map f) (Sieve.image_mem_functorPushforward F T hf)

private theorem separated_of_restriction {D : Type u} [SmallCategory D] (F : C ⥤ D)
    (G : Dᵒᵖ ⥤ Type u) {X : C} (T : Sieve (F.obj X))
    (hG : Presieve.IsSheafFor (F.op ⋙ G) (T.functorPullback F).arrows) :
    Presieve.IsSeparatedFor G T.arrows := by
  intro x t₁ t₂ ht₁ ht₂
  apply hG.isSeparatedFor.ext
  intro Y f hf
  exact (ht₁ (F.map f) hf).trans (ht₂ (F.map f) hf).symm

private theorem sheafFor_pullback_image {D : Type u} [SmallCategory D] (F : C ⥤ D)
    (G : Dᵒᵖ ⥤ Type u) (hF : Function.Surjective F.obj)
    (hG : Presieve.IsSheaf J (F.op ⋙ G))
    (H : ∀ {X Y : C} (T : Sieve X), T ∈ J X →
      ∀ (f : F.obj Y ⟶ F.obj X),
        ((T.functorPushforward F).pullback f).functorPullback F ∈ J Y)
    {X : C} (T : Sieve X) (hT : T ∈ J X) {Y : D} (f : Y ⟶ F.obj X) :
    Presieve.IsSheafFor G ((T.functorPushforward F).pullback f).arrows := by
  obtain ⟨Y, rfl⟩ := hF Y
  let Q := (T.functorPushforward F).pullback f
  let U := Q.functorPullback F
  have hU : U ∈ J Y := H T hT f
  refine Presieve.isSheafFor_subsieve_aux G
    (S := U.functorPushforward F) ?_ (sheafFor_image F G U (hG U hU)) ?_
  · exact Sieve.functorPullback_pushforward_le F Q
  · intro Z k _
    obtain ⟨Z, rfl⟩ := hF Z
    exact separated_of_restriction F G _ (hG _ (H U hU k))

private theorem powNat_continuous (e : C ≌ C) [e.functor.IsContinuous J J] (n : ℕ) :
    (e.powNat n).functor.IsContinuous J J := by
  induction n using Nat.twoStepInduction with
  | zero => exact Functor.isContinuous_id J
  | one => exact inferInstanceAs (e.functor.IsContinuous J J)
  | more n _ hn =>
    let := hn
    exact Functor.isContinuous_comp _ _ J J J

private theorem power_continuous (n : ℤ) : (s ^ n).functor.IsContinuous J J := by
  cases n with
  | ofNat n => exact powNat_continuous J s n
  | negSucc n =>
    let : s.symm.functor.IsContinuous J J :=
      inferInstanceAs (s.inverse.IsContinuous J J)
    exact powNat_continuous J s.symm (n + 1)

omit [s.functor.IsContinuous J J] in
private theorem powerComp_zero_left (S : Site J s R a) (n : ℤ) (X : C) :
    HEq ((S.powerComp 0 n).hom.app X) (𝟙 ((s ^ n).functor.obj X)) := by
  let := S.category
  have hi := (S.arrows ((s ^ n).functor.obj X) ((s ^ n).functor.obj X)).symm_apply_apply
    (𝟙 _)
  rw [S.arrows_id] at hi
  have h := S.arrows_comp ((s ^ n).functor.obj X) ((s ^ n).functor.obj X) X
    0 n (𝟙 _) (𝟙 _)
  simp only [hi, Category.id_comp, Equiv.apply_symm_apply, Functor.map_id] at h
  exact (Sigma.mk.inj h).2.symm

omit [s.functor.IsContinuous J J] in
private theorem powerComp_zero_right (S : Site J s R a) (n : ℤ) (X : C) :
    HEq ((S.powerComp n 0).hom.app X) (𝟙 ((s ^ n).functor.obj X)) := by
  let := S.category
  have hi := (S.arrows X X).symm_apply_apply (𝟙 _)
  rw [S.arrows_id] at hi
  have h := S.arrows_comp ((s ^ n).functor.obj X) X X n 0 (𝟙 _) (𝟙 _)
  simp only [hi, Category.comp_id, Equiv.apply_symm_apply, Functor.map_id,
    Category.id_comp] at h
  exact (Sigma.mk.inj h).2.symm

private theorem image_cover_pullback (S : Site J s R a) :
    let := S.category
    ∀ {X Y : C} (T : Sieve X), T ∈ J X →
      ∀ (f : S.inclusion.obj Y ⟶ S.inclusion.obj X),
        ((T.functorPushforward S.inclusion).pullback f).functorPullback S.inclusion ∈ J Y := by
  let := S.category
  dsimp only
  intro X Y T hT f
  obtain ⟨⟨n, g⟩, rfl⟩ := (S.arrows Y X).symm.surjective f
  let := power_continuous J s n
  have hcov := J.pullback_stable g
    ((CoverPreserving.of_isContinuous (s ^ n).functor J J).cover_preserve hT)
  refine J.superset_covering ?_ hcov
  intro Z k hk
  obtain ⟨W, l, q, hl, he⟩ := hk
  refine ⟨W, l, (S.arrows Z W).symm ⟨n, q⟩, hl, ?_⟩
  apply (S.arrows Z X).injective
  have hk := (S.arrows Z Y).symm_apply_apply (S.inclusion.map k)
  have hl := (S.arrows W X).symm_apply_apply (S.inclusion.map l)
  rw [S.arrows_inclusion] at hk hl
  rw [← hk, ← hl, S.arrows_comp, S.arrows_comp]
  have hleft := powerComp_zero_left J s R a S n X
  have hright := powerComp_zero_right J s R a S n X
  have hL := heq_comp (f := k ≫ (s ^ (0 : ℤ)).functor.map g) (f' := k ≫ g)
    rfl rfl (show (s ^ (0 + n)).functor.obj X = (s ^ n).functor.obj X by simp)
    HEq.rfl hleft
  have hR := heq_comp (f := q ≫ (s ^ n).functor.map l)
    (f' := q ≫ (s ^ n).functor.map l)
    rfl rfl (show (s ^ (n + 0)).functor.obj X = (s ^ n).functor.obj X by simp)
    HEq.rfl hright
  apply Sigma.ext ((Int.zero_add n).trans (Int.add_zero n).symm)
  exact (heq_of_eq (Category.assoc _ _ _).symm).trans
    (hL.trans ((heq_of_eq (by simpa only [Category.comp_id] using he)).trans
      (hR.symm.trans (heq_of_eq (Category.assoc _ _ _)))))

/-- Sheaf descent along the degree-zero inclusion of a specified twisted site.

Source: the covering-basis part of original step 3 of the agent twisted variant
of Stacks Tag 00W0, `sites.tex`, proposition-sheaves-on-group
(blueprint: lem-sf-twisted-action-sheaf-detection).

Proof: a degree-n arrow is a degree-zero arrow followed by an isomorphism of
copied objects. Pulling a generating J-cover back along it is therefore the same,
up to that isomorphism, as translating the cover by s to the appropriate integer
power and then pulling back inside C. Both directions of s are continuous and C
has pullbacks; hence these translated pullbacks are J-covers. For the image of
such a cover, restrict a matching family to its degree-zero arrows and use the
assumed J-sheaf property for the unique amalgamation. Factor each other arrow
through its power isomorphism: naturality of G and compatibility of the family
show that the same amalgamation has the prescribed value there. Uniqueness
already follows on the degree-zero covering family. Thus G satisfies descent on
every pullback of every generating sieve. These are covers for the finest topology
of G; S.topology_eq and its infimum property put S.topology below that topology.
Consequently G is an S.topology-sheaf. This argument also treats empty covers and
an empty category; no coefficient-ring property is used. -/
theorem twistedSheafOfRestriction [HasPullbacks C] (S : Site J s R a) :
    letI := S.category
    ∀ (G : (Object C)ᵒᵖ ⥤ Type u),
      Presheaf.IsSheaf J (S.inclusion.op ⋙ G) → Presheaf.IsSheaf S.topology G := by
  let := S.category
  intro G hG
  have hG' := (isSheaf_iff_isSheaf_of_type J _).mp hG
  have hsurj : Function.Surjective S.inclusion.obj := by
    intro X
    exact ⟨X.base, S.inclusion_obj X.base⟩
  have htop : S.topology ≤ Sheaf.finestTopologySingle G := by
    rw [S.topology_eq]
    apply sInf_le
    intro X T hT Y f
    exact sheafFor_pullback_image J S.inclusion G hsurj hG'
      (image_cover_pullback J s R a S) T hT f
  apply (isSheaf_iff_isSheaf_of_type S.topology G).mpr
  apply Presieve.isSheaf_of_le G htop
  intro X T hT
  simpa only [Sieve.pullback_id] using hT X (𝟙 X)

end CategoryTheory.TwistedActionRingedSite
