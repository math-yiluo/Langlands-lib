/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.CategoryTheory.Subobject.Lattice
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.CommSq

/-!
# The lattice of subobjects of an object of an abelian category

Let `X` be an object of an abelian category `C`, and let `S` and `T` be subobjects of `X`.
We study the image functor `Subobject.«exists» f` along the projection
`π : X ⟶ X / S` onto the cokernel of `S.arrow`, and the square of canonical monomorphisms
relating `S ⊓ T`, `S`, `T` and `S ⊔ T`. We also show that the intersection `S ⊓ T` is the
kernel of the composition of `T.arrow : (T : C) ⟶ X` with the projection `π : X ⟶ X / S`.

## Main results

* `CategoryTheory.Subobject.pullback_exists_cokernelπ`: the preimage in `X` of the image
  of `T` in `X / S` is `S ⊔ T`; the modularity consequence
  `CategoryTheory.Subobject.le_sup_of_exists_obj_le` says that if the image of `T` in `X / S`
  is contained in the image of `U`, then `T ≤ S ⊔ U`.
* `CategoryTheory.Subobject.isPushout_inf_sup`: the square `(S ⊓ T, S, T, S ⊔ T)` is a
  pushout square (it is also a pullback square, see
  `CategoryTheory.Subobject.isPullback_ofLE_inf`).
* `CategoryTheory.Subobject.noetherIso`: the Noether isomorphism `T / (S ⊓ T) ≅ (S ⊔ T) / S`,
  and `CategoryTheory.Subobject.cokernelOfLEIsoExistsObj`, which identifies `T / (S ⊓ T)` with
  the image of `T` in `X / S`.
* `CategoryTheory.Subobject.exists_obj_pullback_obj`: pulling back subobjects along an
  epimorphism is injective.
* `CategoryTheory.Subobject.isLimitKernelForkInf`: the intersection `S ⊓ T` is the kernel
  of `T.arrow ≫ π`.

-/

@[expose] public section

universe v u

namespace CategoryTheory.Subobject

open Category Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

section

variable {X : C}

@[reassoc (attr := simp)]
lemma ofLE_inf_comp_arrow_comp_cokernel_π (S T : Subobject X) :
    ofLE (S ⊓ T) T _root_.inf_le_right ≫ T.arrow ≫ cokernel.π S.arrow = 0 := by
  rw [← Category.assoc, ofLE_arrow, ← ofLE_arrow (_root_.inf_le_left (a := S) (b := T)),
    Category.assoc, cokernel.condition, comp_zero]

/-- In an abelian category, the intersection `S ⊓ T` of two subobjects of `X` is the kernel
of the composition of `T.arrow` with the projection `X ⟶ X ⧸ S`. -/
noncomputable def isLimitKernelForkInf (S T : Subobject X) :
    IsLimit (KernelFork.ofι (ofLE (S ⊓ T) T _root_.inf_le_right)
      (ofLE_inf_comp_arrow_comp_cokernel_π S T)) :=
  KernelFork.IsLimit.ofι' _ _ (fun {A} k hk => by
    rw [← Category.assoc] at hk
    have hS : S.Factors (k ≫ T.arrow) := by
      rw [← Abelian.monoLift_comp S.arrow (k ≫ T.arrow) hk]
      exact factors_comp_arrow _
    refine ⟨factorThru _ _ ((inf_factors _).2 ⟨hS, factors_comp_arrow k⟩), ?_⟩
    rw [← cancel_mono T.arrow, Category.assoc, ofLE_arrow, factorThru_arrow])

end

lemma exists_obj_eq_mk {X Y : C} (f : X ⟶ Y) (S : Subobject X) {I : C}
    (e : (S : C) ⟶ I) (i : I ⟶ Y) [Epi e] [Mono i] (comm : e ≫ i = S.arrow ≫ f) :
    («exists» f).obj S = mk i := by
  have := strongEpi_of_epi e
  refine (mk_arrow _).symm.trans (mk_eq_mk_of_comm _ _
    (IsImage.isoExt (imageFactorisation f S).isImage (Image.isImage _) ≪≫
      (image.isoStrongEpiMono e i comm).symm) ?_)
  simp [image.isoStrongEpiMono_inv_comp_mono]

lemma exists_obj_eq_bot {X Y : C} (f : X ⟶ Y) (S : Subobject X) (h : S.arrow ≫ f = 0) :
    («exists» f).obj S = ⊥ := by
  have := epi_of_target_iso_zero (0 : (S : C) ⟶ 0) (Iso.refl 0)
  have := mono_of_source_iso_zero (0 : (0 : C) ⟶ Y) (Iso.refl 0)
  rw [exists_obj_eq_mk f S (0 : (S : C) ⟶ 0) (0 : (0 : C) ⟶ Y) (by simp [h]),
    mk_eq_bot_iff_zero]

/-- A subobject `S` of `X` maps epimorphically onto its image in `Y` under `f : X ⟶ Y`. -/
lemma exists_fac {X Y : C} (f : X ⟶ Y) (S : Subobject X) :
    ∃ e : (S : C) ⟶ (((«exists» f).obj S : Subobject Y) : C),
      Epi e ∧ e ≫ ((«exists» f).obj S).arrow = S.arrow ≫ f := by
  refine ⟨(imageFactorisation f S).F.e, ?_, ?_⟩
  · have : Epi (Image.monoFactorisation (S.arrow ≫ f)).e :=
      inferInstanceAs (Epi (factorThruImage _))
    rw [← IsImage.e_isoExt_inv (imageFactorisation f S).isImage (Image.isImage _)]
    infer_instance
  · exact (imageFactorisation f S).F.fac

lemma exists_obj_pullback_obj {X Y : C} (p : X ⟶ Y) [Epi p] (T : Subobject Y) :
    («exists» p).obj ((pullback p).obj T) = T := by
  have : Epi (pullbackπ p T) :=
    (MorphismProperty.epimorphisms C).of_isPullback (Subobject.isPullback p T).flip inferInstance
  rw [exists_obj_eq_mk p _ (pullbackπ p T) T.arrow (Subobject.isPullback p T).w, mk_arrow]

lemma pullback_exists_obj_of_le {X : C} (S V : Subobject X) (h : S ≤ V) :
    (pullback (cokernel.π S.arrow)).obj ((«exists» (cokernel.π S.arrow)).obj V) = V := by
  refine le_antisymm ?_ ((existsPullbackAdj (cokernel.π S.arrow)).gc.le_u_l V)
  obtain ⟨e, he, hef⟩ := exists_fac (cokernel.π S.arrow) V
  have hSc : S.arrow ≫ cokernel.π V.arrow = 0 := by
    rw [← ofLE_arrow h, assoc, cokernel.condition, comp_zero]
  obtain ⟨c, hfac⟩ : ∃ c, cokernel.π S.arrow ≫ c = cokernel.π V.arrow :=
    ⟨cokernel.desc _ _ hSc, cokernel.π_desc _ _ _⟩
  have hWc : (((«exists» (cokernel.π S.arrow)).obj V)).arrow ≫ c = 0 := by
    rw [← cancel_epi e, comp_zero, ← assoc, hef, assoc, hfac, cokernel.condition]
  have hUc : ((pullback (cokernel.π S.arrow)).obj
      ((«exists» (cokernel.π S.arrow)).obj V)).arrow ≫ cokernel.π V.arrow = 0 := by
    rw [← hfac, ← assoc, ← (Subobject.isPullback (cokernel.π S.arrow) _).w, assoc, hWc,
      comp_zero]
  obtain ⟨k, hk⟩ := KernelFork.IsLimit.lift'
    (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel V.arrow)) _ hUc
  exact le_of_comm k (by simpa using hk)

/-- The image of `S ⊔ T` in `X / S` is the image of `T`. -/
lemma exists_obj_sup_eq {X : C} (S T : Subobject X) :
    («exists» (cokernel.π S.arrow)).obj (S ⊔ T) = («exists» (cokernel.π S.arrow)).obj T := by
  have hgc := (existsPullbackAdj (cokernel.π S.arrow)).gc
  have hS : («exists» (cokernel.π S.arrow)).obj S ≤ («exists» (cokernel.π S.arrow)).obj T :=
    le_of_eq_of_le (exists_obj_eq_bot _ _ (cokernel.condition _)) bot_le
  exact le_antisymm ((hgc _ _).2 (_root_.sup_le ((hgc _ _).1 hS) (hgc.le_u_l T)))
    (Functor.monotone _ _root_.le_sup_right)

lemma pullback_exists_cokernelπ {X : C} (S T : Subobject X) :
    (pullback (cokernel.π S.arrow)).obj ((«exists» (cokernel.π S.arrow)).obj T) = S ⊔ T := by
  rw [← exists_obj_sup_eq S T]
  exact pullback_exists_obj_of_le S (S ⊔ T) _root_.le_sup_left

lemma le_sup_of_exists_obj_le {X : C} (S T U : Subobject X)
    (h : («exists» (cokernel.π S.arrow)).obj T ≤ («exists» (cokernel.π S.arrow)).obj U) :
    T ≤ S ⊔ U := by
  refine le_trans ((existsPullbackAdj (cokernel.π S.arrow)).gc.le_u_l T) ?_
  rw [← pullback_exists_cokernelπ S U]
  exact Functor.monotone _ h

section Noether

variable {X : C} (S T : Subobject X)

/-- The canonical morphism `(S : C) ⊞ (T : C) ⟶ (S ⊔ T : C)`. -/
noncomputable def supDesc : ((S : C) ⊞ (T : C) : C) ⟶ ((S ⊔ T : Subobject X) : C) :=
  biprod.desc (ofLE S (S ⊔ T) _root_.le_sup_left) (ofLE T (S ⊔ T) _root_.le_sup_right)

@[reassoc (attr := simp)]
lemma inl_supDesc : biprod.inl ≫ supDesc S T = ofLE S (S ⊔ T) _root_.le_sup_left :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_supDesc : biprod.inr ≫ supDesc S T = ofLE T (S ⊔ T) _root_.le_sup_right :=
  biprod.inr_desc _ _

/-- The square formed by the four canonical monomorphisms between `S ⊓ T`, `S`, `T` and
`S ⊔ T` is a pullback square. -/
lemma isPullback_ofLE_inf :
    IsPullback (ofLE (S ⊓ T) S _root_.inf_le_left) (ofLE (S ⊓ T) T _root_.inf_le_right)
      (ofLE S (S ⊔ T) _root_.le_sup_left) (ofLE T (S ⊔ T) _root_.le_sup_right) := by
  have w : ofLE (S ⊓ T) S _root_.inf_le_left ≫ ofLE S (S ⊔ T) _root_.le_sup_left
      = ofLE (S ⊓ T) T _root_.inf_le_right ≫ ofLE T (S ⊔ T) _root_.le_sup_right := by
    rw [← cancel_mono (S ⊔ T).arrow]; simp
  have hc : ∀ s : PullbackCone (ofLE S (S ⊔ T) _root_.le_sup_left)
      (ofLE T (S ⊔ T) _root_.le_sup_right), s.fst ≫ S.arrow = s.snd ≫ T.arrow := fun s => by
    rw [← ofLE_arrow (_root_.le_sup_left : S ≤ S ⊔ T),
      ← ofLE_arrow (_root_.le_sup_right : T ≤ S ⊔ T), ← assoc, ← assoc, s.condition]
  have hfac : ∀ s, (S ⊓ T).Factors (PullbackCone.fst s ≫ S.arrow) := fun s =>
    (inf_factors _).2 ⟨factors_comp_arrow s.fst, (hc s) ▸ factors_comp_arrow s.snd⟩
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun s => (S ⊓ T).factorThru _ (hfac s)) (fun s => ?_) (fun s => ?_) (fun s m h₁ _ => ?_))
  · rw [← cancel_mono S.arrow, assoc, ofLE_arrow, factorThru_arrow]
  · rw [← cancel_mono T.arrow, assoc, ofLE_arrow, factorThru_arrow, hc s]
  · rw [← cancel_mono (S ⊓ T).arrow, factorThru_arrow,
      ← ofLE_arrow (_root_.inf_le_left : S ⊓ T ≤ S), ← assoc, h₁]

private lemma eq_zero_of_ofLE_comp_eq_zero {Z : C} (c : ((S ⊔ T : Subobject X) : C) ⟶ Z)
    (hS : ofLE S (S ⊔ T) _root_.le_sup_left ≫ c = 0)
    (hT : ofLE T (S ⊔ T) _root_.le_sup_right ≫ c = 0) : c = 0 := by
  have hS' : S ≤ mk ((kernelSubobject c).arrow ≫ (S ⊔ T).arrow) :=
    le_mk_of_comm (factorThruKernelSubobject c _ hS)
      (by rw [← assoc, factorThruKernelSubobject_comp_arrow, ofLE_arrow])
  have hT' : T ≤ mk ((kernelSubobject c).arrow ≫ (S ⊔ T).arrow) :=
    le_mk_of_comm (factorThruKernelSubobject c _ hT)
      (by rw [← assoc, factorThruKernelSubobject_comp_arrow, ofLE_arrow])
  have hV : mk ((kernelSubobject c).arrow ≫ (S ⊔ T).arrow) = mk (S ⊔ T).arrow :=
    le_antisymm (mk_le_mk_of_comm (kernelSubobject c).arrow rfl)
      (by rw [mk_arrow]; exact _root_.sup_le hS' hT')
  have h1 : (isoOfMkEqMk _ _ hV).hom = (kernelSubobject c).arrow := by
    rw [← cancel_mono (S ⊔ T).arrow, isoOfMkEqMk_hom, ofMkLEMk_comp]
  have : IsIso (kernelSubobject c).arrow := by rw [← h1]; infer_instance
  rw [← cancel_epi (kernelSubobject c).arrow, kernelSubobject_arrow_comp, comp_zero]

lemma epi_supDesc : Epi (supDesc S T) := by
  refine Abelian.epi_of_cokernel_π_eq_zero _ (eq_zero_of_ofLE_comp_eq_zero S T _ ?_ ?_)
  · rw [← inl_supDesc, assoc, cokernel.condition, comp_zero]
  · rw [← inr_supDesc, assoc, cokernel.condition, comp_zero]

/-- The square formed by the four canonical monomorphisms between `S ⊓ T`, `S`, `T` and
`S ⊔ T` is a pushout square. -/
lemma isPushout_inf_sup :
    IsPushout (ofLE (S ⊓ T) S _root_.inf_le_left) (ofLE (S ⊓ T) T _root_.inf_le_right)
      (ofLE S (S ⊔ T) _root_.le_sup_left) (ofLE T (S ⊔ T) _root_.le_sup_right) :=
  (isPullback_ofLE_inf S T).isPushout_of_epi (epi_supDesc S T)

/-- The Noether isomorphism `T / (S ⊓ T) ≅ (S ⊔ T) / S`. -/
noncomputable def noetherIso :
    cokernel (ofLE (S ⊓ T) T _root_.inf_le_right)
      ≅ cokernel (ofLE S (S ⊔ T) _root_.le_sup_left) :=
  (isPushout_inf_sup S T).cokernelIso

/-- The canonical monomorphism `(S ⊔ T) / S ⟶ X / S`. -/
noncomputable def supCokernelDesc :
    cokernel (ofLE S (S ⊔ T) _root_.le_sup_left) ⟶ cokernel S.arrow :=
  cokernel.desc _ ((S ⊔ T).arrow ≫ cokernel.π S.arrow)
    (by rw [← assoc, ofLE_arrow, cokernel.condition])

@[reassoc (attr := simp)]
lemma π_supCokernelDesc : cokernel.π (ofLE S (S ⊔ T) _root_.le_sup_left) ≫ supCokernelDesc S T
    = (S ⊔ T).arrow ≫ cokernel.π S.arrow :=
  cokernel.π_desc _ _ _

instance mono_supCokernelDesc : Mono (supCokernelDesc S T) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z z hz
  obtain ⟨Z', p, _, x, hx⟩ := surjective_up_to_refinements_of_epi
    (cokernel.π (ofLE S (S ⊔ T) _root_.le_sup_left)) z
  have hx0 : (x ≫ (S ⊔ T).arrow) ≫ cokernel.π S.arrow = 0 := by
    rw [assoc, ← π_supCokernelDesc S T, ← assoc, ← hx, assoc, hz, comp_zero]
  obtain ⟨y, hy⟩ := KernelFork.IsLimit.lift'
    (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel S.arrow)) _ hx0
  have hym : y ≫ ofLE S (S ⊔ T) _root_.le_sup_left = x := by
    rw [← cancel_mono (S ⊔ T).arrow, assoc, ofLE_arrow]
    simpa using hy
  rw [← cancel_epi p, comp_zero, hx, ← hym, assoc,
    cokernel.condition (ofLE S (S ⊔ T) _root_.le_sup_left), comp_zero]

/-- The cokernel of `S ⊓ T ⟶ T` is the image of `T` in `X / S`. -/
noncomputable def cokernelOfLEIsoExistsObj :
    cokernel (ofLE (S ⊓ T) T _root_.inf_le_right) ≅
      (((«exists» (cokernel.π S.arrow)).obj T : Subobject (cokernel S.arrow)) : C) :=
  noetherIso S T ≪≫ isoOfMkEqMk (supCokernelDesc S T)
    (((«exists» (cokernel.π S.arrow)).obj T).arrow) (by
      rw [mk_arrow, ← exists_obj_sup_eq S T]
      exact (exists_obj_eq_mk _ _ (cokernel.π (ofLE S (S ⊔ T) _root_.le_sup_left)) _
        (π_supCokernelDesc S T)).symm)

end Noether

end CategoryTheory.Subobject
