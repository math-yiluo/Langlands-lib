/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.MittagLefflerTower
public import Mathlib.CategoryTheory.Subobject.ArtinianObject

/-!
# Towers of Artinian objects are Mittag-Leffler

In an abelian category, let `G : ℕᵒᵖ ⥤ C` be a tower whose terms are Artinian objects (e.g.
objects of finite length). The images of the transitions `G m ⟶ G n` form a decreasing chain
of subobjects of `G n`, which stabilises
(`CategoryTheory.Limits.ArtinianTower.exists_im_eq`). The stable images form a subtower
(`CategoryTheory.Limits.ArtinianTower.stabTower`) with epimorphic transitions through which
the transitions of `G` factor, so `G` is Mittag-Leffler
(`CategoryTheory.Limits.isMittagLefflerTower_of_isArtinianObject`); in particular
`lim¹ G = 0` in a replete abelian category
(`CategoryTheory.Limits.epi_one_sub_of_isMittagLefflerTower`).
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

/-- In an abelian category, if `e ≫ a` factors through a subobject `S` and `e` is an
epimorphism, then `a` factors through `S`. -/
lemma Subobject.factors_of_epi_comp {X Y Z : C} (S : Subobject Z) (e : X ⟶ Y) [Epi e]
    (a : Y ⟶ Z) (h : S.Factors (e ≫ a)) : S.Factors a := by
  have ha : a ≫ cokernel.π S.arrow = 0 := by
    rw [← cancel_epi e, ← assoc, ← Subobject.factorThru_arrow S _ h, assoc, cokernel.condition,
      comp_zero, comp_zero]
  rw [← Abelian.monoLift_comp S.arrow a ha]
  exact Subobject.factors_comp_arrow _

/-- The factorisation of `f` through a subobject equal to its image is an epimorphism. -/
lemma Subobject.epi_factorThru_of_eq_imageSubobject {X Y : C} {S : Subobject Y} (f : X ⟶ Y)
    (hS : S = imageSubobject f) (h : S.Factors f) : Epi (S.factorThru f h) := by
  subst hS
  have : (imageSubobject f).factorThru f h = factorThruImageSubobject f := by
    rw [← cancel_mono (imageSubobject f).arrow, Subobject.factorThru_arrow,
      imageSubobject_arrow_comp]
  rw [this]
  infer_instance

end CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C] (G : ℕᵒᵖ ⥤ C)

omit [Abelian C] in
/-- A morphism factors through its image. -/
lemma factors_imageSubobject {X Y : C} [HasImages C] (f : X ⟶ Y) :
    (imageSubobject f).Factors f := by
  simpa using imageSubobject_factors_comp_self f (𝟙 _)

namespace ArtinianTower

/-- The transition `G m ⟶ G n` of a tower. -/
abbrev tr {n m : ℕ} (h : n ≤ m) : G.obj (op m) ⟶ G.obj (op n) := G.map (homOfLE h).op

omit [Abelian C] in
/-- Composition of transitions. -/
lemma tr_comp {n m m' : ℕ} (h : n ≤ m) (h' : m ≤ m') :
    tr G h' ≫ tr G h = tr G (h.trans h') := by
  rw [← G.map_comp]
  rfl

/-- The image of the transition `G m ⟶ G n`. -/
noncomputable abbrev im {n m : ℕ} (h : n ≤ m) : Subobject (G.obj (op n)) := imageSubobject (tr G h)

/-- Images of transitions shrink as the source moves up the tower. -/
lemma im_antitone {n m m' : ℕ} (h : n ≤ m) (h' : m ≤ m') : im G (h.trans h') ≤ im G h := by
  refine (le_of_eq ?_).trans (imageSubobject_comp_le (tr G h') (tr G h))
  change imageSubobject (tr G _) = _
  congr 1
  exact (tr_comp G h h').symm

/-- **Images stabilise in a tower whose term at `n` is Artinian.** -/
lemma exists_im_eq (n : ℕ) [IsArtinianObject (G.obj (op n))] :
    ∃ (N : ℕ) (hN : n ≤ N), ∀ (m : ℕ) (hm : N ≤ m), im G (hN.trans hm) = im G hN := by
  let f : ℕ →o (Subobject (G.obj (op n)))ᵒᵈ :=
    ⟨fun k ↦ OrderDual.toDual (im G (n.le_add_right k)), fun k k' hk ↦
      im_antitone G (n.le_add_right k) (show n + k ≤ n + k' by lia)⟩
  obtain ⟨N, hN⟩ := antitone_chain_condition_of_isArtinianObject f
  refine ⟨n + N, n.le_add_right N, fun m hm ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (n.le_add_right N |>.trans hm)
  exact congrArg OrderDual.ofDual (hN k (by lia)).symm

/-- The images of the transitions `G m ⟶ G n` **stabilise**: for every `n` there is `N ≥ n` such
that the image of `G m ⟶ G n` is the same for all `m ≥ N`. -/
def ImagesStabilize : Prop :=
  ∀ n : ℕ, ∃ (N : ℕ) (hN : n ≤ N), ∀ (m : ℕ) (hm : N ≤ m), im G (hN.trans hm) = im G hN

/-- In a tower of Artinian objects the images stabilise. -/
lemma imagesStabilize_of_isArtinianObject [∀ n : ℕ, IsArtinianObject (G.obj (op n))] :
    ImagesStabilize G :=
  fun n ↦ exists_im_eq G n

variable {G} (hG : ImagesStabilize G)

/-- A stabilisation index of the images at `n`. -/
noncomputable def stabIdx (n : ℕ) : ℕ := (hG n).choose

/-- The stabilisation index lies above `n`. -/
lemma le_stabIdx (n : ℕ) : n ≤ stabIdx hG n := (hG n).choose_spec.choose

/-- The stable image at `n`: the image of `G m ⟶ G n` for all large `m`. -/
noncomputable abbrev stab (n : ℕ) : Subobject (G.obj (op n)) := im G (le_stabIdx hG n)

/-- The stable image is the image of every transition from beyond the stabilisation index. -/
lemma stab_eq (n m : ℕ) (hm : stabIdx hG n ≤ m) :
    stab hG n = im G ((le_stabIdx hG n).trans hm) :=
  ((hG n).choose_spec.choose_spec m hm).symm

/-- Transitions map stable images into stable images. -/
lemma stab_factors {n m : ℕ} (h : n ≤ m) : (stab hG n).Factors ((stab hG m).arrow ≫ tr G h) := by
  let M := max (stabIdx hG m) (stabIdx hG n)
  have hm : stabIdx hG m ≤ M := le_max_left _ _
  have hn : stabIdx hG n ≤ M := le_max_right _ _
  rw [stab_eq hG n M hn]
  have e := stab_eq hG m M hm
  have hf : (stab hG m).Factors (tr G ((le_stabIdx hG m).trans hm)) := by
    rw [e]; exact factors_imageSubobject _
  have := Subobject.epi_factorThru_of_eq_imageSubobject _ e hf
  refine Subobject.factors_of_epi_comp _ ((stab hG m).factorThru _ hf) _ ?_
  rw [← assoc, Subobject.factorThru_arrow, tr_comp]
  exact factors_imageSubobject _

/-- The tower of stable images of a tower whose images stabilise. -/
@[simps]
noncomputable def stabTower : ℕᵒᵖ ⥤ C where
  obj n := (stab hG n.unop : C)
  map {n m} f := (stab hG m.unop).factorThru ((stab hG n.unop).arrow ≫ G.map f)
    (stab_factors hG (leOfHom f.unop))
  map_id n := by
    rw [← cancel_mono (stab hG n.unop).arrow, Subobject.factorThru_arrow]
    simp
  map_comp f g := by
    rw [← cancel_mono (stab hG _).arrow, Subobject.factorThru_arrow]
    simp

/-- The inclusion of the tower of stable images. -/
@[simps]
noncomputable def stabTowerι : stabTower hG ⟶ G where
  app n := (stab hG n.unop).arrow

/-- The corestriction of a transition from beyond the stabilisation index to the stable image
is an epimorphism. -/
lemma epi_factorThru_tr (n M : ℕ) (hM : stabIdx hG n ≤ M) (h) :
    Epi ((stab hG n).factorThru (tr G ((le_stabIdx hG n).trans hM)) h) :=
  Subobject.epi_factorThru_of_eq_imageSubobject _ (stab_eq hG n M hM) h

end ArtinianTower

open ArtinianTower in
/-- **Towers whose images stabilise are Mittag-Leffler**: the stable images form a subtower
with epimorphic transitions through which the transitions factor. -/
theorem isMittagLefflerTower_of_imagesStabilize {G : ℕᵒᵖ ⥤ C} (hG : ImagesStabilize G) :
    IsMittagLefflerTower G := by
  refine ⟨stabTower hG, stabTowerι hG, fun n ↦ ?_, fun n ↦ ?_, fun n ↦ ?_⟩
  · exact inferInstanceAs (Mono (stab hG n).arrow)
  · let M := max (stabIdx hG n) (stabIdx hG (n + 1))
    have hn : stabIdx hG n ≤ M := le_max_left _ _
    have hn' : stabIdx hG (n + 1) ≤ M := le_max_right _ _
    have hf : (stab hG (n + 1)).Factors (tr G ((le_stabIdx hG (n + 1)).trans hn')) := by
      rw [stab_eq hG (n + 1) M hn']; exact factors_imageSubobject _
    have hg : (stab hG n).Factors (tr G ((le_stabIdx hG n).trans hn)) := by
      rw [stab_eq hG n M hn]; exact factors_imageSubobject _
    have := epi_factorThru_tr hG n M hn hg
    refine epi_of_epi_fac (f := (stab hG (n + 1)).factorThru _ hf)
      (h := (stab hG n).factorThru _ hg) ?_
    rw [← cancel_mono (stab hG n).arrow]
    simp [tr_comp]
  · have hf : (stab hG n).Factors (tr G (le_stabIdx hG n)) := factors_imageSubobject _
    refine ⟨stabIdx hG n, le_stabIdx hG n, (stab hG n).factorThru _ hf, ?_⟩
    simp

open ArtinianTower in
/-- **Towers of Artinian objects are Mittag-Leffler** (e.g. towers of finite length objects in
an abelian category): the images of `G m ⟶ G n` stabilise. -/
theorem isMittagLefflerTower_of_isArtinianObject
    [∀ n : ℕ, IsArtinianObject (G.obj (op n))] : IsMittagLefflerTower G :=
  isMittagLefflerTower_of_imagesStabilize (imagesStabilize_of_isArtinianObject G)

end CategoryTheory.Limits
