/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Enriched.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Restriction of functors commutes with the internal hom

Let `M` be a monoidal closed category and `e : K ⥤ J` a functor. The restriction
`(e ⋙ -) : (J ⥤ M) ⥤ (K ⥤ M)` is strictly monoidal for the pointwise tensor products, so it has
a comparison map `e ⋙ [P, Q] ⟶ [e ⋙ P, e ⋙ Q]`
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`). At `k : K` it is the map of ends induced
by precomposition with `Under.post e : Under k ⥤ Under (e.obj k)`
(`CategoryTheory.ihomComparison_whiskeringLeft_app_app`), hence an isomorphism as soon as all the
functors `Under.post e` are equivalences (`CategoryTheory.isIso_ihomComparison_whiskeringLeft`).
This applies to the restriction of presheaves along the forgetful functor of a slice category.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open MonoidalCategory Limits Enriched.FunctorCategory MonoidalClosed
open scoped MonoidalClosed.FunctorCategory

variable {M : Type u₁} [Category.{v₁} M] [MonoidalCategory M] [MonoidalClosed M]
  {J : Type u₂} [Category.{v₂} J] {K : Type u₃} [Category.{v₃} K]
  [∀ (F₁ F₂ : J ⥤ M), HasFunctorEnrichedHom M F₁ F₂] [∀ (F₁ F₂ : J ⥤ M), HasEnrichedHom M F₁ F₂]
  [∀ (F₁ F₂ : K ⥤ M), HasFunctorEnrichedHom M F₁ F₂] [∀ (F₁ F₂ : K ⥤ M), HasEnrichedHom M F₁ F₂]
  (e : K ⥤ J)

/-- The comparison map of the restriction along `e`, followed by a projection of the end, is the
projection at the image under `Under.post e`. -/
lemma ihomComparison_whiskeringLeft_app_app_π (P Q : J ⥤ M) (k : K) (k' : Under k) :
    ((Functor.LaxMonoidal.ihomComparison ((Functor.whiskeringLeft K J M).obj e) P).app
        Q).app k ≫ enrichedHomπ M (Under.forget k ⋙ e ⋙ P) (Under.forget k ⋙ e ⋙ Q) k' =
      enrichedHomπ M (Under.forget (e.obj k) ⋙ P) (Under.forget (e.obj k) ⋙ Q)
        ((Under.post e).obj k') := by
  let W := (Functor.whiskeringLeft K J M).obj e
  let κ := (Functor.LaxMonoidal.ihomComparison W P).app Q
  have hev := Functor.LaxMonoidal.ihomComparison_ev W P Q
  have hμ : Functor.LaxMonoidal.μ W P ((ihom P).obj Q) = 𝟙 _ := by
    ext X : 2
    simp [W, Functor.Monoidal.whiskeringLeft_μ_app]
  rw [hμ, Category.id_comp] at hev
  have h : curry (W.obj P ◁ κ ≫ (ihom.ev (W.obj P)).app (W.obj Q)) = κ := by
    rw [← uncurry_eq, curry_uncurry]
  change κ.app k ≫ _ = _
  rw [← h]
  have hc : curry (W.obj P ◁ κ ≫ (ihom.ev (W.obj P)).app (W.obj Q)) =
    MonoidalClosed.FunctorCategory.homEquiv (W.obj P ◁ κ ≫ (ihom.ev (W.obj P)).app (W.obj Q)) := by
    change ((MonoidalClosed.FunctorCategory.adj (W.obj P)).homEquiv _ _) _ = _
    rw [MonoidalClosed.FunctorCategory.adj, Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  rw [hc, show W.obj P ◁ κ ≫ (ihom.ev (W.obj P)).app (W.obj Q) = W.map ((ihom.ev P).app Q) from hev]
  dsimp only [MonoidalClosed.FunctorCategory.homEquiv, Equiv.coe_fn_mk]
  erw [end_.lift_π]
  have hev' : ((ihom.ev P).app Q).app (e.obj k'.right) =
      uncurry (enrichedHomπ M (Under.forget (e.obj k'.right) ⋙ P)
        (Under.forget (e.obj k'.right) ⋙ Q) (Under.mk (𝟙 (e.obj k'.right)))) := by
    change ((MonoidalClosed.FunctorCategory.adj P).counit.app Q).app _ = _
    rw [MonoidalClosed.FunctorCategory.adj, Adjunction.mkOfHomEquiv_counit_app]
    change (MonoidalClosed.FunctorCategory.homEquiv.symm (𝟙 _)).app _ = _
    simp only [MonoidalClosed.FunctorCategory.homEquiv, Equiv.coe_fn_symm_mk, NatTrans.id_app,
      Category.id_comp]
    rfl
  change ((ihom P).obj Q).map (e.map k'.hom) ≫
    curry (((ihom.ev P).app Q).app (e.obj k'.right)) = _
  rw [hev', curry_uncurry]
  change (functorEnrichedHom M P Q).map (e.map k'.hom) ≫ _ = _
  simp only [functorEnrichedHom_map, enrichedHomπ, end_.lift_π, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app]
  simp only [Functor.id_obj, Functor.comp_obj, Under.forget_obj, Under.map_obj_right,
    Under.mk_right, eHomWhiskerRight_id, eHomWhiskerLeft_id, Category.comp_id]
  simp only [Under.map, Comma.mapLeft, Under.post, Under.mk, Discrete.natTrans_app]
  erw [Category.comp_id]
  rfl

instance (P Q : J ⥤ M) (k : K) :
    HasEnrichedHom M (Under.post e (X := k) ⋙ Under.forget (e.obj k) ⋙ P)
      (Under.post e (X := k) ⋙ Under.forget (e.obj k) ⋙ Q) :=
  (inferInstance : HasFunctorEnrichedHom M (e ⋙ P) (e ⋙ Q)) k

/-- The comparison map of the restriction along `e` at `k` is precomposition with
`Under.post e`. -/
lemma ihomComparison_whiskeringLeft_app_app (P Q : J ⥤ M) (k : K) :
    ((Functor.LaxMonoidal.ihomComparison ((Functor.whiskeringLeft K J M).obj e) P).app
        Q).app k =
      precompEnrichedHom M (Under.forget (e.obj k) ⋙ P) (Under.forget (e.obj k) ⋙ Q)
        (Under.post e (X := k)) := by
  refine end_.hom_ext fun k' ↦ ?_
  exact (ihomComparison_whiskeringLeft_app_app_π e P Q k k').trans
    (precompEnrichedHom_π M _ _ _ k').symm

/-- If all the functors `Under.post e` are equivalences, the restriction along `e` commutes with
internal homs. -/
instance isIso_ihomComparison_whiskeringLeft [∀ k : K, (Under.post e (X := k)).IsEquivalence]
    (P : J ⥤ M) :
    IsIso (Functor.LaxMonoidal.ihomComparison
      ((Functor.whiskeringLeft K J M).obj e) P) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Q
  rw [NatTrans.isIso_iff_isIso_app]
  intro k
  rw [ihomComparison_whiskeringLeft_app_app]
  infer_instance

end CategoryTheory
