/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.FinCategory.Basic

import WeilConjectures.CategoryTheory.FilteredColimitCategoryFiniteLift
import WeilConjectures.CategoryTheory.FilteredColimitCategoryListEquality
import WeilConjectures.CategoryTheory.FilteredColimitCategoryFiniteFunctorLift

/-! # Finite diagrams and Hom descent for filtered category colimits -/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph and its
finite-diagram remark, with Categories, Section Tag 04AX.
(blueprint: lem-weil-pbc-filtered-colimit-category-descent).

Proof: The object and arrow cocones are colimits of sets. Represent any finite
lists by stage elements and take a common stage using filteredness. For each
source, target, composition and identity relation holding in the colimit, the
equality criterion for filtered colimits of sets supplies a further stage where
it holds. There are only finitely many indices and relations, so another common
refinement makes all relations hold simultaneously. The same argument applied to
two finite lists proves eventual equality of the lists of representatives.

For a functor from a finite category, enumerate all objects and all arrows. Apply
the finite lifting assertion with their endpoint relations and all identity and
composition relations. The lifted lists define a functor, since these are exactly
its functor laws. Equality with the original functor follows from its object and
arrow images, including the endpoint transports.

For an arrow between the images of X,Y at j, choose an arrow representative.
Take a common stage receiving j and its representative stage. The endpoint
identities in the object colimit become literal at a further stage; transport the
representative along these endpoint equalities. This gives the required Hom
representative. If two Hom representatives have the same image, equality in the
arrow colimit gives a common refinement where their entire arrows agree. Equalize
the resulting parallel maps out of j at one further stage by filteredness. This
proves the forward equality criterion with commuting maps out of j. Conversely,
commuting refinements and equality of stage arrows give equal images by functor
compatibility. The argument also applies to empty lists and to the empty finite
category: filteredness supplies a stage even when no representatives are needed. -/
theorem filteredColimit_category_descent
    (J : Type z) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z}) :
    let O := colimit (F ⋙ Cat.objects)
    ∀ (_s : Category.{z} O) (V : ∀ j : J, F.obj j ⥤ O),
      ((∀ (j : J) (X : F.obj j), (V j).obj X = colimit.ι (F ⋙ Cat.objects) j X) ∧
      (∀ (j k : J) (f : j ⟶ k), (F.map f).toFunctor ⋙ V k = V j) ∧
      (∃ (a : Cocone (F ⋙ Cat.arrows)) (e : a.pt ≃ Arrow O),
        Nonempty (IsColimit a) ∧
          ∀ (j : J) (f : Arrow (F.obj j)),
            e (a.ι.app j f) = (V j).mapArrow.obj f)) →
      (∀ (n m : ℕ) (X : Fin n → O) (A : Fin m → Arrow O),
        ∃ (j : J) (Xj : Fin n → F.obj j) (Aj : Fin m → Arrow (F.obj j)),
          (∀ q, (V j).obj (Xj q) = X q) ∧
          (∀ p, (V j).mapArrow.obj (Aj p) = A p) ∧
          (∀ p q, (A p).left = X q → (Aj p).left = Xj q) ∧
          (∀ p q, (A p).right = X q → (Aj p).right = Xj q) ∧
          (∀ p q r (h : (A p).right = (A q).left),
            Arrow.mk ((A p).hom ≫ eqToHom h ≫ (A q).hom) = A r →
            ∃ hj : (Aj p).right = (Aj q).left,
              Arrow.mk ((Aj p).hom ≫ eqToHom hj ≫ (Aj q).hom) = Aj r) ∧
          (∀ p q, A p = Arrow.mk (𝟙 (X q)) → Aj p = Arrow.mk (𝟙 (Xj q)))) ∧
      (∀ (n m : ℕ) (j k : J)
        (Xj : Fin n → F.obj j) (Xk : Fin n → F.obj k)
        (Aj : Fin m → Arrow (F.obj j)) (Ak : Fin m → Arrow (F.obj k)),
        (∀ q, (V j).obj (Xj q) = (V k).obj (Xk q)) →
        (∀ p, (V j).mapArrow.obj (Aj p) = (V k).mapArrow.obj (Ak p)) →
        ∃ (t : J) (f : j ⟶ t) (g : k ⟶ t),
          (∀ q, (F.map f).toFunctor.obj (Xj q) = (F.map g).toFunctor.obj (Xk q)) ∧
          (∀ p, (F.map f).toFunctor.mapArrow.obj (Aj p) =
            (F.map g).toFunctor.mapArrow.obj (Ak p))) ∧
      (∀ (D : Type z) [SmallCategory D] [FinCategory D] (d : D ⥤ O),
        ∃ (j : J) (dj : D ⥤ F.obj j), dj ⋙ V j = d) ∧
      (∀ (j : J) (X Y : F.obj j),
        (∀ b : (V j).obj X ⟶ (V j).obj Y,
          ∃ (k : J) (f : j ⟶ k)
            (g : (F.map f).toFunctor.obj X ⟶ (F.map f).toFunctor.obj Y),
            Arrow.mk ((V k).map g) = Arrow.mk b) ∧
        (∀ (k l : J) (f : j ⟶ k) (g : j ⟶ l)
          (a : (F.map f).toFunctor.obj X ⟶ (F.map f).toFunctor.obj Y)
          (b : (F.map g).toFunctor.obj X ⟶ (F.map g).toFunctor.obj Y),
          Arrow.mk ((V k).map a) = Arrow.mk ((V l).map b) ↔
          ∃ (t : J) (h : k ⟶ t) (i : l ⟶ t),
            f ≫ h = g ≫ i ∧
              Arrow.mk ((F.map h).toFunctor.map a) =
                Arrow.mk ((F.map i).toFunctor.map b))) := by
  classical
  intro O s V h
  have hLift := filteredColimit_category_finite_lift J F s V h
  have hEqual := filteredColimit_category_list_equality J F s V h
  have hFinite := filteredColimit_category_finite_functor_lift J F s V hLift
  refine ⟨hLift, hEqual, hFinite, ?_⟩
  intro j X Y
  constructor
  · intro b
    obtain ⟨i, Xi, Ai, hx, ha, hs, ht, _⟩ :=
      hLift 2 1 ![(V j).obj X, (V j).obj Y] ![Arrow.mk b]
    obtain ⟨t, u, v, he, _⟩ := hEqual 2 0 i j Xi ![X, Y]
      (Fin.elim0) (Fin.elim0) (fun q ↦ by
        refine Fin.cases ?_ (fun q ↦ ?_) q
        · exact hx 0
        · have hq : q = 0 := Fin.eq_zero q
          subst q
          exact hx 1) (fun p ↦ Fin.elim0 p)
    let c := (F.map u).toFunctor.mapArrow.obj (Ai 0)
    have hcl : c.left = (F.map v).toFunctor.obj X := by
      change (F.map u).toFunctor.obj (Ai 0).left = _
      rw [hs 0 0 rfl]
      exact he 0
    have hcr : c.right = (F.map v).toFunctor.obj Y := by
      change (F.map u).toFunctor.obj (Ai 0).right = _
      rw [ht 0 1 rfl]
      exact he 1
    let a := eqToHom hcl.symm ≫ c.hom ≫ eqToHom hcr
    have hac : Arrow.mk a = c := by
      dsimp only [a]
      rw [Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]
      exact Arrow.mk_eq c
    refine ⟨t, v, a, ?_⟩
    have hc := congrArg (fun c : Arrow (F.obj t) ↦ (V t).mapArrow.obj c) hac
    have hi := congrArg (fun H : F.obj i ⥤ O ↦ H.mapArrow.obj (Ai 0)) (h.2.1 i t u)
    exact hc.trans (hi.trans (ha 0))
  · intro k l f g a b
    constructor
    · intro hab
      obtain ⟨t, u, v, _, he⟩ := hEqual 0 1 k l (Fin.elim0) (Fin.elim0)
        (fun _ ↦ Arrow.mk a) (fun _ ↦ Arrow.mk b) (fun q ↦ Fin.elim0 q) (fun _ ↦ hab)
      let w := IsFiltered.coeqHom (f ≫ u) (g ≫ v)
      refine ⟨IsFiltered.coeq (f ≫ u) (g ≫ v), u ≫ w, v ≫ w, ?_, ?_⟩
      · simpa only [Category.assoc] using IsFiltered.coeq_condition (f ≫ u) (g ≫ v)
      · have hh := congrArg
          (fun c : Arrow (F.obj t) ↦ (F.map w).toFunctor.mapArrow.obj c) (he 0)
        change Arrow.mk ((F.map w).toFunctor.map ((F.map u).toFunctor.map a)) =
          Arrow.mk ((F.map w).toFunctor.map ((F.map v).toFunctor.map b)) at hh
        have hu := congrArg (fun H : F.obj k ⥤ F.obj (IsFiltered.coeq (f ≫ u) (g ≫ v)) ↦
          H.mapArrow.obj (Arrow.mk a)) (congrArg Cat.Hom.toFunctor (F.map_comp u w))
        have hv := congrArg (fun H : F.obj l ⥤ F.obj (IsFiltered.coeq (f ≫ u) (g ≫ v)) ↦
          H.mapArrow.obj (Arrow.mk b)) (congrArg Cat.Hom.toFunctor (F.map_comp v w))
        exact hu.trans (hh.trans hv.symm)
    · rintro ⟨t, u, v, huv, hab⟩
      have hk := congrArg
        (fun H : F.obj k ⥤ O ↦ H.mapArrow.obj (Arrow.mk a)) (h.2.1 k t u)
      have hl := congrArg
        (fun H : F.obj l ⥤ O ↦ H.mapArrow.obj (Arrow.mk b)) (h.2.1 l t v)
      have he := congrArg (fun c : Arrow (F.obj t) ↦ (V t).mapArrow.obj c) hab
      exact hk.symm.trans (he.trans hl)

end CategoryTheory
