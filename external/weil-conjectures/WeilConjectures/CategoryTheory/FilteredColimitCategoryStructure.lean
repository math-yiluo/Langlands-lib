/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.FilteredColimitFiberOperations
import WeilConjectures.CategoryTheory.FilteredColimitFiberLaws

/-! # The category structure on the filtered object colimit -/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem fiber_arrow_eq
    {O A : Type z} [Category.{z} O] (src tgt : A → O)
    (e : ∀ X Y : O, (X ⟶ Y) ≃ {a : A // src a = X ∧ tgt a = Y})
    {X Y X' Y' : O} (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : (e _ _ f).val = (e _ _ g).val) : Arrow.mk f = Arrow.mk g := by
  have hx : X = X' := (e _ _ f).property.1.symm.trans
    ((congrArg src h).trans (e _ _ g).property.1)
  have hy : Y = Y' := (e _ _ f).property.2.symm.trans
    ((congrArg tgt h).trans (e _ _ g).property.2)
  subst X'
  subst Y'
  exact congrArg Arrow.mk ((e _ _).injective (Subtype.ext h))

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph, and
Categories, Section Tag 04AX (filtered colimits of sets).
(blueprint: lem-weil-pbc-filtered-colimit-category-structure).

Proof: Let A be the filtered colimit of the sets of stage arrows. The source and
target maps to the object colimit O descend by their compatibility with transition
functors. Identities descend in the same way. Every pair of composable arrows in A
has representatives at a common stage. The equality of their middle objects in O
holds at a further stage by the filtered-colimit equality criterion. Compose there.
Changing representatives does not change the resulting element of A: place both
pairs at a common further stage and use eventual equality on the finitely many
arrows and endpoint equalities. The identity laws and associativity follow by
representing the finitely many arrows at one stage where their endpoint equalities
hold, and applying the corresponding category laws there.

Define Hom(X,Y) to be the arrows in A whose source is X and target is Y. These
fibres, with the descended operations, define a category on O. An arrow with its
endpoints is equivalent to an element of A, giving the required equivalence from
the chosen set colimit cocone to Arrow O. Each stage functor sends an object and
an arrow to its colimit class. Its identity and composition laws follow from the
construction. Compatibility with transition functors follows from the cocone laws
on objects and arrows, and equality of functors follows by extensionality. -/
theorem filteredColimit_category_structure
    (J : Type z) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z}) :
    let O := colimit (F ⋙ Cat.objects)
    ∃ (s : Category.{z} O),
    letI := s
    ∃ V : ∀ j : J, F.obj j ⥤ O,
      (∀ (j : J) (X : F.obj j), (V j).obj X = colimit.ι (F ⋙ Cat.objects) j X) ∧
      (∀ (j k : J) (f : j ⟶ k), (F.map f).toFunctor ⋙ V k = V j) ∧
      (∃ (a : Cocone (F ⋙ Cat.arrows)) (e : a.pt ≃ Arrow O),
        Nonempty (IsColimit a) ∧
          ∀ (j : J) (f : Arrow (F.obj j)),
            e (a.ι.app j f) = (V j).mapArrow.obj f) := by
  obtain ⟨i, c, hi, hc⟩ := filteredColimit_fiber_operations J F
  obtain ⟨hid, hci, hassoc⟩ := filteredColimit_fiber_laws J F i c hi hc
  let s : Category.{z} (colimit (F ⋙ Cat.objects)) :=
    { Hom := FilteredColimitHom F
      id := i
      comp := c
      id_comp := fun f ↦ hid _ _ f
      comp_id := fun f ↦ hci _ _ f
      assoc := fun f g h ↦ hassoc _ _ _ _ f g h }
  let := s
  let e : ∀ X Y : colimit (F ⋙ Cat.objects), (X ⟶ Y) ≃ FilteredColimitHom F X Y :=
    fun _ _ ↦ Equiv.refl _
  have hId : ∀ (j : J) (X : F.obj j),
      (e _ _).symm (filteredColimitHomι F j (𝟙 X)) =
        𝟙 (colimit.ι (F ⋙ Cat.objects) j X) := fun j X ↦ (hi j X).symm
  have hComp : ∀ (j : J) (X Y Z : F.obj j) (f : X ⟶ Y) (g : Y ⟶ Z),
      (e _ _).symm (filteredColimitHomι F j (f ≫ g)) =
        (e _ _).symm (filteredColimitHomι F j f) ≫
          (e _ _).symm (filteredColimitHomι F j g) :=
    fun j X Y Z f g ↦ (hc j X Y Z f g).symm
  let V : ∀ j : J, F.obj j ⥤ colimit (F ⋙ Cat.objects) := fun j ↦
    { obj := fun X ↦ colimit.ι (F ⋙ Cat.objects) j X
      map := fun f ↦ (e _ _).symm (filteredColimitHomι F j f)
      map_id := hId j
      map_comp := fun f g ↦ hComp j _ _ _ f g }
  have hObj : ∀ (j : J) (X : F.obj j),
      (V j).obj X = colimit.ι (F ⋙ Cat.objects) j X := fun _ _ ↦ rfl
  have hCompat : ∀ (j k : J) (f : j ⟶ k), (F.map f).toFunctor ⋙ V k = V j := by
    intro j k f
    refine Functor.ext (fun X ↦
      ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.objects) f) X) ?_
    intro X Y g
    have ha : Arrow.mk (((F.map f).toFunctor ⋙ V k).map g) =
        Arrow.mk ((V j).map g) := by
      apply fiber_arrow_eq (filteredColimitArrowSource F) (filteredColimitArrowTarget F) e
      change (e _ _ ((e _ _).symm (filteredColimitHomι F k
        ((F.map f).toFunctor.map g)))).val =
        (e _ _ ((e _ _).symm (filteredColimitHomι F j g))).val
      simp only [Equiv.apply_symm_apply]
      exact ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.arrows) f) (Arrow.mk g)
    obtain ⟨hx, hy, hm⟩ := (Arrow.mk_eq_mk_iff _ _).mp ha
    exact hm
  let a := colimit.cocone (F ⋙ Cat.arrows)
  let E : a.pt ≃ Arrow (colimit (F ⋙ Cat.objects)) :=
    { toFun := fun b ↦ Arrow.mk ((e _ _).symm ⟨b, rfl, rfl⟩)
      invFun := fun b ↦ (e _ _ b.hom).val
      left_inv := by
        intro b
        exact congrArg Subtype.val ((e _ _).apply_symm_apply ⟨b, rfl, rfl⟩)
      right_inv := by
        intro b
        apply fiber_arrow_eq (filteredColimitArrowSource F) (filteredColimitArrowTarget F) e
        exact congrArg Subtype.val ((e _ _).apply_symm_apply _) }
  refine ⟨s, V, hObj, hCompat, a, E, ⟨colimit.isColimit _⟩, ?_⟩
  intro j b
  apply fiber_arrow_eq (filteredColimitArrowSource F) (filteredColimitArrowTarget F) e
  change (e _ _ ((e _ _).symm _)).val =
    (e _ _ ((e _ _).symm (filteredColimitHomι F j b.hom))).val
  simp only [Equiv.apply_symm_apply]
  change colimit.ι (F ⋙ Cat.arrows) j b =
    colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk b.hom)
  rw [Arrow.mk_eq]

end CategoryTheory
