import Langlands.CategoryTheory.EquivariantDiagramFunctor
import Mathlib.CategoryTheory.Grothendieck

/-! # A functor-category realization of varying-group equivariant diagrams -/

universe uG uI vI uC vC

namespace Langlands.EquivariantDiagram

open CategoryTheory

variable {I : Type uI} [Category.{vI} I] (D : I ⥤ GrpCat.{uG})
variable (C : Type uC) [Category.{vC} C]

/-- The diagram of single-object categories attached to the group diagram. -/
abbrev groupCategoryDiagram : I ⥤ Cat.{uG, 0} where
  obj i := Cat.of (SingleObj (D.obj i))
  map f := (SingleObj.mapHom _ _ (D.map f).hom).toCatHom
  map_id i := by rw [D.map_id]; rfl
  map_comp f g := by rw [D.map_comp]; rfl

/-- The Grothendieck category recording both transitions and fiber group elements. -/
abbrev Index := Grothendieck (groupCategoryDiagram D)

namespace Index

variable {D}

/-- The group element of a Grothendieck arrow, with its group type exposed. -/
def element {x y : Index D} (f : x ⟶ y) : D.obj y.base := f.fiber

@[simp] theorem id_element (x : Index D) : element (𝟙 x) = 1 := rfl

@[simp] theorem comp_element {x y z : Index D} (f : x ⟶ y) (g : y ⟶ z) :
    element (f ≫ g) = element g * (D.map g.base).hom (element f) := by
  dsimp [element, Grothendieck.comp, groupCategoryDiagram]
  change (element g * (D.map g.base).hom (element f)) * 1 = _
  exact mul_one _

@[ext] theorem hom_ext {x y : Index D} {f g : x ⟶ y}
    (hb : f.base = g.base) (he : element f = element g) : f = g := by
  cases f
  cases g
  dsimp [element] at hb he
  cases hb
  cases he
  rfl

/-- The base category embeds by assigning the identity group element to every transition. -/
def inclusion : I ⥤ Index D where
  obj i := ⟨i, SingleObj.star (D.obj i)⟩
  map {i j} f := ⟨f, (1 : D.obj j)⟩
  map_id i := by
    apply hom_ext (by rfl)
    rfl
  map_comp {i j k} f g := by
    apply hom_ext (by rfl)
    rw [comp_element]
    change (1 : D.obj k) = 1 * (D.map g).hom 1
    simp

@[simp] theorem inclusion_map_element {i j : I} (f : i ⟶ j) :
    element ((inclusion (D := D)).map f) = 1 := rfl

@[simp] theorem inclusion_map_base {i j : I} (f : i ⟶ j) :
    ((inclusion (D := D)).map f).base = f := rfl

/-- Fiber group elements act as endomorphisms through Mathlib's fiber inclusion. -/
def groupMap (i : I) : D.obj i →* End ((inclusion (D := D)).obj i) :=
  ((Grothendieck.ι (groupCategoryDiagram D) i).mapEnd (SingleObj.star (D.obj i))).comp
    (SingleObj.toEnd (D.obj i)).toMonoidHom

@[simp] theorem groupMap_base (i : I) (g : D.obj i) : (groupMap i g).base = 𝟙 i := rfl

@[simp] theorem groupMap_element (i : I) (g : D.obj i) : element (groupMap i g) = g := by
  change g * 1 = g
  simp

@[reassoc] theorem comm {i j : I} (f : i ⟶ j) (g : D.obj i) :
    groupMap i g ≫ (inclusion (D := D)).map f =
      (inclusion (D := D)).map f ≫ groupMap j ((D.map f).hom g) := by
  apply hom_ext
  · change (𝟙 i) ≫ f = f ≫ 𝟙 j
    simp
  · simp only [comp_element, groupMap_base, groupMap_element,
      inclusion_map_element, inclusion_map_base, map_one, one_mul]
    exact (mul_one _).symm

end Index

variable {D C}

/-- Read an equivariant diagram as a functor on the Grothendieck category. -/
def toIndexFunctor (M : EquivariantDiagram D C) : Index D ⥤ C where
  obj x := M.obj.obj x.base
  map {x y} f := M.obj.map f.base ≫ M.ρ y.base (Index.element f)
  map_id x := by
    simp only [Grothendieck.id_base, Index.id_element, M.obj.map_id, map_one, Category.id_comp]
    rfl
  map_comp {x y z} f g := by
    simp only [Grothendieck.comp_base, Index.comp_element, M.obj.map_comp, map_mul]
    change (M.obj.map f.base ≫ M.obj.map g.base) ≫
        (M.ρ z.base ((D.map g.base).hom (Index.element f)) ≫ M.ρ z.base (Index.element g)) =
      (M.obj.map f.base ≫ M.ρ y.base (Index.element f)) ≫
        (M.obj.map g.base ≫ M.ρ z.base (Index.element g))
    simp only [Category.assoc]
    rw [← Category.assoc (M.obj.map g.base), ← M.comm g.base (Index.element f)]
    simp only [Category.assoc]

@[simp] theorem toIndexFunctor_map_inclusion (M : EquivariantDiagram D C)
    {i j : I} (f : i ⟶ j) :
    (toIndexFunctor M).map ((Index.inclusion (D := D)).map f) = M.obj.map f := by
  change M.obj.map f ≫ M.ρ j 1 = _
  rw [map_one]
  exact Category.comp_id _

@[simp] theorem toIndexFunctor_map_groupMap (M : EquivariantDiagram D C)
    (i : I) (g : D.obj i) :
    (toIndexFunctor M).map (Index.groupMap i g) = M.ρ i g := by
  change M.obj.map (𝟙 i) ≫ M.ρ i (Index.element (Index.groupMap i g)) = _
  rw [Index.groupMap_element, M.obj.map_id, Category.id_comp]

/-- The functor from varying-group diagrams to ordinary functors on their index category. -/
def toFunctor : EquivariantDiagram D C ⥤ (Index D ⥤ C) where
  obj := toIndexFunctor
  map c :=
    { app x := c.hom.app x.base
      naturality {x y} f := by
        change ( _ ≫ _ ) ≫ c.hom.app y.base = c.hom.app x.base ≫ (_ ≫ _)
        rw [Category.assoc, c.comm, ← Category.assoc, c.hom.naturality, Category.assoc] }
  map_id M := by ext; rfl
  map_comp c d := by ext; rfl

/-- Recover the underlying base diagram and the fiber actions of an index functor. -/
def fromIndexFunctor (F : Index D ⥤ C) : EquivariantDiagram D C where
  obj := Index.inclusion ⋙ F
  ρ i := (F.mapEnd _).comp (Index.groupMap i)
  comm f g := by
    change F.map (Index.groupMap _ g) ≫ F.map (Index.inclusion.map f) =
      F.map (Index.inclusion.map f) ≫ F.map (Index.groupMap _ ((D.map f).hom g))
    rw [← F.map_comp, Index.comm, F.map_comp]

/-- Restriction to the base and to the fiber endomorphisms is functorial. -/
def fromFunctor : (Index D ⥤ C) ⥤ EquivariantDiagram D C where
  obj := fromIndexFunctor
  map c :=
    { hom := Functor.whiskerLeft Index.inclusion c
      comm i g := c.naturality (Index.groupMap i g) }
  map_id F := by apply Hom.ext; rfl
  map_comp c d := by apply Hom.ext; rfl

/-- Reading and then recovering a varying-group diagram gives its original data. -/
def fromToIso (M : EquivariantDiagram D C) :
    M ≅ fromIndexFunctor (toIndexFunctor M) where
  hom :=
    { hom :=
        { app i := 𝟙 _
          naturality {i j} f := by
            change M.obj.map f ≫ 𝟙 _ = 𝟙 _ ≫
              (toIndexFunctor M).map (Index.inclusion.map f)
            rw [toIndexFunctor_map_inclusion]
            change M.obj.map f ≫ 𝟙 (M.obj.obj j) = 𝟙 (M.obj.obj i) ≫ M.obj.map f
            simp }
      comm i g := by
        change M.ρ i g ≫ 𝟙 _ = 𝟙 _ ≫ (toIndexFunctor M).map (Index.groupMap i g)
        rw [toIndexFunctor_map_groupMap]
        change M.ρ i g ≫ 𝟙 (M.obj.obj i) = 𝟙 (M.obj.obj i) ≫ M.ρ i g
        simp }
  inv :=
    { hom :=
        { app i := 𝟙 _
          naturality {i j} f := by
            change (toIndexFunctor M).map (Index.inclusion.map f) ≫ 𝟙 _ =
              𝟙 _ ≫ M.obj.map f
            rw [toIndexFunctor_map_inclusion]
            change M.obj.map f ≫ 𝟙 (M.obj.obj j) = 𝟙 (M.obj.obj i) ≫ M.obj.map f
            simp }
      comm i g := by
        change (toIndexFunctor M).map (Index.groupMap i g) ≫ 𝟙 _ = 𝟙 _ ≫ M.ρ i g
        rw [toIndexFunctor_map_groupMap]
        change M.ρ i g ≫ 𝟙 (M.obj.obj i) = 𝟙 (M.obj.obj i) ≫ M.ρ i g
        simp }
  hom_inv_id := by
    apply Hom.ext
    apply NatTrans.ext
    funext i
    change (𝟙 (M.obj.obj i)) ≫ 𝟙 _ = 𝟙 _
    simp
  inv_hom_id := by
    apply Hom.ext
    apply NatTrans.ext
    funext i
    change (𝟙 (M.obj.obj i)) ≫ 𝟙 _ = 𝟙 _
    simp

private theorem indexObject_eq (x : Index D) : Index.inclusion.obj x.base = x := by
  rcases x with ⟨i, s⟩
  cases s
  rfl

/-- Every index functor is naturally recovered from its base and fiber restrictions. -/
def toFromIso (F : Index D ⥤ C) :
    toIndexFunctor (fromIndexFunctor F) ≅ F :=
  NatIso.ofComponents (fun x => F.mapIso (eqToIso (indexObject_eq x))) (by
    intro x y f
    rcases x with ⟨i, xi⟩
    cases xi
    rcases y with ⟨j, yj⟩
    cases yj
    change (F.map (Index.inclusion.map f.base) ≫
      F.map (Index.groupMap j (Index.element f))) ≫ F.map (𝟙 _) =
        F.map (𝟙 _) ≫ F.map f
    simp only [F.map_id, Category.comp_id, Category.id_comp, ← F.map_comp]
    congr 1
    apply Index.hom_ext
    · change f.base ≫ 𝟙 j = f.base
      simp
    · simp only [Index.comp_element, Index.groupMap_element,
        Index.inclusion_map_element, map_one]
      exact mul_one _)

/-- Varying-group equivariant diagrams are an actual ordinary functor category. -/
def indexEquivalence : EquivariantDiagram D C ≌ (Index D ⥤ C) :=
  CategoryTheory.Equivalence.mk toFunctor fromFunctor
    (NatIso.ofComponents fromToIso (by
      intro M N c
      apply Hom.ext
      ext i
      change c.hom.app i ≫ 𝟙 _ = 𝟙 _ ≫ c.hom.app i
      simp))
    (NatIso.ofComponents toFromIso (by
      intro F G c
      ext x
      change c.app (Index.inclusion.obj x.base) ≫ G.map (eqToHom (indexObject_eq x)) =
        F.map (eqToHom (indexObject_eq x)) ≫ c.app x
      exact (c.naturality (eqToHom (indexObject_eq x))).symm))

end Langlands.EquivariantDiagram
