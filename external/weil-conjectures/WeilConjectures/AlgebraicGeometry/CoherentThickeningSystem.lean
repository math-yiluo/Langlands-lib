/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Coherent

/-! # Coherent systems on a tower of schemes

Source: Stacks Project, Cohomology of Schemes, Remark 088F
(blueprint: def-weil-pbc-coherent-thickening-system).

The tower is indexed starting at zero. Its objects have coherent terms and pullback
isomorphisms; its arrows are precisely compatible families of linear maps.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Coherent terms with pullback transition isomorphisms on a tower.
Source: Stacks, Remark 088F (blueprint: def-weil-pbc-coherent-thickening-system). -/
structure CoherentThickeningSystem (T : ℕ → Scheme.{u}) (i : ∀ n, T n ⟶ T (n + 1)) where
  term : ∀ n, (T n).Modules
  coherent : ∀ n, RingedSpace.IsCoherent (T n).toRingedSpace (term n)
  comparison : ∀ n, (Scheme.Modules.tensorPullback (i n)).obj (term (n + 1)) ≅ term n

namespace CoherentThickeningSystem

variable {T : ℕ → Scheme.{u}} {i : ∀ n, T n ⟶ T (n + 1)}

/-- Compatible families, with the equation in composition order.
Source: Stacks, Remark 088F (blueprint: def-weil-pbc-coherent-thickening-system). -/
structure Hom (F G : CoherentThickeningSystem T i) where
  app : ∀ n, F.term n ⟶ G.term n
  compatibility : ∀ n,
    (F.comparison n).hom ≫ app n =
      (Scheme.Modules.tensorPullback (i n)).map (app (n + 1)) ≫ (G.comparison n).hom

/-- Identity families satisfy compatibility because pullback preserves identities.
Source: Stacks, Remark 088F (blueprint: def-weil-pbc-coherent-thickening-system). -/
theorem id_compatibility (F : CoherentThickeningSystem T i) (n : ℕ) :
    (F.comparison n).hom ≫ 𝟙 (F.term n) =
      (Scheme.Modules.tensorPullback (i n)).map (𝟙 (F.term (n + 1))) ≫
        (F.comparison n).hom := by
  simp

/-- Composition preserves compatibility: substitute the two compatibility equations,
associate compositions and use preservation of composition by pullback.
Source: Stacks, Remark 088F (blueprint: def-weil-pbc-coherent-thickening-system). -/
theorem comp_compatibility {F G H : CoherentThickeningSystem T i}
    (f : Hom F G) (g : Hom G H) (n : ℕ) :
    (F.comparison n).hom ≫ (f.app n ≫ g.app n) =
      (Scheme.Modules.tensorPullback (i n)).map (f.app (n + 1) ≫ g.app (n + 1)) ≫
        (H.comparison n).hom := by
  rw [Functor.map_comp, ← Category.assoc, f.compatibility n]
  rw [Category.assoc, g.compatibility n, ← Category.assoc]

/-- The identity compatible family.
Source: Stacks, Remark 088F (blueprint: def-weil-pbc-coherent-thickening-system). -/
def identity (F : CoherentThickeningSystem T i) : Hom F F :=
  ⟨fun n ↦ 𝟙 (F.term n), id_compatibility F⟩

/-- Componentwise composition of compatible families.
Source: Stacks, Remark 088F (blueprint: def-weil-pbc-coherent-thickening-system). -/
def composition {F G H : CoherentThickeningSystem T i} (f : Hom F G) (g : Hom G H) :
    Hom F H :=
  ⟨fun n ↦ f.app n ≫ g.app n, comp_compatibility f g⟩

/-- Category laws hold componentwise; the module category laws give each equality,
and equality of families gives equality of compatible arrows by proof irrelevance.
Source: Stacks, Remark 088F (blueprint: def-weil-pbc-coherent-thickening-system). -/
theorem category_laws :
    (∀ (F G : CoherentThickeningSystem T i) (f : Hom F G),
      composition (identity F) f = f) ∧
    (∀ (F G : CoherentThickeningSystem T i) (f : Hom F G),
      composition f (identity G) = f) ∧
    (∀ (F G H K : CoherentThickeningSystem T i) (f : Hom F G) (g : Hom G H) (h : Hom H K),
      composition (composition f g) h = composition f (composition g h)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro F G f
    cases f
    simp only [composition, identity, Category.id_comp]
  · intro F G f
    cases f
    simp only [composition, identity, Category.comp_id]
  · intro F G H K f g h
    cases f
    cases g
    cases h
    simp only [composition, Category.assoc]

/-- The category of coherent systems, with exactly the compatible families as arrows.
Source: Stacks, Remark 088F (blueprint: def-weil-pbc-coherent-thickening-system). -/
instance category : Category (CoherentThickeningSystem T i) where
  Hom := Hom
  id := identity
  comp := composition
  id_comp := fun {F G} f ↦ category_laws.1 F G f
  comp_id := fun {F G} f ↦ category_laws.2.1 F G f
  assoc := fun {F G H K} f g h ↦ category_laws.2.2 F G H K f g h

/-- Evaluation at a level, sending a compatible family to its component.
Source: Stacks, Remark 088F (blueprint: def-weil-pbc-coherent-thickening-system). -/
def evaluation (T : ℕ → Scheme.{u}) (i : ∀ n, T n ⟶ T (n + 1)) (n : ℕ) :
    CoherentThickeningSystem T i ⥤ (T n).Modules where
  obj F := F.term n
  map f := f.app n

end CoherentThickeningSystem
end AlgebraicGeometry
