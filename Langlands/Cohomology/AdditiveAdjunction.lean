import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Additive adjunctions on complexes and homotopy categories

The units and counits are applied degreewise, then passed to the homotopy
quotient. No exactness hypothesis is needed.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory

universe uC vC uD vD uι u

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  (adj : F ⊣ G) {ι : Type uι} (c : ComplexShape ι)

/-- The degreewise unit of an additive adjunction. -/
def complexAdjunctionUnit :
    𝟭 (HomologicalComplex C c) ⟶
      F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c where
  app K :=
    { f i := adj.unit.app (K.X i)
      comm' i j _ := (adj.unit.naturality (K.d i j)).symm }
  naturality _ _ f :=
    HomologicalComplex.hom_ext _ _ fun i => adj.unit.naturality (f.f i)

/-- The degreewise counit of an additive adjunction. -/
def complexAdjunctionCounit :
    G.mapHomologicalComplex c ⋙ F.mapHomologicalComplex c ⟶
      𝟭 (HomologicalComplex D c) where
  app K :=
    { f i := adj.counit.app (K.X i)
      comm' i j _ := (adj.counit.naturality (K.d i j)).symm }
  naturality _ _ f :=
    HomologicalComplex.hom_ext _ _ fun i => adj.counit.naturality (f.f i)

/-- An additive adjunction induces an adjunction on actual complexes. -/
def complexAdjunction :
    F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c where
  unit := complexAdjunctionUnit adj c
  counit := complexAdjunctionCounit adj c
  left_triangle_components K := by
    apply HomologicalComplex.hom_ext
    intro i
    exact adj.left_triangle_components (K.X i)
  right_triangle_components K := by
    apply HomologicalComplex.hom_ext
    intro i
    exact adj.right_triangle_components (K.X i)

@[simp]
theorem complexAdjunction_unit_app_f (K : HomologicalComplex C c) (i : ι) :
    ((complexAdjunction adj c).unit.app K).f i = adj.unit.app (K.X i) := rfl

@[simp]
theorem complexAdjunction_counit_app_f (K : HomologicalComplex D c) (i : ι) :
    ((complexAdjunction adj c).counit.app K).f i = adj.counit.app (K.X i) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise unit passed to the homotopy quotient. -/
def homotopyAdjunctionUnit :
    𝟭 (HomotopyCategory C c) ⟶
      F.mapHomotopyCategory c ⋙ G.mapHomotopyCategory c where
  app K := (HomotopyCategory.quotient C c).map
    ((complexAdjunctionUnit adj c).app K.as)
  naturality := by
    rintro ⟨K⟩ ⟨L⟩ ⟨f : K ⟶ L⟩
    simp only [HomotopyCategory.quot_mk_eq_quotient_map,
      Functor.comp_map, Functor.id_map, Functor.mapHomotopyCategory_map,
      ← Functor.map_comp]
    exact congrArg ((HomotopyCategory.quotient C c).map)
      ((complexAdjunctionUnit adj c).naturality f)

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise counit passed to the homotopy quotient. -/
def homotopyAdjunctionCounit :
    G.mapHomotopyCategory c ⋙ F.mapHomotopyCategory c ⟶
      𝟭 (HomotopyCategory D c) where
  app K := (HomotopyCategory.quotient D c).map
    ((complexAdjunctionCounit adj c).app K.as)
  naturality := by
    rintro ⟨K⟩ ⟨L⟩ ⟨f : K ⟶ L⟩
    simp only [HomotopyCategory.quot_mk_eq_quotient_map,
      Functor.comp_map, Functor.id_map, Functor.mapHomotopyCategory_map,
      ← Functor.map_comp]
    exact congrArg ((HomotopyCategory.quotient D c).map)
      ((complexAdjunctionCounit adj c).naturality f)

set_option backward.isDefEq.respectTransparency false in
/-- An additive adjunction induces an adjunction on actual homotopy categories. -/
def homotopyAdjunction :
    F.mapHomotopyCategory c ⊣ G.mapHomotopyCategory c where
  unit := homotopyAdjunctionUnit adj c
  counit := homotopyAdjunctionCounit adj c
  left_triangle_components := by
    rintro ⟨K⟩
    change (HomotopyCategory.quotient D c).map
        ((F.mapHomologicalComplex c).map ((complexAdjunctionUnit adj c).app K)) ≫
      (HomotopyCategory.quotient D c).map
        ((complexAdjunctionCounit adj c).app ((F.mapHomologicalComplex c).obj K)) = _
    rw [← Functor.map_comp]
    exact (congrArg ((HomotopyCategory.quotient D c).map)
      ((complexAdjunction adj c).left_triangle_components K)).trans
        ((HomotopyCategory.quotient D c).map_id _)
  right_triangle_components := by
    rintro ⟨K⟩
    change (HomotopyCategory.quotient C c).map
        ((complexAdjunctionUnit adj c).app ((G.mapHomologicalComplex c).obj K)) ≫
      (HomotopyCategory.quotient C c).map
        ((G.mapHomologicalComplex c).map ((complexAdjunctionCounit adj c).app K)) = _
    rw [← Functor.map_comp]
    exact (congrArg ((HomotopyCategory.quotient C c).map)
      ((complexAdjunction adj c).right_triangle_components K)).trans
        ((HomotopyCategory.quotient C c).map_id _)

@[simp]
theorem homotopyAdjunction_unit_app_quotient (K : HomologicalComplex C c) :
    (homotopyAdjunction adj c).unit.app ((HomotopyCategory.quotient C c).obj K) =
      (HomotopyCategory.quotient C c).map ((complexAdjunction adj c).unit.app K) := rfl

@[simp]
theorem homotopyAdjunction_counit_app_quotient (K : HomologicalComplex D c) :
    (homotopyAdjunction adj c).counit.app ((HomotopyCategory.quotient D c).obj K) =
      (HomotopyCategory.quotient D c).map ((complexAdjunction adj c).counit.app K) := rfl

section Scalars

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Scalar extension is additive because its right adjoint is additive. -/
instance moduleExtendScalarsAdditive : (ModuleCat.extendScalars.{u, u, u} φ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive

/-- Ordinary extension and restriction of scalars are adjoint on complexes. -/
def extendRestrictScalarsComplexAdjunction :
    (ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex c ⊣
      (ModuleCat.restrictScalars.{u, u, u} φ).mapHomologicalComplex c :=
  complexAdjunction (ModuleCat.extendRestrictScalarsAdj φ) c

/-- Ordinary extension and restriction of scalars are adjoint on homotopy categories. -/
def extendRestrictScalarsHomotopyAdjunction :
    (ModuleCat.extendScalars.{u, u, u} φ).mapHomotopyCategory c ⊣
      (ModuleCat.restrictScalars.{u, u, u} φ).mapHomotopyCategory c :=
  homotopyAdjunction (ModuleCat.extendRestrictScalarsAdj φ) c

end Scalars

end Langlands.Cohomology
