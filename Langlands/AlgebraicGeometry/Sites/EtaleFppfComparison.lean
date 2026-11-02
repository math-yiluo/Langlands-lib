import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over

/-! # Restricting fppf sheaves to the big etale topology -/

universe v u w

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Sites

lemma etalePrecoverage_le_fppfPrecoverage :
    Scheme.etalePrecoverage.{u} ≤ Scheme.fppfPrecoverage :=
  Scheme.precoverage_mono fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩

lemma etaleTopology_le_fppfTopology :
    Scheme.etaleTopology.{u} ≤ Scheme.fppfTopology :=
  Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage

lemma etaleTopologyOver_le_fppfTopologyOver (S : Scheme.{u}) :
    Scheme.etaleTopology.over S ≤ Scheme.fppfTopology.over S := by
  intro T R hR
  exact etaleTopology_le_fppfTopology _ hR

/-- Restrict an fppf sheaf to the big etale site on the same slice category. -/
def fppfSheafToEtaleSheaf (S : Scheme.{u}) (A : Type w) [Category.{v} A] :
    Sheaf (Scheme.fppfTopology.over S) A ⥤ Sheaf (Scheme.etaleTopology.over S) A where
  obj F := ⟨F.obj, F.property.of_le (etaleTopologyOver_le_fppfTopologyOver S)⟩
  map η := ⟨η.hom⟩

@[simp]
lemma fppfSheafToEtaleSheaf_obj (S : Scheme.{u}) (A : Type w) [Category.{v} A]
    (F : Sheaf (Scheme.fppfTopology.over S) A) :
    ((fppfSheafToEtaleSheaf S A).obj F).obj = F.obj := rfl

@[simp]
lemma fppfSheafToEtaleSheaf_map {S : Scheme.{u}} {A : Type w} [Category.{v} A]
    {F G : Sheaf (Scheme.fppfTopology.over S) A} (η : F ⟶ G) :
    ((fppfSheafToEtaleSheaf S A).map η).hom = η.hom := rfl

end Langlands.AlgebraicGeometry.Sites
