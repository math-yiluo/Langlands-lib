import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrum
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final

/-! # The actual algebra tail after an initial ring stage -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

variable {J : Type u} [SmallCategory J] (F : J ⥤ CommRingCat.{u}) (j₀ : J)

/-- The actual rings under the initial stage, with their specified algebra
structures, indexed by arrows out of that stage. -/
def initialRingAlgebraDiagram : Under j₀ ⥤ CommAlgCat.{u} (F.obj j₀) :=
  Under.post F ⋙ (commAlgCatEquivUnder (F.obj j₀)).inverse

@[simp]
lemma initialRingAlgebraDiagram_obj (j : Under j₀) :
    (forget₂ (CommAlgCat.{u} (F.obj j₀)) CommRingCat).obj
      ((initialRingAlgebraDiagram F j₀).obj j) = F.obj j.right := rfl

@[simp]
lemma initialRingAlgebraDiagram_map {i j : Under j₀} (r : i ⟶ j) :
    (forget₂ (CommAlgCat.{u} (F.obj j₀)) CommRingCat).map
      ((initialRingAlgebraDiagram F j₀).map r) = F.map r.right := rfl

@[simp]
lemma initialRingAlgebraDiagram_algebraMap (j : Under j₀) :
    algebraMap (F.obj j₀) ((initialRingAlgebraDiagram F j₀).obj j) =
      (F.map j.hom).hom := rfl

variable (c : Cocone F)

/-- The cocone has the original colimit ring, made an algebra through the
original cocone map from the initial stage. -/
def initialRingAlgebraCocone : Cocone (initialRingAlgebraDiagram F j₀) :=
  (commAlgCatEquivUnder (F.obj j₀)).inverse.mapCocone (c.underPost j₀)

@[simp]
lemma initialRingAlgebraCocone_pt :
    (forget₂ (CommAlgCat.{u} (F.obj j₀)) CommRingCat).obj
      (initialRingAlgebraCocone F j₀ c).pt = c.pt := rfl

@[simp]
lemma initialRingAlgebraCocone_algebraMap :
    algebraMap (F.obj j₀) (initialRingAlgebraCocone F j₀ c).pt =
      (c.ι.app j₀).hom := rfl

@[simp]
lemma initialRingAlgebraCocone_ι (j : Under j₀) :
    (forget₂ (CommAlgCat.{u} (F.obj j₀)) CommRingCat).map
      ((initialRingAlgebraCocone F j₀ c).ι.app j) = c.ι.app j.right := rfl

/-- Finality of the under-category tail and the ring/algebra equivalence
prove that the original colimit ring is also the colimit as an initial-stage
algebra. -/
def initialRingAlgebraCoconeIsColimit [IsFiltered J] (hc : IsColimit c) :
    IsColimit (initialRingAlgebraCocone F j₀ c) :=
  isColimitOfPreserves (commAlgCatEquivUnder (F.obj j₀)).inverse (hc.underPost j₀)

@[simp]
lemma initialRing_spectrumStructure (j : (Under j₀)ᵒᵖ) :
    (spectrumStructure (F.obj j₀) (initialRingAlgebraDiagram F j₀)).app j =
      Spec.map (F.map j.unop.hom) := rfl

@[simp]
lemma initialRing_spectrumBaseMap :
    spectrumBaseMap (F.obj j₀) (initialRingAlgebraDiagram F j₀)
      (initialRingAlgebraCocone F j₀ c) = Spec.map (c.ι.app j₀) := rfl

@[simp]
lemma initialRing_spectrumCone_π (j : Under j₀) :
    (spectrumCone (F.obj j₀) (initialRingAlgebraDiagram F j₀)
      (initialRingAlgebraCocone F j₀ c)).π.app (op j) =
        Spec.map (c.ι.app j.right) := rfl

end Langlands.AlgebraicGeometry.SchemeLimitModel
