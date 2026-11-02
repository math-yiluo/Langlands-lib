import Langlands.Global.FiniteAdeleLevel
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Topology.Category.TopCommRingCat

/-! # The actual finite-adelic level diagram and its canonical cocone -/

noncomputable section

universe u

open IsDedekindDomain CategoryTheory Limits

namespace Langlands.Global

variable (R K : Type u) [CommRing R] [IsDedekindDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Actual finite-adelic levels, ordered by inclusion, as topological commutative rings. -/
def finiteAdeleLevelDiagram : Finset (HeightOneSpectrum R) ⥤ TopCommRingCat.{u} where
  obj S := TopCommRingCat.of (finiteAdeleLevel R K S)
  map {S T} h := ⟨finiteAdeleLevelMap R K (leOfHom h), by
    apply Continuous.subtype_mk
    exact continuous_subtype_val⟩
  map_id _ := by
    apply Subtype.ext
    ext a
    rfl
  map_comp _ _ := by
    apply Subtype.ext
    ext a
    rfl

/-- The ambient finite adele ring, with its actual continuous level inclusions. -/
def finiteAdeleLevelCocone : Cocone (finiteAdeleLevelDiagram R K) where
  pt := TopCommRingCat.of (FiniteAdeleRing R K)
  ι :=
    { app := fun S => ⟨(finiteAdeleLevel R K S).subtype, continuous_subtype_val⟩
      naturality := by
        intro S T h
        apply Subtype.ext
        ext a
        rfl }

/-- The same actual level diagram after forgetting topology. -/
def finiteAdeleLevelRingDiagram : Finset (HeightOneSpectrum R) ⥤ CommRingCat.{u} :=
  finiteAdeleLevelDiagram R K ⋙ forget₂ TopCommRingCat CommRingCat

/-- The same canonical cocone in the category of commutative rings. -/
def finiteAdeleLevelRingCocone : Cocone (finiteAdeleLevelRingDiagram R K) :=
  (forget₂ TopCommRingCat CommRingCat).mapCocone (finiteAdeleLevelCocone R K)

end Langlands.Global
