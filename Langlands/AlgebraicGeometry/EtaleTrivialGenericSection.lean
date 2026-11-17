import Langlands.AlgebraicGeometry.ConstantSchemeOpenPullback
import Langlands.AlgebraicGeometry.EtaleConstantGenericSection

/-! # Generic sections from an arbitrary étale constant trivialization -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (C : Over (Spec (CommRingCat.of R))) [IsSeparated C.hom]
  {U : Scheme.{u}} (q : U ⟶ Spec (CommRingCat.of R)) [Etale q] [Surjective q]
  (I : Type u)
  (e : (Over.pullback q).obj C ≅ Over.mk (Sigma.desc (fun _ : I => 𝟙 U)))
  (p : Over.mk (Spec.algebraMap R K) ⟶ C)

include q I e in
/-- A generic section extends uniquely when an arbitrary étale cover makes the
separated parameter constant. -/
theorem existsUnique_section_of_etale_trivialization :
    ∃! s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ C,
      Over.homMk (Spec.algebraMap R K) ≫ s = p := by
  exact existsUnique_section_of_connected_etale_trivialization R K C
    ((connectedEtaleRefinementOpen R U q).ι ≫ q) I
    (connectedEtaleRefinementTrivialization R U q C I e) p

/-- The integral section selected by a supplied étale constant trivialization. -/
def sectionOfEtaleTrivialization : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ C :=
  (existsUnique_section_of_etale_trivialization R K C q I e p).choose

/-- The selected section restricts to the exact original fraction-field point. -/
theorem sectionOfEtaleTrivialization_generic :
    Over.homMk (Spec.algebraMap R K) ≫ sectionOfEtaleTrivialization R K C q I e p = p :=
  (existsUnique_section_of_etale_trivialization R K C q I e p).choose_spec.1

/-- Any section with the required restriction equals the selected section. -/
theorem sectionOfEtaleTrivialization_unique
    (s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ C)
    (hs : Over.homMk (Spec.algebraMap R K) ≫ s = p) :
    s = sectionOfEtaleTrivialization R K C q I e p :=
  (existsUnique_section_of_etale_trivialization R K C q I e p).choose_spec.2 s hs

end Langlands.AlgebraicGeometry
