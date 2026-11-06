import Langlands.GroupScheme.Reductive.TorusDominationStatement
import Langlands.GroupScheme.Reductive.TorusDominationReduction
import Langlands.GroupScheme.Reductive.TorusGenerationProof
import Langlands.GroupScheme.Torus.PowerDomination
import Langlands.GroupScheme.ImageGenerationPointed

/-! # Connected reductive groups over infinite fields are dominated by a torus -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A dense map from a finite power of a torus gives a dense map from a torus. -/
theorem reductiveTorusDomination_of_powerDomination
    (h : ReductiveTorusPowerDominationStatement.{u}) :
    ReductiveTorusDominationStatement.{u} := by
  intro k _ _ G hG
  obtain ⟨P, n, g, hP, hg⟩ := h k G hG
  exact exists_isTorus_dense_of_finitePower hP n g hg

/-- Torus domination follows from generation by finitely many closed subtori. -/
theorem reductiveTorusDomination_of_generation
    (hGen : ReductiveFiniteTorusGenerationStatement.{u}) :
    ReductiveTorusDominationStatement.{u} :=
  reductiveTorusDomination_of_powerDomination
    (reductiveTorusPowerDomination_of_generation hGen ImageGeneration.pointedImageGeneration)

/-- A connected reductive group over an infinite field admits a morphism with dense range
from a torus. -/
theorem reductiveTorusDomination : ReductiveTorusDominationStatement.{u} :=
  reductiveTorusDomination_of_generation reductiveFiniteTorusGeneration

end Langlands.GroupScheme
