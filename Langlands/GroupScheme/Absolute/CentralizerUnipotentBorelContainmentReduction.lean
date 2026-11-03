import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionStatement
import Langlands.GroupScheme.Absolute.NormalUnipotentBorelContainmentStatement
import Langlands.GroupScheme.Absolute.CentralizerUnipotentBorelContainmentStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # Reduction of centralizer Borel containment to two structural statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Ambient Borel containment for normal unipotent subgroups of cocharacter centralizers follows
from the existence of a Borel subgroup of the centralizer inside the ambient Borel and from
containment of normal unipotent subgroups in every Borel subgroup. -/
theorem centralizerUnipotentBorelContainment_of_statements
    (h₁ : CentralizerBorelIntersectionStatement.{u})
    (h₂ : NormalUnipotentBorelContainmentStatement.{u}) :
    CentralizerUnipotentBorelContainmentStatement.{u} := by
  intro k _ _ G _ _ _ χ M j hj hrep hMs hMc U i hi hUs hUc hU hnormal B b hb hχ
  obtain ⟨C, c, hc, hcb⟩ := h₁ k G χ M j hj hrep hMs hMc B b hb hχ
  have : Smooth M.X.hom := hMs
  have : ConnectedSpace M.X.left := hMc
  have : IsAffineHom M.X.hom := hj.isAffineHom
  exact (SubgroupFunctor.range_comp_mono (h₂ k M U i hi hUs hUc hU hnormal C c hc) j).trans hcb

end Langlands.GroupScheme
