import Langlands.GroupScheme.Absolute.ChevalleyUnipotentEnvelopeStatement
import Langlands.GroupScheme.Absolute.UnipotentTorusBorelsToAllBorelsProof
import Langlands.GroupScheme.Absolute.UnipotentAllBorelsEnvelopeProof

/-! # The unipotent envelope in the Borel subgroups through a maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected unipotent closed subgroup lying in every Borel through a
maximal torus lies in a smooth connected normal unipotent closed subgroup. -/
theorem chevalleyUnipotentEnvelope : ChevalleyUnipotentEnvelopeStatement.{u} := by
  intro k _ _ G _ _ _ T t ht U i hi hU hUc hUu hTB
  exact unipotentAllBorelsEnvelope k G U i hi hU hUc hUu
    (unipotentTorusBorelsToAllBorels k G T t ht U i hi hU hUc hUu hTB)

end Langlands.GroupScheme
