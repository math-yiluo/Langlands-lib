import Langlands.GroupScheme.Cartan.FiniteHomReflection
import Langlands.GroupScheme.Lie.SemisimpleIsogenyReductionStatement
import Langlands.GroupScheme.Lie.SmoothIsogenyDimension
import Langlands.GroupScheme.Lie.SemisimpleCentralizerMaximalTori
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSmooth

/-! # Cartan generation from the structural isogeny reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The five structural inputs suffice for the full universe-general Cartan
generation statement. Each input remains an explicit hypothesis. -/
def CartanGenerationIsogenyInductionStatement : Prop :=
  NilpotentCentralTorusStatement.{u} →
    UnipotentSemisimpleStatement.{u} →
    CartanStructureStatement.{u} →
    Lie.SemisimpleCentralizerSpanningStatement.{u} →
    SemisimpleIsogenyReductionStatement.{u} →
    CartanGenerationStatement.{u}

variable {k : Type u} [Field k]

/-- A smooth connected affine nilpotent group generates itself as one of its
Cartan subgroups, using a central maximal torus. -/
theorem isGeneratedByCartanSubgroups_of_nilpotent
    (hstructure : NilpotentCentralTorusStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsNilpotentGroupScheme G) : IsGeneratedByCartanSubgroups G := by
  obtain ⟨T, t, Q, q, ht, hcentral, _⟩ := hstructure k G hG
  exact isGeneratedByCartanSubgroups_of_isCartanSubgroup_id
    (isCartanSubgroup_id_of_central_maximalTorus ht hcentral)

/-- Strong Lie-dimension induction combines the nilpotent and semisimple cases
after an isogeny, then reflects generation to the original group. -/
theorem cartanGeneration_of_isogenyReduction
    (hstructure : NilpotentCentralTorusStatement.{u})
    (hvan : UnipotentSemisimpleStatement.{u})
    (hcartan : CartanStructureStatement.{u})
    (hspanning : Lie.SemisimpleCentralizerSpanningStatement.{u})
    (hreduction : SemisimpleIsogenyReductionStatement.{u}) :
    CartanGenerationStatement.{u} := by
  intro k _ _ G hsm haff hconn
  let : Smooth G.X.hom := hsm
  let : IsAffineHom G.X.hom := haff
  let : ConnectedSpace G.X.left := hconn
  change IsGeneratedByCartanSubgroups G
  apply smoothConnectedAffineGroup_lieDimension_induction
    IsGeneratedByCartanSubgroups _ G
  intro A _ _ _ hind
  obtain ⟨B, q, hsmB, haffB, hconnB, hq, hcases, hlift⟩ := hreduction k A
  let : Smooth B.X.hom := hsmB
  let : IsAffineHom B.X.hom := haffB
  let : ConnectedSpace B.X.left := hconnB
  apply isGeneratedByCartanSubgroups_of_isogeny q hq hlift
  rcases hcases with hnil | hgeo
  · exact isGeneratedByCartanSubgroups_of_nilpotent hstructure B hnil
  · apply isGeneratedByCartanSubgroups_of_geometricSemisimpleElement
      Lie.semisimpleCentralizerSmooth hspanning hgeo
    · intro H _ _ _ hdim
      apply hind H
      have heq : Lie.dimension A = Lie.dimension B :=
        Lie.finrank_kernel_eq_of_isogeny q hq
      exact hdim.trans_eq heq.symm
    · intro X hX C _ _ j hrep hj
      exact preservesMaximalTori_identityComponent_elementCentralizer_of_semisimple
        hstructure hvan hcartan hX j hrep hj

/-- The conditional induction statement holds without any further assumptions. -/
theorem cartanGenerationIsogenyInductionStatement :
    CartanGenerationIsogenyInductionStatement.{u} :=
  cartanGeneration_of_isogenyReduction

end Langlands.GroupScheme
