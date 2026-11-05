import Langlands.GroupScheme.Cartan.IsogenyInduction
import Langlands.GroupScheme.Cartan.InfiniteFieldStructure
import Langlands.GroupScheme.Nilpotent.NoTorusUnipotent
import Langlands.GroupScheme.Lie.UnipotentSemisimpleProof
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSpanningProof
import Langlands.GroupScheme.Lie.SemisimpleIsogenyReduction

/-! # Cartan generation over infinite fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every smooth connected affine group over an infinite field is generated
by its actual Cartan subgroups, on all test schemes. -/
theorem cartanGenerationStatement : CartanGenerationStatement.{u} := by
  intro k _ _ G hsm haff hconn
  let : Smooth G.X.hom := hsm
  let : IsAffineHom G.X.hom := haff
  let : ConnectedSpace G.X.left := hconn
  change IsGeneratedByCartanSubgroups G
  apply smoothConnectedAffineGroup_lieDimension_induction
    IsGeneratedByCartanSubgroups _ G
  intro A _ _ _ hind
  obtain ⟨B, q, hsmB, haffB, hconnB, hq, hcases, hlift⟩ :=
    semisimpleIsogenyReduction k A
  let : Smooth B.X.hom := hsmB
  let : IsAffineHom B.X.hom := haffB
  let : ConnectedSpace B.X.left := hconnB
  apply isGeneratedByCartanSubgroups_of_isogeny q hq hlift
  rcases hcases with hnil | hgeo
  · exact isGeneratedByCartanSubgroups_of_nilpotent nilpotentCentralTorus B hnil
  · apply isGeneratedByCartanSubgroups_of_geometricSemisimpleElement
      Lie.semisimpleCentralizerSmooth Lie.semisimpleCentralizerSpanning hgeo
    · intro H _ _ _ hdim
      apply hind H
      have heq : Lie.dimension A = Lie.dimension B :=
        Lie.finrank_kernel_eq_of_isogeny q hq
      exact hdim.trans_eq heq.symm
    · intro X hX C _ _ j hrep hj
      apply preservesMaximalTori_identityComponent_elementCentralizer_of_cartanLifts
        nilpotentCentralTorus unipotentSemisimpleStatement X j hrep hj
        (Lie.mem_elementCentralizerLie_self X)
      · intro D d hd
        exact hd.structure_of_infiniteField.2
      · intro D d hd Y hY
        exact Lie.isSemisimpleElement_of_closed_subgroup d hd (by rwa [hY])

end Langlands.GroupScheme
