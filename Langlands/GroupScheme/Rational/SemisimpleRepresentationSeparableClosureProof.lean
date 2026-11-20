import Langlands.GroupScheme.Rational.SemisimpleRepresentationSeparableClosureStatement
import Langlands.GroupScheme.Rational.SplitHighestWeightBaseChangeProof
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.SplitPinningExistenceProof
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction

/-! # Semisimple representations descend to the separable closure -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every semisimple representation over the algebraic closure of a separable closure
descends to a semisimple representation over the separable closure. -/
theorem reductiveSemisimpleRepresentationSeparableClosure :
    ReductiveSemisimpleRepresentationSeparableClosureStatement.{u} := by
  intro k _ G hG Ks _ _ _ Ka _ _ _
  have : IsSepClosed Ks := IsSepClosure.sep_closed k
  let Gs := (GroupScheme.baseChange (algebraBaseMap k Ks)).obj G
  have hGs : IsConnectedReductive Gs :=
    connectedReductiveFieldExtensionStatement k Ks G hG
  let : Smooth Gs.X.hom := hGs.smooth
  let : IsAffineHom Gs.X.hom := hGs.isAffineHom
  obtain ⟨T, i, hi, hT⟩ := exists_isMaximalTorus_isSplitTorus_of_isSepClosed Gs
  obtain ⟨p⟩ := splitPinningExistence Ks Gs hGs T hT i hi
  exact (splitHighestWeightBaseChange Ks Gs p).2.2.2 Ka

end Langlands.GroupScheme
