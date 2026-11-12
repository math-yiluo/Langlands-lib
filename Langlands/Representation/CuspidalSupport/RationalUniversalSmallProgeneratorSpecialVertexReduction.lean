import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorReduction
import Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaDecompositionReduction
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelTwistEquivalenceProof

/-!
# Renard VI.4.1 for the full-restriction Π₁ from the special-vertex inputs

The unconditional target `RationalUniversalSmallProgeneratorStatement` follows from the
existence of one geometric special vertex carrying the structural inputs of the published
VI.2.1 implication. The VI.2.1 implication and both VI.3.2 restriction statements are
published proofs. The special-vertex input is not proved here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme
open Langlands.BruhatTits.SpecialCompact

/-- The special-vertex inputs of VI.2.1 (a) ⇒ (c) imply VI.4.1 for the full-restriction
Π₁, at independent field and carrier universes. -/
def RationalUniversalSmallProgeneratorSpecialVertexReductionStatement : Prop :=
  RationalSpecialVertexCompactInputsStatement.{uF} →
    RationalUniversalSmallProgeneratorStatement.{uF, uV}

/-- VI.4.1 for Π₁ from the special-vertex inputs and the two VI.3.2 restriction
statements, supplied as hypotheses. -/
theorem rationalUniversalSmallProgenerator_of_specialVertexInputs_of_restriction
    (hInputs : RationalSpecialVertexCompactInputsStatement.{uF})
    (hfin : RationalNormKernelFiniteRestrictionStatement.{uF, uV})
    (htw : RationalNormKernelTwistEquivalenceStatement.{uF, max uF uV, max uF uV}) :
    RationalUniversalSmallProgeneratorStatement.{uF, uV} := by
  intro F _ _ _ _ G hG T i hi _ _ _ ν hν hStandard hRoots hU _ π hπ hcusp
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  obtain ⟨D, x, hspecial, hprops, hbasis, hcover⟩ := hInputs F G hG T i hi ν hν
  have hc := rationalCuspidalCompactRestriction F G hG T i hi ν hν hStandard hRoots hU
    D x hspecial hprops hbasis hcover π hcusp
  exact rationalNormKernelSmallProgeneratorReduction G hG π hπ hc hfin htw

/-- The published VI.3.2 (ii) and (iii) proofs discharge the restriction hypotheses. -/
theorem rationalUniversalSmallProgeneratorSpecialVertexReduction :
    RationalUniversalSmallProgeneratorSpecialVertexReductionStatement.{uF, uV} :=
  fun hInputs =>
    rationalUniversalSmallProgenerator_of_specialVertexInputs_of_restriction hInputs
      rationalNormKernelFiniteRestriction rationalNormKernelTwistEquivalence

/-- The joint special-compact existence target implies VI.4.1 for Π₁. -/
theorem rationalUniversalSmallProgenerator_of_jointBasis
    (hJoint : JointSpecialCompactBasisExistenceStatement.{uF}) :
    RationalUniversalSmallProgeneratorStatement.{uF, uV} :=
  rationalUniversalSmallProgeneratorSpecialVertexReduction
    (rationalSpecialVertexCompactInputs_of_jointBasis hJoint)

end Langlands.CuspidalSupport
