import Langlands.Global.AdelicFiniteVolumeReduction
import Langlands.Global.SplitUnipotentRationalQuotientCompact
import Langlands.Global.SimpleRootBoxCompact

/-! # Finite volume of the norm-one rational quotient from its remaining inputs

Finite volume of `G(F) \ G(𝔸_F)¹` for every smooth connected affine `G` over a number field
follows from seven inputs: the characteristic-zero Levi decomposition, splitness of smooth
connected unipotent groups over perfect fields, triviality of split-unipotent torsors over
affine schemes, good Siegel reduction for connected reductive groups, the modulus formula for
the positive torus on the unipotent radical, negation stability of the relative roots and the
relative root/character complement.
-/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Global.AdelicSiegelFactors

/-- **Finite volume from the remaining inputs.** The seven input propositions together imply
`NormOneRationalQuotientFiniteVolumeStatement`. -/
def NormOneFiniteVolumeInputsStatement : Prop :=
  CharacteristicZeroLeviDecompositionStatement.{u} →
    PerfectFieldUnipotentSplitStatement.{u} →
      SplitUnipotentAffineTorsorStatement.{u} →
        AdelicGoodSiegelReductionStatement.{u} →
          PositiveTorusUnipotentModulusStatement.{u} →
            RelativeRootNegationStatement.{u} →
              RelativeCharacterRootComplementStatement.{u} →
                NormOneRationalQuotientFiniteVolumeStatement.{u}

theorem normOneFiniteVolumeInputsStatement : NormOneFiniteVolumeInputsStatement.{u} := by
  intro hlevi hsplit htor hgood hmod hneg hcompl F _ _ G _ _ hs hc
  have hunip := unipotentRationalQuotientCompact_of_split hsplit htor
  exact isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_levi hlevi hunip
    (connectedReductiveFiniteVolumeStatement_of_siegel hgood
      (siegelProductFiniteMeasureStatement_of_inputs hunip hmod
        (simpleRootBoxCompactStatement_of_rootComplement hneg hcompl))) F G hs hc

end Langlands.Global.AdelicGroupPoints
