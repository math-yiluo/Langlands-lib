import Langlands.Representation.Aubert.General.CanonicalRationalTheorem17Targets
import Langlands.Representation.Aubert.General.RationalInducedWeylConjugacyTarget
import Langlands.Representation.Aubert.General.RationalCorollaryTargets
import Langlands.Representation.Aubert.General.PrerequisiteStatements
import Langlands.Representation.CuspidalSupport.RationalWholeCuspidalDecompositionStatement

/-! # Reductions of the canonical targets of Théorème 1.7 and Corollaire 1.10

Five implication statements on the canonical actual rational-point families.
Each one says that a canonical target of Aubert's Théorème 1.7 or
Corollaire 1.10 follows from named published targets: induced K0 Weyl
conjugacy (Aubert (1.2)), its class form, the two finite-length-implies-
admissible targets (Renard VI.6.3), rank-one self-association and the
whole-category cuspidal splitting (Renard VI.3.5). No proof is supplied here.
-/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Reduction of Théorème 1.7 (2) (compatibility of the canonical actual
duality operators with normalized parabolic induction) to induced K0 Weyl
conjugacy. No proof is supplied. -/
def CanonicalRationalInductionCompatibilityReductionStatement : Prop :=
  RationalInducedK0WeylConjugacyStatement.{u, v} →
    CanonicalRationalInductionCompatibilityStatement.{u, v}

/-- Reduction of Théorème 1.7 (3) (involutivity `D_G ∘ D_G = id` of the
canonical actual operator) to induced K0 Weyl conjugacy. No proof is
supplied. -/
def CanonicalRationalInvolutivityReductionStatement : Prop :=
  RationalInducedK0WeylConjugacyStatement.{u, v} →
    CanonicalRationalInvolutivityStatement.{u, v}

/-- Reduction of Corollaire 1.10 (a) for the canonical actual families to
induced K0 Weyl conjugacy. No proof is supplied. -/
def CanonicalRationalCorollary110aReductionStatement : Prop :=
  RationalInducedK0WeylConjugacyStatement.{u, v} →
    CanonicalRationalCorollary110aStatement.{u, v}

/-- Reduction of Théorème 1.7 (1) (commutation of the canonical actual
operator with the smooth contragredient) to the class form of induced Weyl
conjugacy and the two finite-length-implies-admissible targets (Renard VI.6.3,
for `G(F)` and for every dynamic Levi `Z(χ)(F)`) at carrier universe
`max (u + 1) v`. No proof is supplied. -/
def CanonicalRationalContragredientCommutationReductionStatement : Prop :=
  RationalInducedClassWeylConjugacyStatement.{u, v} →
    RationalPointsFiniteLengthAdmissibleStatement.{u, max (u + 1) v} →
      DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v} →
        CanonicalRationalContragredientCommutationStatement.{u, v}

/-- Reduction of Corollaire 1.10 (b) for the canonical actual families to
rank-one self-association, the whole-category cuspidal decomposition of
Renard VI.3.5 at carrier universe `max (u + 1) v` and induced K0 Weyl
conjugacy. No proof is supplied. -/
def CanonicalRationalCorollary110bReductionStatement : Prop :=
  RationalRankOneSelfAssociationStatement.{u, v} →
    CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
      RationalInducedK0WeylConjugacyStatement.{u, v} →
        CanonicalRationalCorollary110bStatement.{u, v}

end Langlands.Aubert.General.RationalPointFamily
