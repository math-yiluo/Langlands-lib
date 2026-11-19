import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerStatement
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerInheritanceStatement
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterAuxiliaryStatement
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerDistinctnessStatement
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerBranchStatement

/-!
# Explicit-input reduction of Harris's Proposition 4.8 under the exact-stabilizer condition

The one-place induction for the exact-stabilizer form of Harris (1998),
Proposition 4.8, with its named inputs, implies
`Proposition48ExactStabilizerStatement` at the universes used by globalization.
Compared with the published `Proposition48ReductionStatement`, the comparison
at a split supercuspidal place is dropped, and the inputs gain the inheritance
of condition (4.12), the parameter statements, distinctness of Mackey
components, the exact-stabilizer branches, supercuspidal descent along cyclic
base change (B5), the tower comparison (B6), Arthur–Clozel III.4.2(c), the
restricted complex-place compatibility and the archimedean bridge. The totally
complex form uses the totally complex forms of the global inputs. Proposition
definitions only.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.GaloisRepresentation

/-- The one-place induction under condition (4.12) and its named arithmetic and
automorphic inputs imply the exact-stabilizer form of Proposition 4.8 at the
universes used by globalization. -/
def Proposition48ExactStabilizerReductionStatement : Prop :=
  (Proposition48ExactStabilizerAuxiliaryRankOneStatement.{uF, uV} ∧
    Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV} ∧
    Proposition48ExactStabilizerParameterUntwistStatement.{uF, uV} ∧
    Proposition48MackeyStepStatement.{uF} ∧
    Proposition48ExactStabilizerMackeyInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerParityInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerDistinctnessStatement.{uF, uV} ∧
    Proposition48ExactStabilizerPrimeBranchStatement.{uF, uV} ∧
    Proposition48ExactStabilizerSingletonBranchStatement.{uF, uV} ∧
    Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} ∧
    CuspidalSpectralRigidityStatement.{0, uV} ∧
    Proposition48IsobaricInvarianceStatement.{uV} ∧
    CyclicRegularInductionStatement.{0, 0, uV, uV} ∧
    CyclicRegularOrbitLiftStatement.{0, 0, uV, uV} ∧
    CyclicStableDescentStatement.{0, 0, uV, uV} ∧
    CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV} ∧
    CyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV} ∧
    TowerBaseChangeHeckeComponentStatement.{0, 0, uV, uV} ∧
    CyclicPrimeIsobaricBaseChangeStatement.{0, 0, uV, uV} ∧
    RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} ∧
    CuspidalComplexParameterBridgeTCStatement.{0}) →
  Proposition48ExactStabilizerStatement.{uF, 0, 0, 0, uV}

/-- The totally complex form of `Proposition48ExactStabilizerReductionStatement`:
the distinctness statement, the two branches, rigidity, isobaric invariance,
the four cyclic inputs, B5, B6 and III.4.2(c) are replaced by their totally
complex forms; the other inputs and the conclusion are unchanged. -/
def Proposition48ExactStabilizerReductionTCStatement : Prop :=
  (Proposition48ExactStabilizerAuxiliaryRankOneStatement.{uF, uV} ∧
    Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV} ∧
    Proposition48ExactStabilizerParameterUntwistStatement.{uF, uV} ∧
    Proposition48MackeyStepStatement.{uF} ∧
    Proposition48ExactStabilizerMackeyInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerParityInheritanceStatement.{uF} ∧
    Proposition48ExactStabilizerDistinctnessTCStatement.{uF, uV} ∧
    Proposition48ExactStabilizerPrimeBranchTCStatement.{uF, uV} ∧
    Proposition48ExactStabilizerSingletonBranchTCStatement.{uF, uV} ∧
    Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} ∧
    CuspidalSpectralRigidityTCStatement.{0, uV} ∧
    Proposition48IsobaricInvarianceTCStatement.{uV} ∧
    CyclicRegularInductionTCStatement.{0, 0, uV, uV} ∧
    CyclicRegularOrbitLiftTCStatement.{0, 0, uV, uV} ∧
    CyclicStableDescentTCStatement.{0, 0, uV, uV} ∧
    CyclicWeakInductionSupercuspidalTCStatement.{0, 0, uV, uV} ∧
    CyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV} ∧
    TowerBaseChangeHeckeComponentTCStatement.{0, 0, uV, uV} ∧
    CyclicPrimeIsobaricBaseChangeTCStatement.{0, 0, uV, uV} ∧
    RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV} ∧
    CuspidalComplexParameterBridgeTCStatement.{0}) →
  Proposition48ExactStabilizerStatement.{uF, 0, 0, 0, uV}

end Langlands.Global.Harris
