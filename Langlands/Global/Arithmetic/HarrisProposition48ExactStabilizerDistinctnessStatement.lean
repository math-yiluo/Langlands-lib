import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterData
import Langlands.Automorphic.Unramified.TowerBaseChangeHeckeComponentStatement
import Langlands.Automorphic.Unramified.CyclicPrimeIsobaricBaseChangeTCStatement
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement

/-!
# Distinct Mackey components in the exact-stabilizer form of Proposition 4.8

Under condition (4.12) on the auxiliary character, the Mackey constituents of
a prime cyclic step with `[D : E]` Mackey classes have different local
components above the auxiliary place. This replaces the comparison at a split
supercuspidal place used by the published prime branch: the inputs are the
tower comparison of Hecke components (B6), Arthur–Clozel III.4.2(c) to build
the unitary isobaric chains, and rigidity. The totally complex form uses the
totally complex forms of the three inputs. Proposition definitions only.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified

/-- From the tower comparison of Hecke components (B6), Arthur–Clozel
III.4.2(c) and rigidity: for a problem with exact-stabilizer validity and a
prime cyclic step `D` with `[D : E]` Mackey classes, Mackey constituents of
different double cosets have different components at every place of `D` above
the auxiliary place. -/
def Proposition48ExactStabilizerDistinctnessStatement : Prop :=
  TowerBaseChangeHeckeComponentStatement.{0, 0, uV, uV} →
  CyclicPrimeIsobaricBaseChangeStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityStatement.{0, uV} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryExactStabilizerValid → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D →
      Q.HasDistinctMackeyComponents.{uF, uV} D

/-- The totally complex form of `Proposition48ExactStabilizerDistinctnessStatement`:
the three inputs are replaced by their totally complex forms; the body is
unchanged. -/
def Proposition48ExactStabilizerDistinctnessTCStatement : Prop :=
  TowerBaseChangeHeckeComponentTCStatement.{0, 0, uV, uV} →
  CyclicPrimeIsobaricBaseChangeTCStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryExactStabilizerValid → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D →
      Q.HasDistinctMackeyComponents.{uF, uV} D

end Langlands.Global.Harris
