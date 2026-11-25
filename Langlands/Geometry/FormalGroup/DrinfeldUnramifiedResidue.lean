import Langlands.Geometry.FormalGroup.DrinfeldActionNaturality
import Langlands.Galois.Local.SeparableUnramifiedCompletion

/-! # Drinfeld's framed functor over the actual maximal unramified residue field -/

noncomputable section

universe u s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralSimple ModuleLaw
open Langlands.LocalGalois.Separable

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}

/-- The height-d² special frames over the residue field of the actual completed
maximal unramified scalar base. -/
abbrev UnramifiedFrame (π : 𝒪[K]) :=
  SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
    (R := UnramifiedCompletion.Residue K) π

variable {π : 𝒪[K]} (Φ : UnramifiedFrame (ι := ι) π)

/-- Over the original scalar `Nilp`, use the comparison classes whose residue
maps start at the actual maximal unramified residue field. -/
def unramifiedFunctor : Nilp.{u, u} 𝒪[K] π ⥤ Type (u + 1) :=
  comparisonClassFunctor (R := 𝒪[K]) Φ

variable (c : Φ.val.MatrixCoordinates)

local instance : ExpChar (UnramifiedCompletion.Residue K)
    (DrinfeldResidue.exists_expChar_card K (UnramifiedCompletion.Residue K)).choose :=
  (DrinfeldResidue.exists_expChar_card K (UnramifiedCompletion.Residue K)).choose_spec.choose_spec.2.1

/-- Drinfeld's action on the functor with the original scalar Nilp and actual
unramified residue field. The positive characteristic and residue-cardinal
power are supplied by finite-field arithmetic. -/
def unramifiedAction : GL (Fin (reducedDegree K D)) K × Dˣ →*
    Aut (unramifiedFunctor Φ) := by
  let h := DrinfeldResidue.exists_expChar_card K (UnramifiedCompletion.Residue K)
  exact actionHom (R := 𝒪[K]) h.choose h.choose_spec.choose_spec.2.2 c

variable {A : Nilp.{u, u} 𝒪[K] π} (g : GL (Fin (reducedDegree K D)) K × Dˣ)
variable (q : ComparisonClass Φ A)

/-- The specialized action has the printed inverse Frobenius shift on the
varying residue homomorphism. -/
theorem unramifiedAction_residueMap :
    ((unramifiedAction Φ c g).asIso.hom.app A q).residueMap =
      DrinfeldResidue.shift (DrinfeldAction.exponent K D g) q.residueMap := by
  unfold unramifiedAction
  apply ComparisonClass.act_residueMap

/-- The specialized action conjugates the original target's order action. -/
theorem unramifiedAction_targetClass :
    ((unramifiedAction Φ c g).asIso.hom.app A q).targetClass =
      q.targetClass.twistDivisionUnit g.2 := by
  unfold unramifiedAction
  apply ComparisonClass.act_targetClass

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
