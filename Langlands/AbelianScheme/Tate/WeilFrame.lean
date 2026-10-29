import Langlands.Shimura.PEL.ScalarExtension
import Langlands.AbelianScheme.Tate.WeilRationalAlongHom
import Langlands.AbelianScheme.Tate.PrimeToAdelicFrameTransport

/-! # Frames compatible with the actual adelic Weil pairing -/

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme Langlands.Shimura.PEL

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

variable (polarizationMap : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry) (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)

/-- Tensor-algebra-linear frames carrying the scalar extension of the rational
form to the actual full Weil pullback, with an existential twist trivialization. -/
abbrev WeilAdelicFrame :=
  letI := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  letI := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk s) (fun _ => True) h
  letI := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤)
    (fun _ => True) h
  FormIso (D ⊗[ℚ] Global.FiniteAdeles ℚ) (ψ.baseChange (Global.FiniteAdeles ℚ))
    (adelicWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility
      (Over.mk s) polarizationMap (fun _ => True) h)

local notation "FullFrame" => WeilAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ s

/-- Forgetting form compatibility gives an existing actual adelic Tate frame. -/
def weilAdelicFrameUnderlying (eta : FullFrame) :
    letI := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
    AdelicFrame A h i ((Global.FiniteAdeles ℚ) ⊗[ℚ] V) s :=
  eta.1

/-- The right source-similitude action preserves actual Weil compatibility. -/
@[instance_reducible]
def weilAdelicFrameRightAction :
    MulAction (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)ᵐᵒᵖ
      FullFrame := by
  letI := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  letI := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk s) (fun _ => True) h
  letI := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤)
    (fun _ => True) h
  exact inferInstance

/-- The right action has the convention eta times g equals eta composed with g. -/
theorem weilAdelicFrameRightAction_apply
    (g : ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)
    (eta : FullFrame) (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] V) :
    letI := weilAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i V ψ s
    (MulOpposite.op g • eta).1 x = eta.1 (g.1.1 x) := rfl

variable {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- The same construction for actual prime-to-modulus Tate modules and twists. -/
abbrev WeilPrimeToAdelicFrame :=
  letI := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  letI := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp (Over.mk s) hAway
  letI := TateTwist.Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
  FormIso (D ⊗[ℚ] Global.PrimeToFiniteAdeles m)
    (ψ.baseChange (Global.PrimeToFiniteAdeles m))
    (awayAdelicWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility
      (Over.mk s) polarizationMap hAway)

local notation "AwayFrame" => WeilPrimeToAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ s hAway

/-- Forgetting the away form condition retains the actual tensor-linear frame. -/
def weilPrimeToAdelicFrameUnderlying (eta : AwayFrame) :
    letI := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
    PrimeToAdelicFrame A m hAway i ((Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) s :=
  eta.1

/-- Right composition by prime-to-modulus source similitudes. -/
@[instance_reducible]
def weilPrimeToAdelicFrameRightAction :
    MulAction (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)ᵐᵒᵖ
      AwayFrame := by
  letI := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  letI := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp (Over.mk s) hAway
  letI := TateTwist.Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
  exact inferInstance

theorem weilPrimeToAdelicFrameRightAction_apply
    (g : ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)
    (eta : AwayFrame) (x : (Global.PrimeToFiniteAdeles m) ⊗[ℚ] V) :
    letI := weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i V ψ s hAway
    (MulOpposite.op g • eta).1 x = eta.1 (g.1.1 x) := rfl

end Langlands.AbelianScheme.Tate
