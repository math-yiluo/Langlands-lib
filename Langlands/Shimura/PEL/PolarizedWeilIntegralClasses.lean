import Langlands.Shimura.PEL.PolarizedWeilLevelClasses
import Langlands.AbelianScheme.IntegralActionRationalIsomorphism
import Langlands.AbelianScheme.Tate.WeilIntegralPolarizationComparison

/-! # Exact integral witnesses for the polarized Weil-level class relation -/

universe u v w uI

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.Shimura.PEL.PolarizedWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  {S : Scheme.{u}} {D : Type v} [Ring D] [Algebra ℚ D] [StarRing D]

local notation "PObj" => PolarizedAction preservation composition unitCoherence
  associativity comparison symmetry stability square universality S D

/-- A supplied integral order action on the same actual representative, agreeing
with its existing rational action on every order element. -/
structure IntegralActionRestriction (O : Subalgebra ℤ D) (X : PObj) where
  action : O →+* CategoryTheory.End X.actionObj.abelianScheme
  agrees : ∀ x : O, homToHom0 (action x) = X.actionObj.action (x : D)

local notation "Restriction" => IntegralActionRestriction preservation composition
  unitCoherence associativity comparison symmetry stability square universality

variable {O : Subalgebra ℤ D} {I : Type uI} [Finite I] (b : Basis I ℤ O)

/-- Exact equivariant integral representatives of the original rational isomorphism. -/
def integralRestrictionIsoData (X Y : PObj) (a : Restriction O X) (a' : Restriction O Y)
    (e : X.actionObj ≅ Y.actionObj) :
    EquivariantRationalIsoIntegralData a.action a'.action
      (RationalAlgebraAction.underlyingIso e) :=
  Rationalization.equivariantIntegralIsoData a.action a'.action b
    (RationalAlgebraAction.underlyingIso e) (by
      intro x
      change comp0 X.actionObj.abelianScheme X.actionObj.abelianScheme
          Y.actionObj.abelianScheme (homToHom0 (a.action x))
          (RationalAlgebraAction.hom0 e.hom) =
        comp0 X.actionObj.abelianScheme Y.actionObj.abelianScheme Y.actionObj.abelianScheme
          (RationalAlgebraAction.hom0 e.hom) (homToHom0 (a'.action x))
      rw [a.agrees, a'.agrees]
      exact RationalAlgebraAction.intertwines e.hom (x : D))

variable (additivity : PairAdditivity preservation composition unitCoherence associativity
  comparison symmetry stability square universality (S := S) (D := D))

local notation "Mult" => Multiple preservation composition unitCoherence associativity
  comparison symmetry stability square universality additivity

/-- Exact integral equivariance, inverse-multiple identities and an exact polarization
cross-multiple equation for the original rational isomorphism and multiplier. -/
def IntegralPolarizedMultiple (X Y : PObj) (a : Restriction O X) (a' : Restriction O Y)
    (q : ℚˣ) (e : X.actionObj ≅ Y.actionObj) : Prop :=
  ∃ d : EquivariantRationalIsoIntegralData a.action a'.action
      (RationalAlgebraAction.underlyingIso e),
    Nonempty (Rationalization.IntegralMultipleData
      (integralDualPullbackHom preservation composition unitCoherence associativity comparison
        symmetry stability X.hasDual Y.hasDual X.geometry Y.geometry
        X.inversePoincare X.evaluation Y.inversePoincare Y.evaluation d.hom Y.polarization)
      X.polarization (((d.homDenom : ℚ) * (d.homDenom : ℚ)) * (q : ℚ)))

local notation "IntegralMult" => IntegralPolarizedMultiple preservation composition
  unitCoherence associativity comparison symmetry stability square universality

include b in
/-- The exact integral formulation preserves and reflects the original geometric equation. -/
theorem multiple_iff_integralPolarizedMultiple
    (X Y : PObj) (a : Restriction O X) (a' : Restriction O Y)
    (q : ℚˣ) (e : X.actionObj ≅ Y.actionObj) :
    Mult X Y q e ↔ IntegralMult X Y a a' q e := by
  constructor
  · intro he
    let d := integralRestrictionIsoData preservation composition unitCoherence associativity
      comparison symmetry stability square universality b X Y a a' e
    refine ⟨d, ?_⟩
    exact (rationalDualPullbackMultiple_iff_integralMultipleData preservation composition
      unitCoherence associativity comparison symmetry stability X.hasDual Y.hasDual
      X.geometry Y.geometry X.inversePoincare X.evaluation Y.inversePoincare Y.evaluation
      (additivity X Y) (q : ℚ) (RationalAlgebraAction.underlyingIso e)
      d.toIntegralIsoData X.polarization Y.polarization).mp he
  · rintro ⟨d, hd⟩
    exact (rationalDualPullbackMultiple_iff_integralMultipleData preservation composition
      unitCoherence associativity comparison symmetry stability X.hasDual Y.hasDual
      X.geometry Y.geometry X.inversePoincare X.evaluation Y.inversePoincare Y.evaluation
      (additivity X Y) (q : ℚ) (RationalAlgebraAction.underlyingIso e)
      d.toIntegralIsoData X.polarization Y.polarization).mpr hd

variable (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]
  [QuasiSeparatedSpace S]

local notation "Data" => LevelData preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu
local notation "mkClass" => classOf preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu additivity
local notation "transport" => levelIso preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu additivity
local notation "restore" => multiple_iff_integralPolarizedMultiple preservation composition
  unitCoherence associativity comparison symmetry stability square universality b additivity

/-- Equality of the existing actual classes is exactly the integral formulation
with the original rational isomorphism, multiplier and actual fixed-orbit transport. -/
theorem classOf_eq_iff_integralPolarizedMultiple
    {K : FiniteAdelicScalarExtensionLevel D V ψ} (x y : Data K)
    (a : Restriction O x.1) (a' : Restriction O y.1) :
    mkClass x = mkClass y ↔
      ∃ (q : ℚˣ) (e : x.1.actionObj ≅ y.1.actionObj)
        (hd : IntegralMult x.1 y.1 a a' q e),
        transport x.1 y.1 K q e ((restore x.1 y.1 a a' q e).mpr hd) x.2 = y.2 := by
  rw [classOf_eq_iff]
  constructor
  · rintro ⟨q, e, he, hxy⟩
    refine ⟨q, e, (restore x.1 y.1 a a' q e).mp he, ?_⟩
    exact hxy
  · rintro ⟨q, e, hd, hxy⟩
    exact ⟨q, e, (restore x.1 y.1 a a' q e).mpr hd, hxy⟩

end Langlands.Shimura.PEL.PolarizedWeilLevel
