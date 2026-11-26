import Langlands.Shimura.PEL.HarrisIntegralRosatiEquations
import Langlands.AbelianScheme.PolarizedFiniteLevel.Data

/-! # Actual Mumford-map expressions in the integral Harris order -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (P : Prerequisites.{u}) {S : Scheme.{u}} {B : AbelianScheme S} (W : DualWitness B)

local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "tau" => D.harrisHodgePELIntegralInvolution C

/-- The order element acting before the Mumford map of the twisting line bundle. -/
def harrisMumfordTwistOrderElement (a : O) (j : ℕ) : O :=
  (j : O) + tau a * a

local notation "DB" =>
  dualAbelianSchemeFromEvaluation B W.hasDual W.geometry P.preservation
    W.inverseBundle W.evaluation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry
local notation "dualInt" =>
  dualAbelianSchemeMapFromEvaluation W.hasDual W.geometry P.preservation
    W.inverseBundle W.evaluation P.stability P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry W.hasDual W.geometry W.inverseBundle W.evaluation
local notation "RosatiEq" =>
  IntegralRosatiEquations D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability B W.hasDual
    W.inverseBundle W.evaluation W.geometry

/-- The actual integral Rosati equations hold for natural multiples of the
given homomorphism. -/
theorem IntegralRosatiEquations.nsmul
    (i : O →+* CategoryTheory.End B) (lam : B ⟶ DB)
    (hm : RosatiEq i lam) (k : ℕ) : RosatiEq i (k • lam) := by
  intro a
  change (i a).asHom ≫ (k • lam) = (k • lam) ≫ dualInt (i (tau a)).asHom
  rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp, hm a]

/-- The homomorphism used in the twisted Mumford degree formula is the action
of one explicit element of the original order followed by the given map. -/
theorem IntegralRosatiEquations.mumfordTwist_eq
    (i : O →+* CategoryTheory.End B) (lam : B ⟶ DB)
    (hm : RosatiEq i lam) (a : O) (j : ℕ) :
    j • lam + (i a).asHom ≫ lam ≫ dualInt (i a).asHom =
      (i (harrisMumfordTwistOrderElement D C a j)).asHom ≫ lam := by
  have ha := hm (tau a)
  change (i (tau a)).asHom ≫ lam = lam ≫ dualInt (i (tau (tau a))).asHom at ha
  rw [(tau).apply_apply] at ha
  have hj : (i (j : O)).asHom = j • 𝟙 B := by
    change (i (j : O)).asHom = (j • (1 : CategoryTheory.End B)).asHom
    rw [nsmul_one]
    exact congrArg CategoryTheory.End.asHom (map_natCast i j)
  rw [harrisMumfordTwistOrderElement, ← ha, i.map_add (j : O) (tau a * a), i.map_mul (tau a) a]
  change _ = ((i (j : O)).asHom + ((i a).asHom ≫ (i (tau a)).asHom)) ≫ lam
  rw [Preadditive.add_comp, Category.assoc, hj, Preadditive.nsmul_comp, Category.id_comp]

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
