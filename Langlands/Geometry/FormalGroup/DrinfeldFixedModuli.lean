import Langlands.Geometry.FormalGroup.DrinfeldFixedFrameMatrices
import Langlands.Geometry.FormalGroup.DrinfeldUnramifiedResidue
import Langlands.Geometry.FormalGroup.DrinfeldActionKernel

/-! # Drinfeld's functor and action with the constructed fixed special frame -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision CentralSimple ModuleLaw DrinfeldFramedAtlas
open Langlands.ClassFieldTheory.Local Langlands.LocalGalois.Separable.UnramifiedCompletion
open _root_.Langlands.Brauer

universe u

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable (hInv : localBrauerInvariant K (classOf (opposite (divisionAlgebraCSA K D))) =
  reciprocalClass (CentralSimple.reducedDegree K D))
variable {π : 𝒪[K]} (hπ : Irreducible π)

attribute [local instance] coefficientAlgebra coefficientScalarTower

local notation "d" => CentralSimple.reducedDegree K D
local notation "Φ" => drinfeldFixedFrame K D hInv hπ
local notation "c" => drinfeldFixedFrameMatrixCoordinates K D hInv hπ
local notation "κ" => Residue K
local notation "hp" => DrinfeldResidue.exists_expChar_card K κ
local notation "p" => Classical.choose hp
local notation "n" => Classical.choose (Classical.choose_spec hp)
local notation "hpdata" => Classical.choose_spec (Classical.choose_spec hp)
local notation "hcard" => And.right (And.right hpdata)

local instance fixedModuliExpChar : ExpChar κ p := And.left (And.right hpdata)

/-- Drinfeld's height-zero functor on affine Nilp with the actual fixed special frame. -/
def drinfeldFixedFunctor : Nilp.{u, u} 𝒪[K] π ⥤ Type (u + 1) := unramifiedFunctor Φ

local notation "G" => drinfeldFixedFunctor K D hInv hπ

/-- The matrix group and the division group act naturally on the actual framed functor. -/
def drinfeldFixedAction : GL (Fin d) K × Dˣ →* Aut G := unramifiedAction Φ c

/-- The natural action factors through the published triviality relations. -/
def drinfeldFixedActionQuotient : (GL (Fin d) K × Dˣ) ⧸ DrinfeldAction.trivialSubgroup K D →* Aut G :=
  actionQuotientHom (R := 𝒪[K]) p hcard c

@[simp]
theorem drinfeldFixedActionQuotient_mk (g : GL (Fin d) K × Dˣ) :
    drinfeldFixedActionQuotient K D hInv hπ (QuotientGroup.mk' (DrinfeldAction.trivialSubgroup K D) g) =
      drinfeldFixedAction K D hInv hπ g := rfl

variable {A : Nilp.{u, u} 𝒪[K] π} (g : GL (Fin (CentralSimple.reducedDegree K D)) K × Dˣ)

/-- The representative action uses the actual fixed matrix coordinates and the proved
relative Frobenius maps. -/
def drinfeldFixedAct (X : DrinfeldFramedAtlas Φ A) : DrinfeldFramedAtlas Φ A :=
  X.act g p hcard
    (fun j => SpecialModule.relativeFrobeniusQuasiIsogeny Φ p (n * j))
    (fun j => ModuleLaw.relativeFrobeniusIsogeny (Φ).val.formalModule p (n * j)) c

@[simp]
theorem drinfeldFixedAction_class (X : DrinfeldFramedAtlas Φ A) :
    (drinfeldFixedAction K D hInv hπ g).hom.app A (comparisonClassOf X) =
      comparisonClassOf (drinfeldFixedAct K D hInv hπ g X) := rfl

/-- The first coordinate of the class transforms by the printed inverse Frobenius shift. -/
theorem drinfeldFixedAction_residueMap (q : ComparisonClass Φ A) :
    ((drinfeldFixedAction K D hInv hπ g).hom.app A q).residueMap =
      DrinfeldResidue.shift (DrinfeldAction.exponent K D g) q.residueMap :=
  unramifiedAction_residueMap Φ c g q

/-- The target of the class transforms by conjugation of its division-order action. -/
theorem drinfeldFixedAction_targetClass (q : ComparisonClass Φ A) :
    ((drinfeldFixedAction K D hInv hπ g).hom.app A q).targetClass =
      q.targetClass.twistDivisionUnit g.2 := unramifiedAction_targetClass Φ c g q

end Langlands.FormalGroup.LocalDivision
