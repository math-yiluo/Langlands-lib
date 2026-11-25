import Langlands.Geometry.FormalGroup.DrinfeldFixedModuli
import Langlands.Geometry.FormalGroup.DrinfeldEquivariantRepresentabilityStatement

/-! # Equivariant representability with the constructed fixed Drinfeld frame -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory IsLocalRing ValuativeRel CentralDivision CentralSimple DeligneFormalSpace
open Langlands.ClassFieldTheory.Local Langlands.LocalGalois.Separable
open Langlands.LocalGalois.Separable.UnramifiedCompletion
open _root_.Langlands.Brauer

universe u

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable (hInv : localBrauerInvariant K (classOf (opposite (divisionAlgebraCSA K D))) =
  reciprocalClass (CentralSimple.reducedDegree K D))
variable {π : 𝒪[K]} (hπ : Irreducible π)

local notation "nD" => CentralSimple.reducedDegree K D
local notation "E" => drinfeldUnramifiedField K D
local notation "hE" => drinfeldUnramifiedField_unramified K D
local notation "emb" => drinfeldUnramifiedEmbedding K D hInv
local notation "Φ" => drinfeldFixedFrame K D hInv hπ
local notation "c" => drinfeldFixedFrameMatrixCoordinates K D hInv hπ

/-- Drinfeld's equivariant comparison on the constructed height-zero functor
and the actual completed-base Deligne point functor. -/
def DrinfeldFixedEquivariantRepresentabilityStatement : Prop :=
  letI : NeZero nD := ⟨(reducedDegree_pos K D).ne'⟩
  ∃ e : drinfeldFixedFunctor K D hInv hπ ≅ nilpDeligneCompletedFunctor (d := nD) hπ,
    (∀ (B : Nilp.{u, u} 𝒪[K] π) (q : DrinfeldFramedAtlas.ComparisonClass Φ B),
      (Nilp.quotientO 𝒪[K] B).comp (e.hom.app B q).2 =
        q.residueMap.comp (IsScalarTower.toAlgHom 𝒪[K] (Integers K) (Residue K))) ∧
    ∀ g : GL (Fin nD) K × Dˣ,
      (drinfeldFixedAction K D hInv hπ g).asIso.hom ≫ e.hom =
        e.hom ≫ (nilpDeligneCompletedDivisionAction (D := D) hπ g).asIso.hom

include hπ in
/-- The cyclic hypotheses for the chosen embedded field follow from the original invariant. -/
theorem drinfeldFixedCyclicRelations : HasDrinfeldCyclicRelations emb π :=
  ⟨drinfeldArithmeticUniformizer K D hInv hπ, finiteUnramifiedFrobenius K E hE,
    drinfeldArithmeticUniformizer_pow K D hInv hπ,
    drinfeldArithmeticUniformizer_mul K D hInv hπ,
    subfieldArithmeticFrobenius_sub_lt_one K D E emb hE⟩

/-- The comparison theorem for a supplied frame yields the specialized target
with the constructed frame and the verified cyclic relations. -/
theorem drinfeldFixedEquivariantRepresentability_of_general
    (h : DrinfeldEquivariantRepresentabilityStatement Φ c) :
    DrinfeldFixedEquivariantRepresentabilityStatement K D hInv hπ := by
  have hi : HasDrinfeldInvariant K D := by
    simpa only [HasDrinfeldInvariant, reciprocalClass, rationalClass, QuotientAddGroup.mk'_apply, one_div] using hInv
  exact h hi (drinfeldFixedCyclicRelations K D hInv hπ)

end Langlands.FormalGroup.LocalDivision
