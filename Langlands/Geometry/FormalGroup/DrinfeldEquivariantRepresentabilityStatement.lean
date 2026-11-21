import Langlands.Geometry.FormalGroup.DeligneCompletedBase
import Langlands.Geometry.FormalGroup.DrinfeldDeligneResidueComparisonStatement
import Langlands.Geometry.FormalGroup.DrinfeldUnramifiedResidue
import Langlands.ClassFieldTheory.Local.LocalDivisionCyclicInvariant

/-! # Drinfeld's equivariant representability theorem on affine Nilp points -/

noncomputable section

universe u

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision CentralSimple DeligneFormalSpace
open Langlands.ClassFieldTheory.Local Langlands.LocalGalois.Separable.UnramifiedCompletion

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type u} [Field L] [Algebra K L] {ι : L →ₐ[K] D}

/-- Drinfeld's positive reciprocal invariant with the arithmetic conjugation
law is the Library's invariant of the opposite division algebra. -/
def HasDrinfeldInvariant (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] [Algebra.IsCentral K D] : Prop :=
  localBrauerInvariant K (Brauer.classOf (Brauer.opposite (divisionAlgebraCSA K D))) =
    QuotientAddGroup.mk ((1 : ℚ) / (reducedDegree K D : ℚ))

/-- Drinfeld's basic theorem on the actual affine Nilp point functors, with
the comparison over the residue coordinate and the full product action. -/
def DrinfeldEquivariantRepresentabilityStatement {π : 𝒪[K]}
    (Φ : DrinfeldFramedAtlas.UnramifiedFrame (ι := ι) π)
    (c : Φ.val.MatrixCoordinates) : Prop :=
  letI : NeZero (reducedDegree K D) := ⟨(reducedDegree_pos K D).ne'⟩
  HasDrinfeldInvariant K D → HasDrinfeldCyclicRelations ι π →
    ∃ e : DrinfeldFramedAtlas.unramifiedFunctor Φ ≅
        nilpDeligneCompletedFunctor (d := reducedDegree K D) Φ.property.1,
      (∀ (B : Nilp.{u, u} 𝒪[K] π) (q : DrinfeldFramedAtlas.ComparisonClass Φ B),
        (Nilp.quotientO 𝒪[K] B).comp (e.hom.app B q).2 =
          q.residueMap.comp (IsScalarTower.toAlgHom 𝒪[K] (Integers K) (Residue K))) ∧
      ∀ g : GL (Fin (reducedDegree K D)) K × Dˣ,
        (DrinfeldFramedAtlas.unramifiedAction Φ c g).hom ≫ e.hom =
          e.hom ≫ (nilpDeligneCompletedDivisionAction (D := D) Φ.property.1 g).hom

end Langlands.FormalGroup.LocalDivision
