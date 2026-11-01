import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Renard A.V.2: adjoints preserve limits and colimits

Statement-only formulation using the actual image of a supplied cone or
cocone under an adjoint functor, with all six universes independent.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard.AdjunctionPreservation

universe vA uA vB uB vI uI

/-- A right adjoint sends each limiting cone to its actual limiting image. -/
def RightAdjointPreservesLimitsStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A) (F : A ⥤ B) (_adj : G ⊣ F)
    (I : Type uI) [Category.{vI} I] (D : I ⥤ A) (t : Cone D),
    Nonempty (IsLimit t) → Nonempty (IsLimit (F.mapCone t))

/-- A left adjoint sends each colimiting cocone to its actual colimiting image. -/
def LeftAdjointPreservesColimitsStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A) (F : A ⥤ B) (_adj : G ⊣ F)
    (I : Type uI) [Category.{vI} I] (D : I ⥤ B) (t : Cocone D),
    Nonempty (IsColimit t) → Nonempty (IsColimit (G.mapCocone t))

/-- Right-adjoint limit preservation followed by left-adjoint colimit preservation. -/
def AdjunctionPreservationStatements : Prop :=
  RightAdjointPreservesLimitsStatement.{vA, uA, vB, uB, vI, uI} ∧
    LeftAdjointPreservesColimitsStatement.{vA, uA, vB, uB, vI, uI}

end Langlands.Renard.AdjunctionPreservation
