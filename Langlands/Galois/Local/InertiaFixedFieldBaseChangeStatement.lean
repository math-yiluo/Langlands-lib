import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.ClassFieldTheory.Local.ReciprocitySystem

/-! # Inertia fixed fields under finite local base change -/

namespace Langlands.PadicField

universe u

/-- The canonical inertia fixed field after finite base change is the
compositum with the transported canonical inertia fixed field of the base. -/
def InertiaFixedFieldBaseChange : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (D : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier),
    let U_F := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
    let U_D := IntermediateField.fixedField
      ((D.asPadicField (p := p)).absoluteInertia
        (D.asPadicField (p := p)).canonicalTopologicalData)
    letI : Algebra F.Carrier (AlgebraicClosure D.field) :=
      ((algebraMap D.field (AlgebraicClosure D.field)).comp
        (algebraMap F.Carrier D.field)).toAlgebra
    letI : SMul F.Carrier (AlgebraicClosure D.field) :=
      (inferInstance : Algebra F.Carrier (AlgebraicClosure D.field)).toSMul
    letI : SMul D.field (AlgebraicClosure D.field) :=
      (inferInstance : Algebra D.field (AlgebraicClosure D.field)).toSMul
    letI : IsScalarTower F.Carrier D.field (AlgebraicClosure D.field) :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ (j : AlgebraicClosure F.Carrier →ₐ[F.Carrier] AlgebraicClosure D.field),
      (∀ a : D.field,
        j (a : AlgebraicClosure F.Carrier) = algebraMap D.field (AlgebraicClosure D.field) a) →
      U_D = IntermediateField.adjoin D.field
        (j '' (U_F : Set (AlgebraicClosure F.Carrier)))

end Langlands.PadicField
