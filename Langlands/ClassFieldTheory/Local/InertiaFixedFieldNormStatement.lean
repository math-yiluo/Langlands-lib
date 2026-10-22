import Langlands.ClassFieldTheory.Local.Norms
import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.LocalField.Canonical
import Mathlib.FieldTheory.Galois.Basic

/-! # Finite norm surjectivity over the actual inertia fixed field -/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Every finite Galois extension of a finite extension of the actual canonical
inertia fixed field has surjective determinant norm on multiplicative groups. -/
def InertiaFixedFieldNormSurjectivity : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
    let U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
    ∀ (E L : Type u) [Field E] [Field L] [Algebra U E] [FiniteDimensional U E]
      [Algebra E L] [FiniteDimensional E L] [IsGalois E L],
      Function.Surjective (Langlands.LocalClassField.normUnits E L)

end Langlands.ClassFieldTheory.Local
