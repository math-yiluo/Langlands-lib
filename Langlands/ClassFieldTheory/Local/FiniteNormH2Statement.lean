import Langlands.ClassFieldTheory.Local.Cohomology
import Langlands.ClassFieldTheory.Local.Norms
import Mathlib.FieldTheory.Galois.Basic

/-! # Relative H2 vanishing from all intermediate-field norms -/

namespace Langlands.ClassFieldTheory.Local

/-- For a finite Galois extension, surjectivity of the norm to every
intermediate field implies vanishing of the actual relative second cohomology. -/
def FiniteNormH2Vanishing.{u, v} : Prop :=
  ∀ (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    (∀ E : IntermediateField K L,
      letI : FiniteDimensional E L := FiniteDimensional.right K E L
      Function.Surjective (Langlands.LocalClassField.normUnits E L)) →
    Subsingleton (relativeCohomology K L 2)

end Langlands.ClassFieldTheory.Local
