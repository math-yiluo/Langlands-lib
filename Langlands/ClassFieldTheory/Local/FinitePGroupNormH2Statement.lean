import Langlands.ClassFieldTheory.Local.Cohomology
import Langlands.ClassFieldTheory.Local.Norms
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.PGroup

/-! # Relative H2 vanishing for finite p-group Galois extensions from all norms -/

namespace Langlands.ClassFieldTheory.Local

/-- For a finite Galois extension whose Galois group is a `p`-group, surjectivity
of the norm to every intermediate field implies vanishing of the actual relative
second cohomology. -/
def FinitePGroupNormH2Vanishing.{u} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    IsPGroup p Gal(L/K) →
    (∀ E : IntermediateField K L,
      letI : FiniteDimensional E L := FiniteDimensional.right K E L
      Function.Surjective (Langlands.LocalClassField.normUnits E L)) →
    Subsingleton (relativeCohomology K L 2)

end Langlands.ClassFieldTheory.Local
