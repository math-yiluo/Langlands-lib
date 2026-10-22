import Langlands.ClassFieldTheory.Local.Cohomology
import Langlands.LocalField.Definitions

/-! # Local H¹ vanishing and H² invariant existence

This target asserts existence. It does not choose invariant maps, assume a
class formation, or identify finite and absolute cohomology by definition.
-/

namespace Langlands.ClassFieldTheory.Local

universe u v

/-- The first local cohomology existence family, for every finite extension of Q_p. -/
def CohomologyExistence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
    (Subsingleton (absoluteCohomology F.Carrier 1) ∧
      Nonempty (absoluteCohomology F.Carrier 2 ≃+ RationalModIntegers)) ∧
    ∀ (L : Type v) [Field L] [Algebra F.Carrier L]
      [FiniteDimensional F.Carrier L] [IsGalois F.Carrier L],
      Subsingleton (relativeCohomology F.Carrier L 1) ∧
        ∃ inv : relativeCohomology F.Carrier L 2 →+ RationalModIntegers,
          Function.Injective inv ∧
            inv.range = denominatorSubgroup (Module.finrank F.Carrier L)

end Langlands.ClassFieldTheory.Local
