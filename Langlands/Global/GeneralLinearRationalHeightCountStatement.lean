import Langlands.Global.AdelicRepresentationHeight

universe u

namespace Langlands.Global

open NumberField

/-- For positive rank, the rational invertible matrices whose diagonal adelic
image has full matrix-and-inverse height at most `B` are at most a constant
times a fixed power of `B` in number, for every `B ≥ 1`. -/
def GeneralLinearRationalHeightCountStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ), 0 < n →
    ∃ (C : ℝ) (M : ℕ), ∀ B : ℝ, 1 ≤ B →
      ({g : Matrix.GeneralLinearGroup (Fin n) F |
          AdelicMatrixHeight.height F n
            (Matrix.GeneralLinearGroup.map (algebraMap F (AdeleRing (𝓞 F) F)) g) ≤ B}.ncard : ℝ)
        ≤ C * B ^ M

end Langlands.Global
