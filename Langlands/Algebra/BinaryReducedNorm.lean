import Langlands.Algebra.BinarySplittingNorm
import Langlands.Algebra.ReducedNormFiniteChart
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.DivisionRing

/-! Binary elementary generation for the actual canonical reduced norm. -/

noncomputable section

namespace Langlands.BinaryElementary.Reduced

universe u uL uI uJ uB

open scoped TensorProduct
open Langlands.CentralSimple

variable (K D : Type u) [Field K] [Ring D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] [IsSimpleRing D]

/-- The canonical reduced norm restricted to the original coefficient units. -/
def coefficientNorm : Dˣ →* Kˣ :=
  (reducedNormUnits K D K).comp
    (Units.map Algebra.TensorProduct.includeRight.toMonoidHom)

/-- The canonical reduced norm restricted to the original binary matrix units. -/
def binaryNorm : GL₂ D →* Kˣ :=
  (reducedNormUnits K (Matrix (Fin 2) (Fin 2) D) K).comp
    (Units.map Algebra.TensorProduct.includeRight.toMonoidHom)

/-- The coefficient kernel is the actual pullback of the canonical norm-one subgroup. -/
theorem ker_coefficientNorm :
    (coefficientNorm K D).ker = (reducedNormOne K D K).comap
      (Units.map Algebra.TensorProduct.includeRight.toMonoidHom) := rfl

/-- The binary kernel is the actual pullback of the canonical norm-one subgroup. -/
theorem ker_binaryNorm :
    (binaryNorm K D).ker =
      (reducedNormOne K (Matrix (Fin 2) (Fin 2) D) K).comap
        (Units.map Algebra.TensorProduct.includeRight.toMonoidHom) := rfl

@[simp] theorem mem_ker_coefficientNorm (a : Dˣ) :
    a ∈ (coefficientNorm K D).ker ↔
      reducedNorm K D K (1 ⊗ₜ[K] (a : D)) = 1 := by
  change coefficientNorm K D a = 1 ↔ _
  exact Units.ext_iff

@[simp] theorem mem_ker_binaryNorm (g : GL₂ D) :
    g ∈ (binaryNorm K D).ker ↔
      reducedNorm K (Matrix (Fin 2) (Fin 2) D) K (1 ⊗ₜ[K] g.val) = 1 := by
  change binaryNorm K D g = 1 ↔ _
  exact Units.ext_iff

section Chart

variable {L : Type uL} [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  {I : Type uI} [Fintype I] [DecidableEq I] [Nonempty I]
  {J : Type uJ} [Fintype J] {B : Type uB} [Fintype B]

/-- Every actual charted coefficient character equals the canonical one. -/
theorem charted_coefficientNorm_eq (b : Module.Basis J K D)
    (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) :
    Splitting.coefficientNorm b e = coefficientNorm K D := by
  unfold Splitting.coefficientNorm coefficientNorm
  rw [normFromGaloisUnits_eq_reducedNormUnits K D b e K]

/-- The actual binary block chart gives the canonical binary reduced norm. -/
theorem charted_binaryNorm_eq (b : Module.Basis B K (Matrix (Fin 2) (Fin 2) D))
    (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) :
    Splitting.binaryNorm b e = binaryNorm K D := by
  unfold Splitting.binaryNorm binaryNorm
  rw [normFromGaloisUnits_eq_reducedNormUnits K (Matrix (Fin 2) (Fin 2) D)
    b (Splitting.chart e) K]

end Chart

/-- Every elementary matrix has canonical reduced norm one. -/
theorem elementary_le_ker : elementary D ≤ (binaryNorm K D).ker := by
  rw [← charted_binaryNorm_eq K D (Module.finBasis K (Matrix (Fin 2) (Fin 2) D))
    (finiteGaloisSplittingChart K D), Splitting.ker_binaryNorm]
  exact Representation.elementary_le_ker _

section DivisionRing

variable {D : Type u} [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- Binary canonical norm-one generation is exactly coefficient commutator-kernel vanishing. -/
theorem elementary_eq_ker_iff :
    elementary D = (binaryNorm K D).ker ↔
      (coefficientNorm K D).ker = commutator Dˣ := by
  rw [← charted_binaryNorm_eq K D (Module.finBasis K (Matrix (Fin 2) (Fin 2) D))
      (finiteGaloisSplittingChart K D),
    ← charted_coefficientNorm_eq K D (Module.finBasis K D)
      (finiteGaloisSplittingChart K D)]
  exact Splitting.elementary_eq_ker_iff _ _ _

end DivisionRing

end Langlands.BinaryElementary.Reduced
