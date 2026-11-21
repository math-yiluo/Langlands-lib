import Langlands.Automorphic.ArchimedeanFixedCompactDensity

/-! # Commuting finite and infinite restrictions of the adelic action -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global Langlands.Automorphic.CuspidalFixedSmoothDensity

universe u v

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (U : AdelicGL F n →* (E →L[ℂ] E))

/-- The two coordinate actions commute because their actual adelic
inclusions commute. -/
theorem hilbertCoordinateActions_commute (g : ArchimedeanGL F n) (d : FiniteAdelicGL F n) (w : E) :
    infiniteHilbertAction F n U g (finiteHilbertAction F n U d w) =
      finiteHilbertAction F n U d (infiniteHilbertAction F n U g w) := by
  let a := AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm g)
  let b := AdelicGL.ofFinite F n d
  change U a (U b w) = U b (U a w)
  simp only [← mul_apply_eq_comp, ← map_mul]
  exact congrArg (fun z : AdelicGL F n => U z w)
    (AdelicGL.ofFinite_commute_ofInfinite F n d
      ((archimedeanGLCoordinates F n).symm g)).eq.symm


end Langlands.Automorphic.OperatorDeterminantSlice
