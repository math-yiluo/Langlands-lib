import Langlands.Automorphic.CuspidalAdmissible.ExpNeighbourhood

/-!
# Conjugating exponentials in the adelic group

Identities used to move a small archimedean exponential `ofInfinite (exp Y)` past an element
`u = ofInfinite (exp Z) · ofFinite l` of an exponential box: conjugation by `u` replaces `Y` by
`Ad(exp(-Z)) Y`, and conjugation of a finite element of a subgroup containing `l` stays in the
subgroup.
-/

noncomputable section

universe u

open NumberField Filter
open scoped Classical Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

open ArchimedeanGL

theorem infiniteOneParameter_eq_expInf (X : RealLieAlgebra K n) (t : ℝ) :
    infiniteOneParameter K n X t = expInf K n (t • realLieAlgebraToMatrix K n X) := by
  apply (archimedeanGLCoordinates K n).injective
  apply Units.ext
  rw [archimedeanGLCoordinates_expInf_val, infiniteOneParameter,
    ContinuousMulEquiv.apply_symm_apply, oneParameter_val]

theorem expInf_zero : expInf K n 0 = 1 := by
  apply (archimedeanGLCoordinates K n).injective
  apply Units.ext
  rw [archimedeanGLCoordinates_expInf_val, NormedSpace.exp_zero, map_one, Units.val_one]

/-- Conjugation of an archimedean element by an adelic element only sees its infinite part. -/
theorem conj_ofInfinite (u : AdelicGL K n) (a : InfiniteAdelicGL K n) :
    u⁻¹ * AdelicGL.ofInfinite K n a * u =
      AdelicGL.ofInfinite K n ((AdelicGL.infinite K n u)⁻¹ * a * AdelicGL.infinite K n u) := by
  refine AdelicGL.ext_infinite_finite K n ?_ ?_ <;> simp

/-- Conjugation of a finite element by an adelic element only sees its finite part. -/
theorem conj_ofFinite (u : AdelicGL K n) (l : FiniteAdelicGL K n) :
    u⁻¹ * AdelicGL.ofFinite K n l * u =
      AdelicGL.ofFinite K n ((AdelicGL.finite K n u)⁻¹ * l * AdelicGL.finite K n u) := by
  refine AdelicGL.ext_infinite_finite K n ?_ ?_ <;> simp

/-- Conjugating `exp Zm` by `c` gives `exp (c⁻¹ Zm c)` in coordinates. -/
theorem conj_expInf (c : InfiniteAdelicGL K n) (Zm : ArchimedeanMatrix K n) :
    c⁻¹ * expInf K n Zm * c =
      expInf K n ((((archimedeanGLCoordinates K n c)⁻¹ : ArchimedeanGL K n) :
        ArchimedeanMatrix K n) * Zm * (archimedeanGLCoordinates K n c : ArchimedeanMatrix K n)) := by
  apply (archimedeanGLCoordinates K n).injective
  apply Units.ext
  rw [archimedeanGLCoordinates_expInf_val, map_mul, map_mul, Units.val_mul, Units.val_mul,
    archimedeanGLCoordinates_expInf_val, map_inv, NormedSpace.exp_units_conj']

/-- Elements of an exponential box have finite part in the box's subgroup. -/
theorem finite_mem_of_mem_expBox {δ : ℝ} {L : Subgroup (FiniteAdelicGL K n)} {u : AdelicGL K n}
    (hu : u ∈ expBox K n δ (L : Set (FiniteAdelicGL K n))) :
    AdelicGL.finite K n u ∈ L ∧ ∃ Zm : ArchimedeanMatrix K n, ‖Zm‖ ≤ δ ∧
      AdelicGL.infinite K n u = expInf K n Zm := by
  obtain ⟨⟨Zm, l⟩, ⟨hZm, hl⟩, rfl⟩ := hu
  refine ⟨by simpa using hl, Zm, by simpa using hZm, by simp⟩

end Langlands.Global
