import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Length
import Mathlib.Algebra.Module.Torsion.Basic

/-! # Néron's defect of smoothness of a point with values in a ring -/

namespace Langlands.AlgebraicGeometry.DvrSmoothening

open scoped TensorProduct

/-- Néron's measure of the defect of smoothness of a point `φ : A →ₐ[R] R'`: the length, as an
`R'`-module, of the torsion submodule of `R' ⊗_A Ω_{A/R}`, where `R'` is an `A`-algebra through
`φ`. -/
noncomputable def pointDefect {R A R' : Type*} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (φ : A →ₐ[R] R') : ℕ∞ :=
  letI : Algebra A R' := φ.toRingHom.toAlgebra
  Module.length R' (Submodule.torsion R' (R' ⊗[A] Ω[A⁄R]))

end Langlands.AlgebraicGeometry.DvrSmoothening
