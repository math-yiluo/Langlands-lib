import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyStatement
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic

/-! # Finite cohomology and the Euler-square reduction for the cubic bundle -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Finite cohomology is unconditional for the actual cubic bundle. Once higher
cohomology vanishes, its prescribed Euler square determines its dimension. -/
def CubicFibreEulerReductionStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (K : Type u) [Field K] (g d n : ℕ)
    (a : Datum P (Spec (CommRingCat.of K)) g d n),
    HasFiniteCohomology a.abelian.X.hom a.cubicBundle.obj ∧
      (∀ h : HasFiniteCohomology a.abelian.X.hom a.cubicBundle.obj,
        (∀ i : ℕ, 0 < i →
          IsZero ((relativeCohomology a.abelian.X.hom i).obj a.cubicBundle.obj)) →
        (eulerCharacteristic a.abelian.X.hom a.cubicBundle.obj h) ^ 2 =
          (6 : ℤ) ^ (2 * g) * (d : ℤ) ^ 2 →
        Module.finrank K ((relativeCohomology a.abelian.X.hom 0).obj
          a.cubicBundle.obj) = 6 ^ g * d)

end Langlands.AbelianScheme.PolarizedFiniteLevel
