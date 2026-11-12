import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryStatement
import Mathlib.RingTheory.FiniteType

/-! # Geometry of the chosen dual parameter scheme over a finite-type `ℤ`-algebra -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- For every commutative ring `R` of finite type over `ℤ`, every abelian scheme `A` over
`Spec R` and every proof of existence of an actual universal Picard-zero family, the chosen
parameter scheme is smooth, proper and geometrically connected over `Spec R`. -/
def FiniteTypeDualSchemeGeometryStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (A : AbelianScheme (Spec (CommRingCat.of R))) (hA : HasDualScheme A),
    DualSchemeGeometry A hA

end Langlands.AbelianScheme
