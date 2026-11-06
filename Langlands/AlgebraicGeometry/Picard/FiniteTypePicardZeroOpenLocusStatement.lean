import Langlands.AlgebraicGeometry.Picard.OpenLocus
import Mathlib.RingTheory.FiniteType

/-! # Geometric Picard-zero openness for actual families over finite-type integer algebras -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- For every commutative ring `R` of finite type over `ℤ`, every abelian scheme over `Spec R`,
every scheme `P` over `Spec R` and every actual rigidified family on `P`, some open subset of
`P` is characterized on every test scheme by geometric Picard-zero classes of the actual
pulled-back family. -/
def FiniteTypePicardZeroOpenLocusStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (A : AbelianScheme (Spec (CommRingCat.of R)))
    (P : Over (Spec (CommRingCat.of R)))
    (L : RigidifiedFamily A P),
    ∃ U : P.left.Opens, IsPicardZeroOpenLocus A L U

end Langlands.AbelianScheme
