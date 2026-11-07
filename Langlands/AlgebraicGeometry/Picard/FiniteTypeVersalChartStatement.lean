import Langlands.AlgebraicGeometry.Picard.ArtinianChartVersality
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.FiniteType

/-! # Versal Picard charts at finite-type field points: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation in
/-- Let `R` be a commutative ring of finite type over `ℤ` and `X` a proper flat
scheme over `Spec R`. For every field `K` of finite type over `R` and every
line bundle `L₀` on `X_K`, there are a scheme `U` locally of finite type over
`Spec R`, a line bundle `L` on `X_U` and a point `u₀` of `U` whose residue
field is identified with `K` over `R`, such that `L` is formally versal at the
resulting `K`-point `p` of `U` and restricts there to `L₀`. -/
def FiniteTypeVersalChartStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (X : Over (Spec (CommRingCat.of R))),
    IsProper X.hom → Flat X.hom →
      ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.FiniteType R K]
        (L₀ : LineBundle
          ((relativeSpace X.hom).obj (ArtinianTest.residueBase R K))),
        ∃ (U : Over (Spec (CommRingCat.of R)))
          (L : LineBundle ((relativeSpace X.hom).obj U))
          (u₀ : U.left) (e : U.left.residueField u₀ ≅ CommRingCat.of K)
          (p : ArtinianTest.residueBase R K ⟶ U),
          p.left = Spec.map e.hom ≫ U.left.fromSpecResidueField u₀ ∧
            LocallyOfFiniteType U.hom ∧
            PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt X.hom L p ∧
            Nonempty (PicardGroupoid.ArtinianChartVersality.residueBundle X.hom L p ≅ L₀)

end Langlands.AlgebraicGeometry.Picard
