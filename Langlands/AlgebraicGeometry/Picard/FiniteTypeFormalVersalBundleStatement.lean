import Langlands.AlgebraicGeometry.Picard.ArtinianChartVersality
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.FiniteType

/-! # Formally versal Picard families over complete local bases: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation in
/-- Let `R` be a commutative ring of finite type over `ℤ` and `X` a proper flat
scheme over `Spec R`. For every field `K` of finite type over `R` and every
line bundle `L₀` on `X_K`, there are a complete noetherian local `R`-algebra
`A` with a surjective `R`-algebra map `ε : A → K` and a line bundle `L` on
`X_A` that is formally versal at the closed point `Spec ε` of `Spec A` and
restricts there to `L₀`. -/
def FiniteTypeFormalVersalBundleStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (X : Over (Spec (CommRingCat.of R))),
    IsProper X.hom → Flat X.hom →
      ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.FiniteType R K]
        (L₀ : LineBundle
          ((relativeSpace X.hom).obj (ArtinianTest.residueBase R K))),
        ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A) (_ : IsLocalRing A)
          (_ : IsAdicComplete (IsLocalRing.maximalIdeal A) A) (_ : Algebra R A)
          (ε : A →ₐ[R] K)
          (L : LineBundle ((relativeSpace X.hom).obj
            (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))))))
          (p : ArtinianTest.residueBase R K ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))),
          Function.Surjective ε ∧
            p.left = Spec.map (CommRingCat.ofHom ε.toRingHom) ∧
            PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt X.hom L p ∧
            Nonempty (PicardGroupoid.ArtinianChartVersality.residueBundle X.hom L p ≅ L₀)

end Langlands.AlgebraicGeometry.Picard
