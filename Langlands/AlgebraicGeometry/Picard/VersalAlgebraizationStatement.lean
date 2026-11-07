import Langlands.AlgebraicGeometry.Picard.ArtinianChartVersality
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.FiniteType

/-! # Algebraization of formally versal Picard families: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation in
/-- Let `R` be a commutative ring of finite type over `ℤ`, `X` a proper flat
scheme over `Spec R` and `K` a field of finite type over `R`. Let `A` be a
complete noetherian local `R`-algebra with a surjective `R`-algebra map
`ε : A → K`, and let `L` be a line bundle on `X_A` that is formally versal at
the closed point `p = Spec ε` of `Spec A`. Then there are a scheme `U` locally
of finite type over `Spec R`, a line bundle `L'` on `X_U` and a point `u₀` of
`U` whose residue field is identified with `K` over `R`, such that `L'` is
formally versal at the resulting `K`-point `p'` of `U` and has the same
restriction to `X_K` as `L`. -/
def VersalAlgebraizationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (X : Over (Spec (CommRingCat.of R))),
    IsProper X.hom → Flat X.hom →
      ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.FiniteType R K]
        (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Algebra R A]
        (ε : A →ₐ[R] K),
        Function.Surjective ε →
          ∀ (L : LineBundle ((relativeSpace X.hom).obj
              (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))))))
            (p : ArtinianTest.residueBase R K ⟶
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))),
            p.left = Spec.map (CommRingCat.ofHom ε.toRingHom) →
            PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt X.hom L p →
              ∃ (U : Over (Spec (CommRingCat.of R)))
                (L' : LineBundle ((relativeSpace X.hom).obj U))
                (u₀ : U.left) (e : U.left.residueField u₀ ≅ CommRingCat.of K)
                (p' : ArtinianTest.residueBase R K ⟶ U),
                p'.left = Spec.map e.hom ≫ U.left.fromSpecResidueField u₀ ∧
                  LocallyOfFiniteType U.hom ∧
                  PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt X.hom L' p' ∧
                  Nonempty (PicardGroupoid.ArtinianChartVersality.residueBundle X.hom L' p' ≅
                    PicardGroupoid.ArtinianChartVersality.residueBundle X.hom L p)

end Langlands.AlgebraicGeometry.Picard
