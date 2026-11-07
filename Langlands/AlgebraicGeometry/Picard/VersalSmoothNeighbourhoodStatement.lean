import Langlands.AlgebraicGeometry.Picard.FiniteTypePointSmoothChartStatement
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Smooth open neighbourhoods of versal Picard points: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation in
/-- Let `R` be a commutative ring of finite type over `ℤ`, `X` a proper flat
scheme over `Spec R`, `U` a scheme locally of finite type over `Spec R` and `L`
a line bundle on `X_U`. Let `u₀` be a point of `U` whose residue field is
identified with a field `K` over `R`, with `K`-point `p` of finite type. If `L`
is formally versal at `p`, then some open subscheme of `U` containing `u₀`
carries the restriction of `L` with smooth actual point fibres. -/
def VersalSmoothNeighbourhoodStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (X : Over (Spec (CommRingCat.of R))),
    IsProper X.hom → Flat X.hom →
      ∀ (U : Over (Spec (CommRingCat.of R))), LocallyOfFiniteType U.hom →
        ∀ (L : LineBundle ((relativeSpace X.hom).obj U)) (u₀ : U.left)
          (K : Type u) [Field K] [Algebra R K]
          (e : U.left.residueField u₀ ≅ CommRingCat.of K)
          (p : ArtinianTest.residueBase R K ⟶ U),
          p.left = Spec.map e.hom ≫ U.left.fromSpecResidueField u₀ →
          LocallyOfFiniteType p.left →
          PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt X.hom L p →
          ∃ (V : Over (Spec (CommRingCat.of R))) (j : V ⟶ U),
            IsOpenImmersion j.left ∧ u₀ ∈ Set.range j.left.base ∧
              PicardGroupoid.HasSmoothPointFibers X.hom
                ((LineBundle.pullback ((relativeSpace X.hom).map j)).obj L)

end Langlands.AlgebraicGeometry.Picard
