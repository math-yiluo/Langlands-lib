import Langlands.AlgebraicGeometry.Picard.ArtinianChartVersality
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Openness of versality for actual Picard families: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation

/-- Openness of versality for the actual Picard stack of a proper flat scheme
over a noetherian ring. Let `U` be locally of finite type over `Spec R` with an
actual line bundle `L` on `U ×_R X`. Suppose `L` is formally versal at the
canonical point of a finite-type point `u₀` of `U`, with residue field
identified with `K`. Then some open neighbourhood `V` of `u₀` has the following
property: `L` is formally versal at every locally finite-type field point of
`U` whose image lies in `V`. -/
def PicardOpennessOfVersalityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → Flat X.hom →
    ∀ (U : Over (Spec (CommRingCat.of R))), LocallyOfFiniteType U.hom →
    ∀ (L : LineBundle ((relativeSpace X.hom).obj U))
      (u₀ : U.left) (K : Type u) [Field K] [Algebra R K]
      (p : ArtinianTest.residueBase R K ⟶ U)
      (e : U.left.residueField u₀ ≅ CommRingCat.of K),
      p.left = Spec.map e.hom ≫ U.left.fromSpecResidueField u₀ →
      LocallyOfFiniteType p.left →
      PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt X.hom L p →
      ∃ V : U.left.Opens, u₀ ∈ V ∧
        ∀ (K' : Type u) [Field K'] [Algebra R K']
          (p' : ArtinianTest.residueBase R K' ⟶ U),
          LocallyOfFiniteType p'.left → Set.range p'.left ⊆ V →
          PicardGroupoid.ArtinianChartVersality.IsFormallyVersalAt X.hom L p'

end Langlands.AlgebraicGeometry.Picard
