import Langlands.AlgebraicGeometry.Picard.ArtinianChartVersality
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.FiniteType

/-! # Smooth Picard charts through finite-type field points: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

namespace PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S) {U : Over S}
  (L : LineBundle ((relativeSpace f).obj U))

/-- Every actual point fibre of the family is represented by a scheme on the
full slice that is smooth over the test scheme. No surjectivity is required. -/
def HasSmoothPointFibers : Prop :=
  ∀ (T : Over S) (M : LineBundle ((relativeSpace f).obj T)),
    ∃ P : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅
        pointFiberPresheaf f L M) ∧
      Smooth P.hom

/-- A smooth surjective presentation has smooth point fibres. -/
lemma IsSmoothSurjectivePresentation.hasSmoothPointFibers
    (h : IsSmoothSurjectivePresentation f L) : HasSmoothPointFibers f L := by
  intro T M
  obtain ⟨P, e, hP, -⟩ := h T M
  exact ⟨P, e, hP⟩

end PicardGroupoid

open Langlands.AlgebraicGeometry.Deformation in
/-- Let `R` be a commutative ring of finite type over `ℤ` and `X` a proper flat
scheme over `Spec R`. For every field `K` of finite type over `R` and every
line bundle `L₀` on `X_K`, there is a scheme `U` locally of finite type over
`Spec R` with a line bundle `L` on `X_U` whose actual point fibres are all
represented by smooth schemes, together with a `K`-point `p` of `U` over
`Spec R` at which `L` restricts to `L₀`. -/
def FiniteTypePointSmoothChartStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (X : Over (Spec (CommRingCat.of R))),
    IsProper X.hom → Flat X.hom →
      ∀ (K : Type u) [Field K] [Algebra R K] [Algebra.FiniteType R K]
        (L₀ : LineBundle
          ((relativeSpace X.hom).obj (ArtinianTest.residueBase R K))),
        ∃ (U : Over (Spec (CommRingCat.of R)))
          (L : LineBundle ((relativeSpace X.hom).obj U))
          (p : ArtinianTest.residueBase R K ⟶ U),
          LocallyOfFiniteType U.hom ∧ PicardGroupoid.HasSmoothPointFibers X.hom L ∧
            Nonempty (PicardGroupoid.ArtinianChartVersality.residueBundle X.hom L p ≅ L₀)

end Langlands.AlgebraicGeometry.Picard
