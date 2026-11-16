import Langlands.GroupScheme.AffineVectorSeries
import Langlands.GroupScheme.RelativeLevi.SplitBorelConjugacyStatement

/-! # Statement: a split Borel with an affine vector-series kernel -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A Borel containing the specified coordinate torus, with a split projection
onto that torus and an affine kernel admitting a finite vector-quotient series. -/
def HasSplitBorelVectorSeries {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))} {I : Type u} [Fintype I]
    (t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) : Prop :=
  ∃ (B₀ K : GroupScheme (Spec (CommRingCat.of R))) (i₀ : B₀ ⟶ G)
    (j : K ⟶ B₀) (q : B₀ ⟶ splitTorus (Spec (CommRingCat.of R)) I)
    (t₀ : splitTorus (Spec (CommRingCat.of R)) I ⟶ B₀),
    IsRelativeBorelSubgroup i₀ ∧ IsClosedSubgroup j ∧ IsAffineHom K.X.hom ∧
      t₀ ≫ i₀ = t ∧ t₀ ≫ q = 𝟙 _ ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q ∧
      ∃ n : ℕ, HasAffineVectorSeries n K

/-- The split Borel structure used in Conrad's proof of Corollary 5.2.13(1),
with its vector filtration supplied by Proposition 5.1.16(2).
This is an unproved structural statement over every commutative ring. -/
def SplitBorelVectorSeriesStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (I : Type u) [Fintype I] (t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
    haveI := hG.isAffineHom
    IsClosedSubgroup t →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) t →
    IsFibrewiseRootDatumOf I G t P →
    (∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G t (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) →
    HasSplitBorelVectorSeries t

end Langlands.GroupScheme
