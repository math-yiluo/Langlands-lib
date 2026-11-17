import Langlands.GroupScheme.Reductive.LocalSplitWeylChains

/-! # Universality of Weyl conjugation from partner uniqueness and inverse rescaling -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open LocalSplitCell

/-- **Statement: uniqueness of Weyl-normalized partners over a local ring.** For a reductive
group over a local ring with affine structure morphism, a closed coordinate split torus that
is maximal on every residue-field fibre and a fibrewise root datum `P`, a parametrization of a
root `a` has at most one parametrization of `-a` as partner whose Weyl point acts by `s_a`
(`PartnerUnique`). -/
def LocalSplitPartnerUniqueStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] [DecidableEq I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
        PartnerUnique P G i

/-- **Statement: inverse rescaling of Weyl-normalized pairs over a local ring.** In the setting
of `LocalSplitPartnerUniqueStatement`, rescaling a pair whose Weyl point acts by `s_a` by a unit
`κ` and by `κ⁻¹` gives again a Weyl point acting by `s_a` (`PartnerRescales`). -/
def LocalSplitPartnerRescalesStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] [DecidableEq I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
        PartnerRescales P G i

/-- **Weyl conjugation from partner uniqueness and inverse rescaling.** -/
theorem localSplitWeylConjugation_of_partner (hPU : LocalSplitPartnerUniqueStatement.{u})
    (hSC : LocalSplitPartnerRescalesStatement.{u}) : LocalSplitWeylConjugationStatement.{u} := by
  intro R _ _ I _ _ J G H _ _ hG hH i i' hi hi' hmax hmax' P hP hP' b W hW u u' hu hw hu' hw'
    hR1 hR2
  have hdG : IsNormalSimpleData i P b W u := ⟨hG, hmax, hP, hu, hw, hW, hR1⟩
  have hdH : IsNormalSimpleData i' P b W u' := ⟨hH, hmax', hP', hu', hw', hW, hR2⟩
  exact weylConjugationRelations_of_partner hdG hdH (hPU R G hG I i hi hmax J P hP)
    (hPU R H hH I i' hi' hmax' J P hP') (hSC R G hG I i hi hmax J P hP)
    (hSC R H hH I i' hi' hmax' J P hP')

/-- **Statement: Weyl conjugation reduces to partner uniqueness and inverse rescaling.**
`LocalSplitPartnerUniqueStatement` and `LocalSplitPartnerRescalesStatement` imply
`LocalSplitWeylConjugationStatement`. -/
def LocalSplitWeylConjugationReductionStatement : Prop :=
  LocalSplitPartnerUniqueStatement.{u} → LocalSplitPartnerRescalesStatement.{u} →
    LocalSplitWeylConjugationStatement.{u}

theorem localSplitWeylConjugationReduction : LocalSplitWeylConjugationReductionStatement.{u} :=
  localSplitWeylConjugation_of_partner

end Langlands.GroupScheme
