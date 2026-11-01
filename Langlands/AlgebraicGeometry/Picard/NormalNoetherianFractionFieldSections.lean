import Langlands.AlgebraicGeometry.Picard.DiscreteValuativeGenericSections
import Langlands.AlgebraicGeometry.Picard.FractionFieldSectionRestriction

/-! # Discrete valuative section extension over normal noetherian domains -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

/-- An integrally closed domain has a geometrically unibranch spectrum in
the Library's actual-stalk sense. -/
theorem normal_spec_geometricallyUnibranch
    (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R] :
    GeometricallyUnibranchIntegralScheme (Spec R) :=
  geometricallyUnibranchIntegralScheme_of_hasNormalStalks (Spec R)
    (spec_hasNormalStalks R)

variable (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {X : Scheme.{u}} (p : X ⟶ Spec R)
  [IsSeparated p] [LocallyOfFiniteType p] [FormallyUnramified p]

/-- The discrete valuative criterion gives bijective restriction along the
specified fraction-field map of a normal noetherian domain. -/
theorem fractionFieldSectionRestriction_bijective_of_normal_discreteValuativeExistence
    (hp : DiscreteValuativeCriterion.Existence p) :
    Function.Bijective (fractionFieldSectionRestriction R K p) := by
  refine ⟨fractionFieldSectionRestriction_injective R K p, ?_⟩
  apply (fractionFieldSectionRestriction_surjective_iff R K p).mpr
  exact (genericSectionRestriction_bijective_of_discreteValuativeExistence p
    (normal_spec_geometricallyUnibranch R) hp).surjective

/-- The equivalence retains actual sections and actual chosen-field maps,
with their original equations over the normal noetherian spectrum. -/
def normalNoetherianFractionFieldSectionEquiv
    (hp : DiscreteValuativeCriterion.Existence p) :
    {s : Spec R ⟶ X // s ≫ p = 𝟙 (Spec R)} ≃
      {sK : Spec (CommRingCat.of K) ⟶ X //
        sK ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R K))} :=
  Equiv.ofBijective (fractionFieldSectionRestriction R K p)
    (fractionFieldSectionRestriction_bijective_of_normal_discreteValuativeExistence
      R K p hp)

@[simp]
theorem normalNoetherianFractionFieldSectionEquiv_apply
    (hp : DiscreteValuativeCriterion.Existence p)
    (s : {s : Spec R ⟶ X // s ≫ p = 𝟙 (Spec R)}) :
    normalNoetherianFractionFieldSectionEquiv R K p hp s =
      fractionFieldSectionRestriction R K p s := rfl

/-- Each prescribed chosen-fraction-field map extends uniquely, and both
the section equation and its exact restriction equation hold. -/
theorem existsUnique_fractionFieldSectionExtension_of_normal_discreteValuativeExistence
    (hp : DiscreteValuativeCriterion.Existence p)
    (sK : Spec (CommRingCat.of K) ⟶ X)
    (hK : sK ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃! s : Spec R ⟶ X,
      s ≫ p = 𝟙 (Spec R) ∧
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = sK := by
  obtain ⟨s, hs⟩ :=
    (fractionFieldSectionRestriction_bijective_of_normal_discreteValuativeExistence
      R K p hp).surjective ⟨sK, hK⟩
  refine ⟨s.val, ⟨s.property, congrArg Subtype.val hs⟩, ?_⟩
  intro t ht
  have heq : (⟨t, ht.1⟩ : {s : Spec R ⟶ X // s ≫ p = 𝟙 (Spec R)}) = s := by
    apply fractionFieldSectionRestriction_injective R K p
    apply Subtype.ext
    exact ht.2.trans (congrArg Subtype.val hs).symm
  exact congrArg Subtype.val heq

end Langlands.AlgebraicGeometry
