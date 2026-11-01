import Langlands.AlgebraicGeometry.Picard.DiscreteValuativeClosedIrreducibleImagesProof
import Langlands.AlgebraicGeometry.Picard.UnramifiedGenericSectionExtensionAssembly

/-! # Generic sections detected by discrete valuative existence -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

namespace DiscreteValuativeCriterion

/-- Base change preserves the actual discrete valuation ring and fraction field
of each test square. -/
instance existence_stableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun _ _ p => Existence p : MorphismProperty Scheme.{u}) := by
  constructor
  intro T X Y S b p a q hP hp sq hDVR
  let sq' : ValuativeCommSq p :=
    { R := sq.R
      K := sq.K
      i₁ := sq.i₁ ≫ a
      i₂ := sq.i₂ ≫ b
      commSq := ⟨by simp only [Category.assoc, hP.w, reassoc_of% sq.commSq.w]⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (hp sq' hDVR).exists_lift
  refine ⟨⟨⟨hP.lift l sq.i₂ (by simp_all only [sq']), ?_, hP.lift_snd _ _ _⟩⟩⟩
  apply hP.hom_ext
  · simpa
  · simp only [Category.assoc]
    rw [hP.lift_snd, sq.commSq.w]

/-- The discrete criterion supplies closed irreducible images after every
base change whose new base is locally noetherian. -/
theorem closedIrreducibleImages_pullback_snd
    {X S T : Scheme.{u}} (p : X ⟶ S)
    [LocallyOfFiniteType p] [IsSeparated p]
    (hp : Existence p) (b : T ⟶ S) [IsLocallyNoetherian T] :
    ClosedIrreducibleImages (pullback.snd p b) := by
  apply discreteValuativeClosedIrreducibleImages
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun _ _ q => Existence q) (IsPullback.of_hasPullback p b) hp

end DiscreteValuativeCriterion

variable {S X : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
  (p : X ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [FormallyUnramified p]

/-- On an integral geometrically unibranch locally noetherian base, discrete
valuative existence makes generic restriction bijective. -/
theorem genericSectionRestriction_bijective_of_discreteValuativeExistence
    (hS : GeometricallyUnibranchIntegralScheme S)
    (hp : DiscreteValuativeCriterion.Existence p) :
    Function.Bijective (genericSectionRestriction p) := by
  refine ⟨genericSectionRestriction_injective p, ?_⟩
  exact unramifiedGenericSectionExtension S X hS p
    (discreteValuativeClosedIrreducibleImages X S p hp)

/-- Actual sections are equivalent to actual generic residue-field maps
over the given locally noetherian base. -/
def discreteValuativeGenericSectionEquiv
    (hS : GeometricallyUnibranchIntegralScheme S)
    (hp : DiscreteValuativeCriterion.Existence p) :
    {s : S ⟶ X // s ≫ p = 𝟙 S} ≃
      {sη : Spec (S.residueField (genericPoint S)) ⟶ X //
        sη ≫ p = S.fromSpecResidueField (genericPoint S)} :=
  Equiv.ofBijective (genericSectionRestriction p)
    (genericSectionRestriction_bijective_of_discreteValuativeExistence p hS hp)

@[simp]
theorem discreteValuativeGenericSectionEquiv_apply
    (hS : GeometricallyUnibranchIntegralScheme S)
    (hp : DiscreteValuativeCriterion.Existence p)
    (s : {s : S ⟶ X // s ≫ p = 𝟙 S}) :
    discreteValuativeGenericSectionEquiv p hS hp s =
      genericSectionRestriction p s := rfl

/-- Every prescribed generic map has a unique actual section extension,
with both its base equation and its exact restriction retained. -/
theorem existsUnique_genericSectionExtension_of_discreteValuativeExistence
    (hS : GeometricallyUnibranchIntegralScheme S)
    (hp : DiscreteValuativeCriterion.Existence p)
    (sη : Spec (S.residueField (genericPoint S)) ⟶ X)
    (hη : sη ≫ p = S.fromSpecResidueField (genericPoint S)) :
    ∃! s : S ⟶ X,
      s ≫ p = 𝟙 S ∧ S.fromSpecResidueField (genericPoint S) ≫ s = sη := by
  obtain ⟨s, hs⟩ :=
    (genericSectionRestriction_bijective_of_discreteValuativeExistence p hS hp).surjective
      ⟨sη, hη⟩
  refine ⟨s.val, ⟨s.property, congrArg Subtype.val hs⟩, ?_⟩
  intro t ht
  have heq : (⟨t, ht.1⟩ : {s : S ⟶ X // s ≫ p = 𝟙 S}) = s := by
    apply genericSectionRestriction_injective p
    apply Subtype.ext
    exact ht.2.trans (congrArg Subtype.val hs).symm
  exact congrArg Subtype.val heq

end Langlands.AlgebraicGeometry
