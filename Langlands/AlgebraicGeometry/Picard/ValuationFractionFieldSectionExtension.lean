import Langlands.AlgebraicGeometry.Picard.FractionFieldSectionRestriction
import Langlands.AlgebraicGeometry.Picard.UnramifiedGenericSectionExtensionAssembly

/-! # Actual section extension over valuation domains -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

variable (R : CommRingCat.{u}) [IsDomain R] [ValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {X : Scheme.{u}} (p : X ⟶ Spec R)
  [IsSeparated p] [LocallyOfFiniteType p] [FormallyUnramified p]

/-- The published generic-section theorem gives bijective restriction along
the specified fraction-field map over an arbitrary valuation domain. -/
theorem fractionFieldSectionRestriction_bijective_of_valuation
    (hp : ClosedIrreducibleImages p) :
    Function.Bijective (fractionFieldSectionRestriction R K p) := by
  refine ⟨fractionFieldSectionRestriction_injective R K p, ?_⟩
  apply (fractionFieldSectionRestriction_surjective_iff R K p).mpr
  exact unramifiedGenericSectionExtension (Spec R) X
    (valuation_spec_geometricallyUnibranch R) p hp

/-- Actual sections are equivalent to actual maps from the chosen fraction
field, with the original equation over the valuation spectrum retained. -/
def valuationFractionFieldSectionEquiv (hp : ClosedIrreducibleImages p) :
    {s : Spec R ⟶ X // s ≫ p = 𝟙 (Spec R)} ≃
      {sK : Spec (CommRingCat.of K) ⟶ X //
        sK ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R K))} :=
  Equiv.ofBijective (fractionFieldSectionRestriction R K p)
    (fractionFieldSectionRestriction_bijective_of_valuation R K p hp)

@[simp]
theorem valuationFractionFieldSectionEquiv_apply
    (hp : ClosedIrreducibleImages p)
    (s : {s : Spec R ⟶ X // s ≫ p = 𝟙 (Spec R)}) :
    valuationFractionFieldSectionEquiv R K p hp s =
      fractionFieldSectionRestriction R K p s := rfl

/-- Each prescribed fraction-field map has a unique actual extension section,
with its restriction along the unchanged algebra map equal to that map. -/
theorem existsUnique_fractionFieldSectionExtension
    (hp : ClosedIrreducibleImages p)
    (sK : Spec (CommRingCat.of K) ⟶ X)
    (hK : sK ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃! s : Spec R ⟶ X,
      s ≫ p = 𝟙 (Spec R) ∧
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = sK := by
  obtain ⟨s, hs⟩ :=
    (fractionFieldSectionRestriction_bijective_of_valuation R K p hp).surjective
      ⟨sK, hK⟩
  refine ⟨s.val, ⟨s.property, congrArg Subtype.val hs⟩, ?_⟩
  intro t ht
  have heq : (⟨t, ht.1⟩ :
      {s : Spec R ⟶ X // s ≫ p = 𝟙 (Spec R)}) = s := by
    apply fractionFieldSectionRestriction_injective R K p
    apply Subtype.ext
    exact ht.2.trans (congrArg Subtype.val hs).symm
  exact congrArg Subtype.val heq

end Langlands.AlgebraicGeometry
