import Langlands.Representation.CompactCoefficient.TotalCompactness
import Langlands.Representation.Category.RestrictionSubquotients

/-!
# Compact smooth-dual coefficients on actual subquotients

These internal permanence laws use smooth-dual extension across injections
and pullback along surjections. They impose no chain condition.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]

section Maps

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- Pullback of a smooth functional proves compactness on a surjective image. -/
theorem HasCompactSmoothDualCoefficients.of_surjective
    (hρ : HasCompactSmoothDualCoefficients ρ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    HasCompactSmoothDualCoefficients σ := by
  intro w ℓ hℓ
  obtain ⟨v, rfl⟩ := hf w
  rw [matrixCoefficient_intertwining f]
  exact hρ v (dualIntertwining f ℓ)
    (isSmoothVector_map (dualIntertwining f) hℓ)

variable [IsTopologicalGroup G]

/-- A smooth functional extends across a smooth injection when compact open
subgroups are cofinal, so compact coefficients pass to the source. -/
theorem HasCompactSmoothDualCoefficients.of_injective
    (hσ : HasCompactSmoothDualCoefficients σ)
    (hcof : ∀ K : OpenSubgroup G,
      ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρs : IsSmooth ρ) (hσs : IsSmooth σ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    HasCompactSmoothDualCoefficients ρ := by
  intro v ℓ hℓ
  obtain ⟨m, hm⟩ :=
    contragredientMap_surjective_of_injective_of_compact_cofinal
      hcof hρs hσs f hf ⟨ℓ, hℓ⟩
  have hdual : dualIntertwining f m.val = ℓ := congrArg Subtype.val hm
  have hc := hσ (f v) m.val m.property
  rw [matrixCoefficient_intertwining f, hdual] at hc
  exact hc

end Maps

namespace SmoothRep

/-- Compactness of every smooth-dual coefficient on the actual restriction. -/
def compactRestrictionProperty (N : Subgroup G) :
    ObjectProperty (SmoothRep.{0, uG, uV} ℂ G) :=
  fun A => HasCompactSmoothDualCoefficients (restrictSubgroup N A).representation

/-- Restriction and an actual ambient isomorphism preserve the coefficient
property, without a compact-open cofinality assumption. -/
theorem compactRestrictionProperty_iff_of_iso (N : Subgroup G)
    {A B : SmoothRep.{0, uG, uV} ℂ G} (e : A ≅ B) :
    compactRestrictionProperty N A ↔ compactRestrictionProperty N B :=
  hasCompactSmoothDualCoefficients_iff_of_equiv
    (equivOfIso ((restrictSubgroupFunctor N).mapIso e))

variable [IsTopologicalGroup G]

/-- Compact smooth-dual coefficients pass to any actual smooth subquotient. -/
theorem hasCompactSmoothDualCoefficients_of_isSubquotient
    (hcof : ∀ K : OpenSubgroup G,
      ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    {A D : SmoothRep.{0, uG, uV} ℂ G}
    (hA : HasCompactSmoothDualCoefficients A.representation)
    (hDA : IsSubquotient D A) :
    HasCompactSmoothDualCoefficients D.representation := by
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp hDA
  exact (hA.of_injective hcof C.isSmooth A.isSmooth (hom i) hi).of_surjective (hom q) hq

/-- The actual restricted coefficient property is closed under all actual
subquotients when compact opens of the subgroup are cofinal. -/
theorem compactRestrictionProperty_of_isSubquotient (N : Subgroup G)
    (hcof : ∀ K : OpenSubgroup N,
      ∃ L : OpenSubgroup N, IsCompact (L : Set N) ∧ L ≤ K)
    {A D : SmoothRep.{0, uG, uV} ℂ G}
    (hA : compactRestrictionProperty N A) (hDA : IsSubquotient D A) :
    compactRestrictionProperty N D :=
  hasCompactSmoothDualCoefficients_of_isSubquotient hcof hA (hDA.restrictSubgroup N)

/-- Testing the restriction itself is equivalent to testing every actual
subquotient; the backward direction includes the object as its own subquotient. -/
theorem compactRestrictionProperty_iff_all_subquotients (N : Subgroup G)
    (hcof : ∀ K : OpenSubgroup N,
      ∃ L : OpenSubgroup N, IsCompact (L : Set N) ∧ L ≤ K)
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    compactRestrictionProperty N A ↔
      ∀ D : SmoothRep.{0, uG, uV} ℂ G,
        IsSubquotient D A → compactRestrictionProperty N D := by
  refine ⟨fun hA D hDA => compactRestrictionProperty_of_isSubquotient N hcof hA hDA, ?_⟩
  intro h
  exact h A (isSubquotient_iff_exists.mpr
    ⟨A, 𝟙 A, 𝟙 A, Function.injective_id, Function.surjective_id⟩)

end SmoothRep
end Langlands
