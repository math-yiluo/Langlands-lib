import Langlands.Geometry.Building.AffineRootLengths
import Langlands.Geometry.Building.AffineIndivisibleRootOrbits

/-! # Transitive simple roots and lengths of all derivative roots -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- Every derivative root is the derivative of an indivisible affine root.
This condition retains all derivative roots, including multipliable ones. -/
def HasIndivisibleDerivativeLifts (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Prop :=
  ∀ a : derivativeRoots Ψ,
    ∃ ψ ∈ nonDivisibleRoots Ψ, ψ.linear = a.val

/-- Any two simple affine roots of the supplied set are related by
root-preserving affine pullback. -/
def HasTransitiveSimpleRoots (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) : Prop :=
  ∀ ψ ∈ simpleAffineRoots Ψ C, ∀ η ∈ simpleAffineRoots Ψ C,
    ∃ (e : A ≃ᵃ[ℝ] A), e ∈ rootStabilizer Ψ ∧
      η = ψ.comp (e : A →ᵃ[ℝ] A)

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)
include hΨ

/-- Simultaneous negation does not change the coroot form. -/
theorem corootForm_neg_neg (α β : Module.Dual ℝ V) :
    hΨ.corootForm (-α) (-β) = hΨ.corootForm α β := by
  simp only [corootForm, LinearMap.neg_apply, neg_mul_neg]

/-- The derivative of an indivisible affine root has the squared length of
some simple root in any prescribed regular chamber. -/
theorem exists_simple_corootForm_self_eq {c : A}
    (hc : GalleryGeometry.IsRegular Ψ c)
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ nonDivisibleRoots Ψ) :
    ∃ η ∈ simpleAffineRoots Ψ (facet Ψ c),
      hΨ.corootForm ψ.linear ψ.linear = hΨ.corootForm η.linear η.linear := by
  obtain ⟨e, he, η, hη, hroot⟩ := hΨ.exists_simple_eq_comp_or_neg hc hψ
  refine ⟨η, hη, ?_⟩
  have hinv := hΨ.corootForm_linear_comp he ψ ψ
  rcases hroot with hroot | hroot <;>
    simpa only [hroot, AffineMap.neg_linear, hΨ.corootForm_neg_neg] using hinv.symm

/-- Transitivity on chamber-simple roots gives equal lengths on the full
derivative set if every derivative has an indivisible affine lift. -/
theorem hasEqualDerivativeLengths_of_transitive_simpleRoots {c : A}
    (hc : GalleryGeometry.IsRegular Ψ c)
    (hlift : HasIndivisibleDerivativeLifts Ψ)
    (htrans : HasTransitiveSimpleRoots Ψ (facet Ψ c)) :
    hΨ.HasEqualDerivativeLengths := by
  intro a b
  obtain ⟨ψ, hψ, hψlin⟩ := hlift a
  obtain ⟨η, hη, hηlin⟩ := hlift b
  obtain ⟨ψ', hψ', hψlen⟩ := hΨ.exists_simple_corootForm_self_eq hc hψ
  obtain ⟨η', hη', hηlen⟩ := hΨ.exists_simple_corootForm_self_eq hc hη
  obtain ⟨e, he, hcomp⟩ := htrans ψ' hψ' η' hη'
  calc
    hΨ.corootForm a.val a.val = hΨ.corootForm ψ.linear ψ.linear := by rw [hψlin]
    _ = hΨ.corootForm ψ'.linear ψ'.linear := hψlen
    _ = hΨ.corootForm η'.linear η'.linear := by
      rw [hcomp]
      exact (hΨ.corootForm_linear_comp he ψ' ψ').symm
    _ = hΨ.corootForm η.linear η.linear := hηlen.symm
    _ = hΨ.corootForm b.val b.val := by rw [hηlin]

/-- Under the indivisible-lift premise, transitivity on chamber-simple roots
forces symmetry of the full derivative root-coroot pairing. -/
theorem hasSymmetricDerivativePairing_of_transitive_simpleRoots {c : A}
    (hc : GalleryGeometry.IsRegular Ψ c)
    (hlift : HasIndivisibleDerivativeLifts Ψ)
    (htrans : HasTransitiveSimpleRoots Ψ (facet Ψ c)) :
    hΨ.HasSymmetricDerivativePairing :=
  hΨ.hasSymmetricDerivativePairing_of_equal_lengths
    (hΨ.hasEqualDerivativeLengths_of_transitive_simpleRoots hc hlift htrans)

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
