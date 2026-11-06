import Langlands.GroupScheme.Reductive.NormalizedCovariantCharacter
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Actual characters and finiteness for arbitrary covariance weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineCoordinates

open AffineLinearEmbedding HomogeneousQuotientFromEmbedding

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- A right contraction normalizes any nonzero covariant at the identity. -/
theorem exists_normalized_covariant_of_ne_zero
    (i : H ⟶ G) (χ : algebra H) {f : algebra G}
    (hf : f ∈ leftCovariantSubspace i χ) (hf0 : f ≠ 0) :
    ∃ d : leftCovariantSubspace i χ, counit (corepresentation G) (d : algebra G) = 1 := by
  let := (bialgebra (corepresentation G)).toCoalgebra
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one k hf0
  refine ⟨⟨rightAct ψ f, rightAct_mem_leftCovariantSubspace i χ ψ hf⟩, ?_⟩
  change Coalgebra.counit (R := k) (rightAct ψ f) = 1
  rw [← apply_leftAct, leftAct_counit]
  exact hψ

/-- A chosen normalized covariant, obtained from a supplied nonzero covariant
by a right contraction. No geometric or unipotence hypothesis is used. -/
def covariantNormalization
    (i : H ⟶ G) (χ : algebra H) {f : algebra G}
    (hf : f ∈ leftCovariantSubspace i χ) (hf0 : f ≠ 0) :
    leftCovariantSubspace i χ :=
  Classical.choose (exists_normalized_covariant_of_ne_zero i χ hf hf0)

theorem counit_covariantNormalization
    (i : H ⟶ G) (χ : algebra H) {f : algebra G}
    (hf : f ∈ leftCovariantSubspace i χ) (hf0 : f ≠ 0) :
    counit (corepresentation G) (covariantNormalization i χ hf hf0 : algebra G) = 1 :=
  Classical.choose_spec (exists_normalized_covariant_of_ne_zero i χ hf hf0)

/-- The normalization holds on every relative scheme test. -/
theorem pointAlgebraHom_covariantNormalization_one
    (i : H ⟶ G) (χ : algebra H) {f : algebra G}
    (hf : f ∈ leftCovariantSubspace i χ) (hf0 : f ≠ 0)
    (T : Over (Spec (CommRingCat.of k))) :
    pointAlgebraHom G T 1 (covariantNormalization i χ hf hf0 : algebra G) = 1 := by
  rw [pointAlgebraHom_one]
  change algebraMap k _ (counit (corepresentation G)
    (covariantNormalization i χ hf hf0 : algebra G)) = 1
  rw [counit_covariantNormalization, map_one]

/-- A nonzero covariance space forces its weight to be an actual rational character. -/
def nonzeroCovariantCharacter
    (i : H ⟶ G) (χ : algebra H) {f : algebra G}
    (hf : f ∈ leftCovariantSubspace i χ) (hf0 : f ≠ 0) :
    rationalCharacters H :=
  normalizedCovariantCharacter i χ (covariantNormalization i χ hf hf0)
    (covariantNormalization i χ hf hf0).property
    (pointAlgebraHom_covariantNormalization_one i χ hf hf0 _)

theorem characterCoordinate_nonzeroCovariantCharacter
    (i : H ⟶ G) (χ : algebra H) {f : algebra G}
    (hf : f ∈ leftCovariantSubspace i χ) (hf0 : f ≠ 0) :
    characterCoordinate H (nonzeroCovariantCharacter i χ hf hf0) = χ :=
  characterCoordinate_normalizedCovariantCharacter i χ
    (covariantNormalization i χ hf hf0)
    (covariantNormalization i χ hf hf0).property
    (pointAlgebraHom_covariantNormalization_one i χ hf hf0 _)

/-- Actual rational characters are determined by their affine coordinates. -/
theorem characterCoordinate_injective :
    Function.Injective (characterCoordinate H) := by
  intro α β he
  apply rationalCharacters.ext_characterEval
  intro T h
  apply Units.ext
  have hval := congrArg (pointAlgebraHom H T h) he
  rw [pointAlgebraHom_characterCoordinate H α T h,
    pointAlgebraHom_characterCoordinate H β T h] at hval
  exact hval

/-- The character recovered from a nonzero covariance space is unique. -/
theorem existsUnique_character_of_nonzero_covariant
    (i : H ⟶ G) (χ : algebra H) {f : algebra G}
    (hf : f ∈ leftCovariantSubspace i χ) (hf0 : f ≠ 0) :
    ∃! α : rationalCharacters H, characterCoordinate H α = χ := by
  refine ⟨nonzeroCovariantCharacter i χ hf hf0,
    characterCoordinate_nonzeroCovariantCharacter i χ hf hf0, ?_⟩
  intro α hα
  exact characterCoordinate_injective
    (hα.trans (characterCoordinate_nonzeroCovariantCharacter i χ hf hf0).symm)

/-- A weight that is not the coordinate of a character has zero covariance space. -/
theorem leftCovariantSubspace_eq_bot_of_not_character
    (i : H ⟶ G) (χ : algebra H)
    (hχ : ¬ ∃ α : rationalCharacters H, characterCoordinate H α = χ) :
    leftCovariantSubspace i χ = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  by_contra hf0
  exact hχ ⟨nonzeroCovariantCharacter i χ hf hf0,
    characterCoordinate_nonzeroCovariantCharacter i χ hf hf0⟩

/-- A proper homogeneous quotient gives finiteness for every supplied
covariance weight, including weights not specified to be characters. -/
theorem finite_leftCovariantSubspace_of_proper_quotient
    (i : H ⟶ G) [Mono i.hom.hom] (D : HomogeneousQuotient i)
    [IsProper D.scheme.hom] (χ : algebra H) :
    Module.Finite k (leftCovariantSubspace i χ) := by
  classical
  by_cases hχ : ∃ α : rationalCharacters H, characterCoordinate H α = χ
  · obtain ⟨α, rfl⟩ := hχ
    exact finite_leftCovariantSubspace_characterCoordinate i D α
  · rw [leftCovariantSubspace_eq_bot_of_not_character i χ hχ]
    infer_instance

end Langlands.GroupScheme.AffineCoordinates
