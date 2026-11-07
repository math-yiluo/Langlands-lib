import Langlands.GroupScheme.MatrixRepresentation.CharacterSpaces
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Character spaces detected by separating linear coefficients -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n] {ι : Type v}

/-- Extension of a family of linear coefficients to an algebra, using the
original finite coordinate basis. -/
def coefficientExtension (C : (n → k) →ₗ[k] (ι → k))
    (A : Type*) [CommRing A] [Algebra k A] : (n → A) →ₗ[A] (ι → A) where
  toFun z a := ∑ j, algebraMap k A (C (Pi.single j 1) a) * z j
  map_add' z w := by
    ext a
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    ext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The extension takes a constant vector to its constant coefficient values. -/
theorem coefficientExtension_constants (C : (n → k) →ₗ[k] (ι → k))
    (A : Type*) [CommRing A] [Algebra k A] (z : n → k) (a : ι) :
    coefficientExtension C A (fun j => algebraMap k A (z j)) a =
      algebraMap k A (C z a) := by
  classical
  have hz : z = ∑ j, z j • Pi.single j (1 : k) := by
    ext j
    simp [Pi.single_apply]
  have hc : C z a = ∑ j, z j * C (Pi.single j 1) a := by
    conv_lhs => rw [hz, map_sum]
    simp only [LinearMap.map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hc, map_sum]
  change (∑ j, algebraMap k A (C (Pi.single j 1) a) * algebraMap k A (z j)) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, mul_comm]

variable (ρ : MatrixRepresentation G n)
  (C : (n → k) →ₗ[k] (ι → k)) (χ : ι → rationalCharacters G)

/-- The coefficient family intertwines the universal action with the diagonal
action of the specified actual characters. This is a linear equivariance
condition, with no injectivity, occurrence or highest-weight assertion. -/
def HasCharacterCoefficients : Prop :=
  ∀ (z : n → k) (a : ι),
    coefficientExtension C (CharacterUnits.Coord G) (ρ.universalCharacterAction z) a =
      (CharacterUnits.unit (χ a) : CharacterUnits.Coord G) *
        algebraMap k (CharacterUnits.Coord G) (C z a)

variable (hC : ρ.HasCharacterCoefficients C χ)

include hC in
/-- A nonzero coefficient of a character vector has the same character as
that vector. Cancellation uses a nonzero field scalar, so the coordinate
algebra need not be reduced or a domain. -/
theorem character_eq_of_coefficient_ne_zero {μ : rationalCharacters G}
    {z : n → k} (hz : z ∈ ρ.characterSpace μ) {a : ι} (ha : C z a ≠ 0) :
    μ = χ a := by
  have he := hC z a
  rw [show ρ.universalCharacterAction z =
    (CharacterUnits.unit μ : CharacterUnits.Coord G) • universalVector z from hz,
    map_smul] at he
  change (CharacterUnits.unit μ : CharacterUnits.Coord G) *
    coefficientExtension C (CharacterUnits.Coord G)
      (fun j => algebraMap k (CharacterUnits.Coord G) (z j)) a = _ at he
  rw [coefficientExtension_constants] at he
  have hu : IsUnit (algebraMap k (CharacterUnits.Coord G) (C z a)) :=
    (isUnit_iff_ne_zero.mpr ha).map (algebraMap k (CharacterUnits.Coord G))
  exact CharacterUnits.unit_injective (Units.ext (hu.mul_right_cancel he))

include hC in
/-- Coefficients with a different assigned character vanish. -/
theorem coefficient_eq_zero_of_character_ne {μ : rationalCharacters G}
    {z : n → k} (hz : z ∈ ρ.characterSpace μ) {a : ι} (ha : μ ≠ χ a) :
    C z a = 0 := by
  by_contra hn
  exact ha (character_eq_of_coefficient_ne_zero ρ C χ hC hz hn)

include hC in
/-- Every nonzero character space has an index carrying its actual character,
provided the coefficient family separates the original vector space. -/
theorem exists_coefficient_character (hsep : Function.Injective C)
    {μ : rationalCharacters G} (hμ : ρ.characterSpace μ ≠ ⊥) :
    ∃ a, μ = χ a := by
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  have hc : C z ≠ 0 := fun he => hz0 (hsep (he.trans (map_zero C).symm))
  obtain ⟨a, ha⟩ : ∃ a, C z a ≠ 0 := by
    by_contra hn
    apply hc
    ext a
    exact not_not.mp (fun h => hn ⟨a, h⟩)
  exact ⟨a, character_eq_of_coefficient_ne_zero ρ C χ hC hz ha⟩

include hC in
/-- A finite collection containing all indices of a character bounds the
corresponding weight multiplicity. No finite index type is required. -/
theorem finrank_characterSpace_le (hsep : Function.Injective C)
    (μ : rationalCharacters G) (S : Finset ι)
    (hS : ∀ a, μ = χ a → a ∈ S) :
    Module.finrank k (ρ.characterSpace μ) ≤ S.card := by
  classical
  let L : ρ.characterSpace μ →ₗ[k] (S → k) :=
    (LinearMap.pi fun a => (LinearMap.proj a.val).comp C).comp
      (ρ.characterSpace μ).subtype
  have hL : Function.Injective L := by
    intro z w he
    apply Subtype.ext
    apply hsep
    ext a
    by_cases ha : a ∈ S
    · exact congrFun he ⟨a, ha⟩
    · have hne : μ ≠ χ a := fun h => ha (hS a h)
      exact (coefficient_eq_zero_of_character_ne ρ C χ hC z.property hne).trans
        (coefficient_eq_zero_of_character_ne ρ C χ hC w.property hne).symm
  have hb := LinearMap.finrank_le_finrank_of_injective hL
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hb

include hC in
/-- If at most one coefficient index has the selected character, its
character space is at most one-dimensional. -/
theorem finrank_characterSpace_le_one (hsep : Function.Injective C)
    (μ : rationalCharacters G) (a₀ : ι) (hunique : ∀ a, μ = χ a → a = a₀) :
    Module.finrank k (ρ.characterSpace μ) ≤ 1 := by
  classical
  simpa only [Finset.card_singleton] using
    finrank_characterSpace_le ρ C χ hC hsep μ {a₀}
      (fun a ha => Finset.mem_singleton.mpr (hunique a ha))

include hC in
/-- Occurrence and a unique possible coefficient prove multiplicity one. -/
theorem finrank_characterSpace_eq_one (hsep : Function.Injective C)
    (μ : rationalCharacters G) (a₀ : ι) (hunique : ∀ a, μ = χ a → a = a₀)
    (hμ : ρ.characterSpace μ ≠ ⊥) :
    Module.finrank k (ρ.characterSpace μ) = 1 := by
  apply Nat.le_antisymm (finrank_characterSpace_le_one ρ C χ hC hsep μ a₀ hunique)
  exact Submodule.one_le_finrank_iff.mpr hμ

end Langlands.GroupScheme.MatrixRepresentation
