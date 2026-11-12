import Langlands.Representation.LanglandsClassification.LanglandsTriplet

/-! # Recovering the standard index from a dominant full character

The open faces of the full simple-coroot chamber are disjoint. Restriction
recovers the published coroot chambers of an actual split component, but no
uniqueness of a lift from that component is asserted.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)

/-- The simple roots whose supplied coroots vanish at a full real character.
Central directions are retained in the character space. -/
def simpleCorootZeroIndex (x : Vstar T) : Set (characterLattice T) :=
  {χ | ∃ α : relativeRoots i, α.val = χ ∧ α.val ∈ simpleRelativeRoots i ν ∧
    pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0}

/-- The full simple-coroot face with zeros at the selected roots and strict
positivity at every complementary simple root. -/
def openSimpleCorootFace (J : Set (characterLattice T)) : Set (Vstar T) :=
  {x | (∀ α : relativeRoots i, α.val ∈ J →
      pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0) ∧
    (∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν → α.val ∉ J →
      0 < pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))}

theorem simpleCorootZeroIndex_subset (x : Vstar T) :
    simpleCorootZeroIndex i ν D x ⊆ simpleRelativeRoots i ν := by
  rintro χ ⟨α, rfl, hα, _⟩
  exact hα

/-- On a full open face, its index is exactly the zero set of the simple
coroot evaluations. -/
theorem eq_simpleCorootZeroIndex_of_mem_openFace
    {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {x : Vstar T} (hx : x ∈ openSimpleCorootFace i ν D J) :
    J = simpleCorootZeroIndex i ν D x := by
  ext χ
  constructor
  · intro hχ
    exact ⟨⟨χ, (hJ hχ).1.1⟩, rfl, hJ hχ, hx.1 ⟨χ, (hJ hχ).1.1⟩ hχ⟩
  · rintro ⟨α, rfl, hα, hzero⟩
    by_contra hnot
    exact (hx.2 α hα hnot).ne' hzero

/-- Equal full lifts in two open faces force equality of their standard
indices. Equality only after restriction is not a premise of this theorem. -/
theorem index_eq_of_equal_openFace_lifts
    {J₁ J₂ : Set (characterLattice T)}
    (hJ₁ : J₁ ⊆ simpleRelativeRoots i ν) (hJ₂ : J₂ ⊆ simpleRelativeRoots i ν)
    {x₁ x₂ : Vstar T}
    (hx₁ : x₁ ∈ openSimpleCorootFace i ν D J₁)
    (hx₂ : x₂ ∈ openSimpleCorootFace i ν D J₂)
    (hxeq : x₁ = x₂) : J₁ = J₂ := by
  rw [eq_simpleCorootZeroIndex_of_mem_openFace i ν D hJ₁ hx₁,
    eq_simpleCorootZeroIndex_of_mem_openFace i ν D hJ₂ hx₂, hxeq]

/-- Every dominant full character belongs to the face cut out by exactly its
zero simple-coroot evaluations. -/
theorem mem_openFace_zeroIndex_of_dominant {x : Vstar T}
    (hx : ∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν →
      0 ≤ pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)) :
    x ∈ openSimpleCorootFace i ν D (simpleCorootZeroIndex i ν D x) := by
  constructor
  · intro α hα
    obtain ⟨β, hβ, _, hz⟩ := hα
    have heq : β = α := Subtype.ext hβ
    rwa [heq] at hz
  · intro α hα hnot
    have hnonneg := hx α hα
    have hne : pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) ≠ 0 := by
      intro hz
      exact hnot ⟨α, rfl, hα, hz⟩
    exact lt_of_le_of_ne hnonneg hne.symm

/-- A dominant full character has a unique simple-root index for its open
face, including the empty root system and all boundary faces. -/
theorem existsUnique_openFace_of_dominant {x : Vstar T}
    (hx : ∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν →
      0 ≤ pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)) :
    ∃! J : Set (characterLattice T),
      J ⊆ simpleRelativeRoots i ν ∧ x ∈ openSimpleCorootFace i ν D J := by
  refine ⟨simpleCorootZeroIndex i ν D x,
    ⟨simpleCorootZeroIndex_subset i ν D x, mem_openFace_zeroIndex_of_dominant i ν D hx⟩, ?_⟩
  intro J hJ
  exact eq_simpleCorootZeroIndex_of_mem_openFace i ν D hJ.1 hJ.2

/-- The published chamber of a split component is exactly the image of the
corresponding full face under the actual character restriction map. -/
theorem restrictedCorootChamber_eq_image_openFace
    (J : Set (characterLattice T)) (f : A ⟶ T) :
    restrictedCorootChamber i ν J f D =
      rationalCharacterRestrictReal (CommGroupScheme.groupHom f) ''
        openSimpleCorootFace i ν D J := by
  ext x
  constructor
  · rintro ⟨y, hy, hzero, hpos⟩
    exact ⟨y, ⟨hzero, hpos⟩, hy⟩
  · rintro ⟨y, ⟨hzero, hpos⟩, hy⟩
    exact ⟨y, hy, hzero, hpos⟩

end Langlands.GroupScheme
