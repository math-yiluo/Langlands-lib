import Langlands.AlgebraicGeometry.IntegralSchemePushoutCompatibleOpens

/-! # A compatible affine cover for integral pinching -/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Langlands.AlgebraicGeometry

/-- All affine pairs with the same inverse-image open in the common source. -/
def CompatibleAffinePairs {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) :=
  {p : X.affineOpens × Y.affineOpens // i ⁻¹ᵁ p.1.1 = j ⁻¹ᵁ p.2.1}

namespace CompatibleAffinePairs

variable {X Y Z : Scheme.{u}} {i : Z ⟶ X} {j : Z ⟶ Y}

/-- The open on the closed-immersion side of a compatible affine pair. -/
abbrev left (p : CompatibleAffinePairs i j) : X.affineOpens := p.1.1

/-- The open on the integral side of a compatible affine pair. -/
abbrev right (p : CompatibleAffinePairs i j) : Y.affineOpens := p.1.2

theorem compatible (p : CompatibleAffinePairs i j) :
    i ⁻¹ᵁ p.left.1 = j ⁻¹ᵁ p.right.1 := p.2

end CompatibleAffinePairs

/-- Compatible affine pairs cover the integral side. -/
theorem compatibleAffinePairs_cover_right
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegralHom j]
    (hF : ∀ y : Y, ∃ U : X.Opens,
      IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U) :
    IsOpenCover (fun p : CompatibleAffinePairs i j => p.right.1) := by
  apply top_le_iff.mp
  intro y _
  obtain ⟨U, V, hyV, hUV⟩ := exists_compatible_affineOpens_of_integral i j hF y
  exact Opens.mem_iSup.mpr ⟨⟨(U, V), hUV⟩, hyV⟩

/-- Compatible affine pairs cover the closed-immersion side, including its open
complement of the closed image. -/
theorem compatibleAffinePairs_cover_left
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegralHom j]
    (hF : ∀ y : Y, ∃ U : X.Opens,
      IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U) :
    IsOpenCover (fun p : CompatibleAffinePairs i j => p.left.1) := by
  classical
  apply top_le_iff.mp
  intro x _
  by_cases hx : x ∈ Set.range i
  · obtain ⟨z, rfl⟩ := hx
    obtain ⟨U, V, hzV, hUV⟩ :=
      exists_compatible_affineOpens_of_integral i j hF (j z)
    refine Opens.mem_iSup.mpr ⟨⟨(U, V), hUV⟩, ?_⟩
    change z ∈ i ⁻¹ᵁ U.1
    rw [hUV]
    exact hzV
  · let W : X.Opens :=
      ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨U, hU, hxU, hUW⟩ :=
      exists_isAffineOpen_mem_and_subset (show x ∈ W from hx)
    have hUV : i ⁻¹ᵁ U = j ⁻¹ᵁ (⊥ : Y.Opens) := by
      ext z
      change i z ∈ U ↔ False
      exact ⟨fun hz => (hUW hz) ⟨z, rfl⟩, False.elim⟩
    exact Opens.mem_iSup.mpr ⟨⟨(⟨U, hU⟩, ⟨⊥, isAffineOpen_bot Y⟩), hUV⟩, hxU⟩

/-- The actual open cover of `X` by all compatible affine pairs. -/
noncomputable def integralCompatibleAffineCoverLeft
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegralHom j]
    (hF : ∀ y : Y, ∃ U : X.Opens,
      IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U) : X.OpenCover :=
  X.openCoverOfIsOpenCover (fun p : CompatibleAffinePairs i j => p.left.1)
    (compatibleAffinePairs_cover_left i j hF)

/-- The actual open cover of `Y` with the same compatible-pair index. -/
noncomputable def integralCompatibleAffineCoverRight
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegralHom j]
    (hF : ∀ y : Y, ∃ U : X.Opens,
      IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U) : Y.OpenCover :=
  Y.openCoverOfIsOpenCover (fun p : CompatibleAffinePairs i j => p.right.1)
    (compatibleAffinePairs_cover_right i j hF)

instance isAffine_integralCompatibleAffineCoverLeft
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegralHom j]
    (hF : ∀ y : Y, ∃ U : X.Opens,
      IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U)
    (p : CompatibleAffinePairs i j) :
    IsAffine ((integralCompatibleAffineCoverLeft i j hF).X p) := p.left.2

instance isAffine_integralCompatibleAffineCoverRight
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegralHom j]
    (hF : ∀ y : Y, ∃ U : X.Opens,
      IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U)
    (p : CompatibleAffinePairs i j) :
    IsAffine ((integralCompatibleAffineCoverRight i j hF).X p) := p.right.2

end Langlands.AlgebraicGeometry
