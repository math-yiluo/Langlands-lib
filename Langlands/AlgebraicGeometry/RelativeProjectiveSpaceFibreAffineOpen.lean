import Langlands.AlgebraicGeometry.RelativeProjectiveSpace
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj

/-! # Finite subsets of a fibre of a closed subscheme of relative projective space lie in an
affine open -/

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

/-- Over an affine open `V` of the base, the part of relative projective space lying over `V`
maps affinely to the integral projective space. -/
theorem isAffineHom_preimage_ι_toIntegral {S : Scheme.{u}} (n : ℕ) (V : S.Opens)
    (hV : IsAffineOpen V) :
    IsAffineHom ((toBase S n ⁻¹ᵁ V).ι ≫ toIntegral S n) := by
  have : IsAffine V := hV
  have h₁ := isPullback_morphismRestrict (toBase S n) V
  have h₂ : IsPullback (toBase S n) (toIntegral S n) (terminal.from S)
      (terminal.from (ProjectiveSpace (ULift.{u} ℤ) n)) :=
    IsPullback.of_hasPullback _ _
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) (h₁.paste_vert h₂) inferInstance

/-- A finite set of points in one fibre of a closed subscheme of relative projective space
lies in an affine open. -/
theorem exists_isAffineOpen_forall_mem_of_fibre
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    (i : X ⟶ RelativeProjectiveSpace S n) [IsClosedImmersion i]
    (hi : i ≫ RelativeProjectiveSpace.toBase S n = f)
    (F : Finset X) (s : S) (hF : ∀ x ∈ F, f x = s) :
    ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ F, x ∈ W := by
  classical
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) (by simp)
  let U : X.Opens := i ⁻¹ᵁ (toBase S n ⁻¹ᵁ V)
  have hmem : ∀ x ∈ F, x ∈ U := by
    intro x hx
    change toBase S n (i x) ∈ V
    rw [← Scheme.Hom.comp_apply, hi, hF x hx]
    exact hsV
  have hι := isAffineHom_preimage_ι_toIntegral n V hV
  let φ : U.toScheme ⟶ Proj (projectiveSpaceGrading (ULift.{u} ℤ) n) :=
    i ∣_ (toBase S n ⁻¹ᵁ V) ≫ (toBase S n ⁻¹ᵁ V).ι ≫ toIntegral S n
  have : IsAffineHom φ := by
    show IsAffineHom (i ∣_ (toBase S n ⁻¹ᵁ V) ≫
      ((toBase S n ⁻¹ᵁ V).ι ≫ toIntegral S n : _ ⟶ ProjectiveSpace (ULift.{u} ℤ) n))
    infer_instance
  obtain ⟨W, hW, hFW⟩ := AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj
    (projectiveSpaceGrading (ULift.{u} ℤ) n) φ (F.subtype (· ∈ U))
  refine ⟨U.ι ''ᵁ W, hW.image_of_isOpenImmersion U.ι, fun x hx => ?_⟩
  have hxW : (⟨x, hmem x hx⟩ : U) ∈ W := hFW _ (Finset.mem_subtype.mpr hx)
  exact ⟨⟨x, hmem x hx⟩, hxW, rfl⟩

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace
