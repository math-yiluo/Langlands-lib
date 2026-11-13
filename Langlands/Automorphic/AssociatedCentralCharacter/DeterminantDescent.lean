import Langlands.Automorphic.AssociatedCentralCharacterStatement
import Langlands.ClassField.Global.RelativeWeilCharacterFactorization
import Langlands.VirtualRepresentation.ExactDeterminant
import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionStatement

/-! # The Hecke character of the determinant of a relative Weil representation

At an arithmetic class family, the determinant of a continuous finite-dimensional complex
representation `S` of `W_{E/F}` is `δ ∘ τ_F` for exactly one Hecke character `δ` of `F`.
-/

noncomputable section

set_option autoImplicit false

universe u uV

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

/-- A Hecke character is determined by its pullback `χ ∘ τ_F` along the transfer, at an
arithmetic class family. -/
theorem reciprocityCharacter_injective (hc : IsArithmeticClassFamily c) :
    Function.Injective (reciprocityCharacter c F E) := by
  intro χ η h
  obtain ⟨I, hI, hd⟩ := hc
  have hsurj := (relativeWeilTransferReciprocity I hI c hd F E).1
  ext a
  obtain ⟨g, rfl⟩ := hsurj a
  have hg := DFunLike.congr_fun h g
  rw [reciprocityCharacter_apply, reciprocityCharacter_apply, inv_inj] at hg
  rw [hg]

/-- The determinant of a continuous finite-dimensional complex representation of `W_{E/F}`
is continuous for the discrete topology `relativeGaloisTopology` on `Gal(E/F)`. -/
theorem continuous_determinantCharacter_relativeGalois
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)) (hS : S.IsContinuous) :
    letI := relativeGaloisTopology F E
    Continuous (FiniteRepresentation.determinantCharacter S) := by
  have h := FiniteRepresentation.continuous_determinantCharacter S hS
  have key : ∀ t : TopologicalSpace (E ≃ₐ[F] E), krullTopology F E = t →
      (letI := t; Continuous (FiniteRepresentation.determinantCharacter S)) →
      letI := relativeGaloisTopology F E
      Continuous (FiniteRepresentation.determinantCharacter S) := by
    rintro t rfl ht
    rw [krullTopology_eq_relativeGaloisTopology] at ht
    exact ht
  exact key _ rfl h

/-- At an arithmetic class family, the determinant of a continuous representation `S` of
`W_{E/F}` is `δ ∘ τ_F` for some Hecke character `δ` of `F`. -/
theorem exists_determinantCharacter_eq_reciprocityCharacter (hc : IsArithmeticClassFamily c)
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)) (hS : S.IsContinuous) :
    ∃ δ : HeckeCharacter F,
      FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E δ := by
  let := relativeGaloisTopology F E
  let ξ : RelativeWeilGroup c F E →ₜ* ℂˣ :=
    { toMonoidHom := (FiniteRepresentation.determinantCharacter S)⁻¹
      continuous_toFun := (continuous_determinantCharacter_relativeGalois S hS).inv }
  obtain ⟨δ, hδ⟩ := transferCharacterFactorization c hc F E ξ
  refine ⟨δ, ?_⟩
  ext g
  have h := hδ g
  change ((FiniteRepresentation.determinantCharacter S) g)⁻¹ = δ (transfer c F E g) at h
  rw [reciprocityCharacter_apply, ← h, inv_inv]

/-- At an arithmetic class family, the determinant of a continuous representation `S` of
`W_{E/F}` is `δ ∘ τ_F` for exactly one Hecke character `δ` of `F`. -/
theorem existsUnique_determinantCharacter_eq_reciprocityCharacter
    (hc : IsArithmeticClassFamily c)
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)) (hS : S.IsContinuous) :
    ∃! δ : HeckeCharacter F,
      FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E δ := by
  obtain ⟨δ, hδ⟩ := exists_determinantCharacter_eq_reciprocityCharacter hc S hS
  exact ⟨δ, hδ, fun χ hχ => reciprocityCharacter_injective hc (hχ.symm.trans hδ)⟩

end Langlands.ClassField.Global.RelativeWeilGroup
