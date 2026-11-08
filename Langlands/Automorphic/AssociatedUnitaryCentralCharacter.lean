import Langlands.Automorphic.AssociatedCentralCharacterStatement
import Langlands.ClassField.Global.RelativeWeilTransferReciprocityProof
import Langlands.Weil.Representation.Determinant
import Mathlib.Analysis.InnerProductSpace.NormDet

/-! # Unitary central characters from actual determinant matching -/

noncomputable section

universe uG uV uF uP

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- A finite-dimensional unitary action has a modulus-one determinant character. -/
theorem norm_determinantCharacter_of_isUnitary
    (S : FiniteRepresentation.{0, uG, uV} ℂ G) (hS : S.IsUnitary) (g : G) :
    ‖(determinantCharacter S g : ℂ)‖ = 1 := by
  obtain ⟨h, hh⟩ := hS
  let := h
  let : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ S :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ S)
  let e : S →ₗᵢ[ℂ] S := (S.representation g).isometryOfInner (hh g)
  change ‖LinearMap.det (S.representation g)‖ = 1
  rw [← LinearMap.normDet_eq_norm_det]
  exact e.normDet_eq_one

end Langlands.FiniteRepresentation

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] (c : FundamentalClass.ClassFamily.{uF})

/-- Surjectivity of the actual transfer detects modulus one after reciprocity pullback. -/
theorem heckeCharacter_isUnitary_of_reciprocityCharacter
    (hc : IsArithmeticClassFamily c) (ω : HeckeCharacter F)
    (hω : ∀ g : RelativeWeilGroup c F E, ‖(reciprocityCharacter c F E ω g : ℂ)‖ = 1) :
    ω.IsUnitary := by
  obtain ⟨I, hI, hd⟩ := hc
  have hsurj := (relativeWeilTransferReciprocity I hI c hd F E).1
  intro a
  obtain ⟨g, rfl⟩ := hsurj a
  have hg := hω g
  change ‖(((ω (transfer c F E g))⁻¹ : ℂˣ) : ℂ)‖ = 1 at hg
  rw [Units.val_inv_eq_inv_val, norm_inv] at hg
  exact inv_eq_one.mp hg

/-- Any matching Hecke character of a unitary Weil determinant is globally unitary. -/
theorem heckeCharacter_isUnitary_of_determinant
    (hc : IsArithmeticClassFamily c)
    (S : FiniteRepresentation.{0, uF, uV} ℂ (RelativeWeilGroup c F E))
    (hS : S.IsUnitary) (ω : HeckeCharacter F)
    (hdet : FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E ω) :
    ω.IsUnitary := by
  apply heckeCharacter_isUnitary_of_reciprocityCharacter F E c hc ω
  intro g
  rw [← hdet]
  exact FiniteRepresentation.norm_determinantCharacter_of_isUnitary S hS g

variable [CompactSpace (AdeleQuotient F)]

/-- Given the exact central-character comparison, an actual unitary associated
representation has a unitary central character. -/
theorem hasUnitaryCentralCharacter_of_associatedCentralCharacter
    (hcentral : AssociatedCentralCharacterStatement.{uF, uV, uP})
    (hc : IsArithmeticClassFamily c) {r : ℕ}
    (S : FiniteRepresentation.{0, uF, uV} ℂ (RelativeWeilGroup c F E))
    (T : Langlands.Automorphic.CuspidalOperatorRealization F r)
    (hassoc : IsWeaklyAssociatedClass.{uF, uV, uP} S T.isoClass)
    (hS : S.IsUnitary) : HasUnitaryCentralCharacter T := by
  obtain ⟨ω, hω, hdet, _⟩ := hcentral c hc F E S T hassoc
  exact ⟨ω, heckeCharacter_isUnitary_of_determinant F E c hc S hS ω hdet, hω⟩

/-- Choose a genuine globally unitary central Hecke character from the proved
comparison input, retaining its actual action on the cuspidal realization. -/
def associatedUnitaryCentralCharacter
    (hcentral : AssociatedCentralCharacterStatement.{uF, uV, uP})
    (hc : IsArithmeticClassFamily c) {r : ℕ}
    (S : FiniteRepresentation.{0, uF, uV} ℂ (RelativeWeilGroup c F E))
    (T : Langlands.Automorphic.CuspidalOperatorRealization F r)
    (hassoc : IsWeaklyAssociatedClass.{uF, uV, uP} S T.isoClass)
    (hS : S.IsUnitary) :
    {ω : HeckeCharacter F // ω.IsUnitary ∧ T.HasCentralCharacter ω} :=
  ⟨Classical.choose
      (hasUnitaryCentralCharacter_of_associatedCentralCharacter F E c hcentral hc S T hassoc hS),
    Classical.choose_spec
      (hasUnitaryCentralCharacter_of_associatedCentralCharacter F E c hcentral hc S T hassoc hS)⟩

end Langlands.ClassField.Global.RelativeWeilGroup
