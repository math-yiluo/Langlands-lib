import Langlands.GroupScheme.IdentityJetBaseChangeCoordinates
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Algebra comparisons for actual identity jet sections -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- The actual section algebra induced by the projection of the identity jet. -/
abbrev jetSectionAlgebra (n : ℕ) (U : S.Opens) :
    Algebra Γ(S, U) Γ(scheme G n, projection G n ⁻¹ᵁ U) :=
  ((projection G n).app U).hom.toAlgebra

attribute [local instance] jetSectionAlgebra

variable {R B : CommRingCat.{u}} [Algebra R B]
  (j : G.X.left ⟶ Spec B) (I : Ideal B)
  (n : ℕ) (U : S.Opens) [Algebra R Γ(S, U)]
  (e : Γ(S, U) ⊗[R] (B ⧸ I) ≃ₗ[Γ(S, U)] Γ(module G n, U))
  (he : ∀ (a : Γ(S, U)) (c : B),
    e (a ⊗ₜ[R] Ideal.Quotient.mk I c) = a • jetCoordinateMap G j n U c)

/-- The actual coordinate formula promotes a linear jet section comparison to an algebra
equivalence. -/
def algEquivOfJetCoordinateFormula :
    Γ(S, U) ⊗[R] (B ⧸ I) ≃ₐ[Γ(S, U)] Γ(scheme G n, projection G n ⁻¹ᵁ U) := by
  let f : _ ≃ₗ[Γ(S, U)] Γ(scheme G n, projection G n ⁻¹ᵁ U) := e
  have hf (a : Γ(S, U)) (c : B) :
      f (a ⊗ₜ[R] Ideal.Quotient.mk I c) = a • jetCoordinateMap G j n U c := he a c
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct f ?_ ?_
  · intro a b x y
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul (Ideal.Quotient.mk I), hf, hf, hf, map_mul]
    exact (smul_mul_smul_comm _ _ _ _).symm
  · change f (1 ⊗ₜ[R] Ideal.Quotient.mk I 1) = 1
    rw [hf, one_smul, map_one]

@[simp]
theorem algEquivOfJetCoordinateFormula_toLinearEquiv :
    (algEquivOfJetCoordinateFormula G j I n U e he).toLinearEquiv = e := rfl

/-- The algebra comparison retains the actual ambient function on every pure tensor. -/
theorem algEquivOfJetCoordinateFormula_tmul_mk (a : Γ(S, U)) (c : B) :
    algEquivOfJetCoordinateFormula G j I n U e he (a ⊗ₜ[R] Ideal.Quotient.mk I c) =
      a • jetCoordinateMap G j n U c :=
  he a c

section BaseChange

open AffineCoordinates Corepresented Opposite

variable (H : GroupScheme (Spec R)) [IsAffine H.X.left] (b : S ⟶ Spec R)

private theorem baseChange_affine : IsAffineHom ((GroupScheme.baseChange b).obj H).X.hom := by
  change IsAffineHom (Limits.pullback.snd H.X.hom b)
  exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance

attribute [local instance] baseChange_affine

private theorem baseChangeJetEquiv_tmul_mk_jetCoordinateMap
    (n : ℕ) (U : S.affineOpens) (a : Γ(S, U)) (c : algebra H) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    baseChangeJetEquiv H b n U (a ⊗ₜ[R] Ideal.Quotient.mk _ c) =
      a • jetCoordinateMap ((GroupScheme.baseChange b).obj H)
        (ambientProjection H b (𝟙 _)) n U c := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  rw [baseChangeJetEquiv_tmul_mk, ambientQuotientCoordinates, quotientCoordinates_mk,
    jetCoordinateMap_restrict]

/-- Fixed affine coordinates identify the actual base-changed identity jet as an algebra. -/
def baseChangeJetAlgEquiv (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    let H_b := (GroupScheme.baseChange b).obj H
    Γ(S, U) ⊗[R] (algebra H ⧸ augIdeal (corepresentation H) ^ (n + 1)) ≃ₐ[Γ(S, U)]
      Γ(scheme H_b n, projection H_b n ⁻¹ᵁ U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  exact algEquivOfJetCoordinateFormula _ (ambientProjection H b (𝟙 _)) _ n U
    (baseChangeJetEquiv H b n U) (baseChangeJetEquiv_tmul_mk_jetCoordinateMap H b n U)

@[simp]
theorem baseChangeJetAlgEquiv_toLinearEquiv (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    (baseChangeJetAlgEquiv H b n U).toLinearEquiv = baseChangeJetEquiv H b n U := rfl

/-- Each fixed coordinate maps to its function on the actual jet. -/
theorem baseChangeJetAlgEquiv_tmul_mk (n : ℕ) (U : S.affineOpens)
    (a : Γ(S, U)) (c : algebra H) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    baseChangeJetAlgEquiv H b n U (a ⊗ₜ[R] Ideal.Quotient.mk _ c) =
      a • jetCoordinateMap ((GroupScheme.baseChange b).obj H)
        (ambientProjection H b (𝟙 _)) n U c :=
  baseChangeJetEquiv_tmul_mk_jetCoordinateMap H b n U a c

end BaseChange

end Langlands.GroupScheme.IdentityJet
