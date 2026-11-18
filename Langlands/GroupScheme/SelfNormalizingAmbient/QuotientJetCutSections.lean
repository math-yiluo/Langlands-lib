import Langlands.GroupScheme.IdentityJetCorepresentedCoordinates
import Langlands.GroupScheme.SelfNormalizingAmbient.QuotientJetCutRepresentative

/-! # Actual sections of identity jets of retained cut subgroups -/

noncomputable section
universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat R ⥤ GrpCat.{u}} {B : CommAlgCat R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  {K : ∀ A : CommAlgCat R, Subgroup (F.obj A)} {I : Ideal B}
  (hI : IsCutOutBy e K I)

/-- The actual cut group's counit restricts the original ambient counit. -/
@[simp]
theorem cut_counit_mk (c : B) :
    (LinearEmbedding.counit (cutCorepresentableBy hI)).hom (Ideal.Quotient.mk I c) =
      (LinearEmbedding.counit e).hom c := rfl

/-- The actual cut group's augmentation-power quotient is the retained jet quotient. -/
def cutJetQuotientEquiv (n : ℕ) :
    ((B ⧸ I) ⧸ augIdeal (cutCorepresentableBy hI) ^ (n + 1)) ≃ₐ[R]
      B ⧸ jetIdeal e I n := by
  have hcomap : (augIdeal (cutCorepresentableBy hI)).comap
      (Ideal.Quotient.mkₐ R I) = augIdeal e := by
    ext c
    rfl
  have hker : augIdeal (cutCorepresentableBy hI) ^ (n + 1) =
      (augIdeal e ^ (n + 1)).map (Ideal.Quotient.mkₐ R I) := by
    rw [Ideal.map_pow, ← hcomap,
      Ideal.map_comap_of_surjective _ (Ideal.Quotient.mkₐ_surjective R I)]
  exact (Ideal.quotientEquivAlgOfEq R hker).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ R I _)

@[simp]
theorem cutJetQuotientEquiv_mk (n : ℕ) (c : B) :
    cutJetQuotientEquiv hI n (Ideal.Quotient.mk _ (Ideal.Quotient.mk I c)) =
      Ideal.Quotient.mk (jetIdeal e I n) c := rfl

@[simp]
theorem cutJetQuotientEquiv_symm_mk (n : ℕ) (c : B) :
    (cutJetQuotientEquiv hI n).symm (Ideal.Quotient.mk (jetIdeal e I n) c) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk I c) := by
  apply (cutJetQuotientEquiv hI n).injective
  rw [AlgEquiv.apply_symm_apply, cutJetQuotientEquiv_mk]

variable {S : Scheme.{u}} (b : S ⟶ Spec R)

/-- The retained ambient jet quotient gives sections of the actual cut identity jet. -/
def cutBaseChangeJetEquiv (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    Γ(S, U) ⊗[R] (B ⧸ jetIdeal e I n) ≃ₗ[Γ(S, U)]
      Γ(IdentityJet.module ((GroupScheme.baseChange b).obj (cutGroupScheme hI)) n, U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Γ(S, U) Γ(S, U))
      (cutJetQuotientEquiv hI n).symm.toLinearEquiv).trans
    (IdentityJet.corepresentedBaseChangeJetEquiv (cutFunctor hI)
      (cutCorepresentableBy hI) b n U)

/-- The comparison sends each retained ambient coordinate to its actual restriction. -/
theorem cutBaseChangeJetEquiv_tmul_mk (n : ℕ) (U : S.affineOpens)
    (a : Γ(S, U)) (c : B) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    cutBaseChangeJetEquiv hI b n U (a ⊗ₜ[R] Ideal.Quotient.mk (jetIdeal e I n) c) =
      a • (IdentityJet.quotientMap
        ((GroupScheme.baseChange b).obj (cutGroupScheme hI)) n).app U
          (IdentityJet.coordinateMap ((GroupScheme.baseChange b).obj (cutGroupScheme hI))
            (Limits.pullback.fst (cutGroupScheme hI).X.hom b) U (Ideal.Quotient.mk I c)) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  change IdentityJet.corepresentedBaseChangeJetEquiv (cutFunctor hI)
    (cutCorepresentableBy hI) b n U
    (a ⊗ₜ[R] (cutJetQuotientEquiv hI n).symm (Ideal.Quotient.mk (jetIdeal e I n) c)) = _
  rw [cutJetQuotientEquiv_symm_mk]
  exact IdentityJet.corepresentedBaseChangeJetEquiv_tmul_mk
    (cutFunctor hI) (cutCorepresentableBy hI) b n U a (Ideal.Quotient.mk I c)

end Langlands.GroupScheme.Corepresented
