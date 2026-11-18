import Langlands.GroupScheme.IdentityJetAlgebraCoordinates
import Langlands.GroupScheme.SelfNormalizingAmbient.QuotientJetOriginalSections

/-! # Actual jet section algebras in supplied and retained ambient coordinates -/

noncomputable section

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.IdentityJet

open Corepresented

attribute [local instance] jetSectionAlgebra

/-- The section algebra from the composite to the affine base factors through the projection. -/
theorem jetSectionScalarTower {R : CommRingCat.{u}} {S : Scheme.{u}}
    (H : GroupScheme S) (b : S ⟶ Spec R) (n : ℕ) (U : S.Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H n ≫ b) (projection H n ⁻¹ᵁ U)
    IsScalarTower R Γ(S, U) Γ(scheme H n, projection H n ⁻¹ᵁ U) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let := Scheme.TwoAffineOpenCover.algebraOfHom (projection H n ≫ b) (projection H n ⁻¹ᵁ U)
  apply IsScalarTower.of_algebraMap_eq
  intro r
  have h := Scheme.Hom.appLE_comp_appLE (projection H n) b ⊤ U
    (projection H n ⁻¹ᵁ U) (by simp) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at h
  exact (ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso R).inv r)).symm

section Corepresentation

variable {R : CommRingCat.{u}} (F : CommAlgCat R ⥤ GrpCat.{u})
  {B : CommAlgCat R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {S : Scheme.{u}} (b : S ⟶ Spec R)

/-- The supplied corepresenting algebra gives the actual base-changed jet section algebra. -/
def corepresentedBaseChangeJetAlgEquiv (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    let H := (GroupScheme.baseChange b).obj (groupScheme F e)
    Γ(S, U) ⊗[R] (B ⧸ augIdeal e ^ (n + 1)) ≃ₐ[Γ(S, U)]
      Γ(scheme H n, projection H n ⁻¹ᵁ U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  refine algEquivOfJetCoordinateFormula (R := R) (B := CommRingCat.of B)
    ((GroupScheme.baseChange b).obj (groupScheme F e))
    (Limits.pullback.fst (groupScheme F e).X.hom b) (augIdeal e ^ (n + 1)) n U
    (corepresentedBaseChangeJetEquiv F e b n U) ?_
  intro a c
  rw [jetCoordinateMap_eq]
  exact corepresentedBaseChangeJetEquiv_tmul_mk F e b n U a c

@[simp]
theorem corepresentedBaseChangeJetAlgEquiv_toLinearEquiv (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    (corepresentedBaseChangeJetAlgEquiv F e b n U).toLinearEquiv =
      corepresentedBaseChangeJetEquiv F e b n U := rfl

/-- Each supplied coordinate maps to its actual jet restriction. -/
theorem corepresentedBaseChangeJetAlgEquiv_tmul_mk (n : ℕ) (U : S.affineOpens)
    (a : Γ(S, U)) (c : B) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    corepresentedBaseChangeJetAlgEquiv F e b n U (a ⊗ₜ[R] Ideal.Quotient.mk _ c) =
      a • jetCoordinateMap ((GroupScheme.baseChange b).obj (groupScheme F e))
        (Limits.pullback.fst (groupScheme F e).X.hom b) n U c := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  change corepresentedBaseChangeJetEquiv F e b n U (a ⊗ₜ[R] Ideal.Quotient.mk _ c) = _
  rw [jetCoordinateMap_eq]
  exact corepresentedBaseChangeJetEquiv_tmul_mk F e b n U a c

end Corepresentation

end Langlands.GroupScheme.IdentityJet

namespace Langlands.GroupScheme.SelfNormalizingAmbient.ProperQuotientJetData

open IdentityJet AffineCoordinates Corepresented

attribute [local instance] IdentityJet.jetSectionAlgebra

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} [IsAffine G.X.left]
  {i : H ⟶ G} {Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient i}
  (D : ProperQuotientJetData i Q) {S : Scheme.{u}} (b : S ⟶ Spec R)

/-- The retained ambient quotient gives the original subgroup's actual jet section algebra. -/
def originalBaseChangeJetAlgEquiv (hi : IsClosedSubgroup i) (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    let H_b := (GroupScheme.baseChange b).obj H
    Γ(S, U) ⊗[R] (algebra G ⧸ jetIdeal (corepresentation G) D.ideal n) ≃ₐ[Γ(S, U)]
      Γ(scheme H_b n, projection H_b n ⁻¹ᵁ U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  refine algEquivOfJetCoordinateFormula (R := R) (B := CommRingCat.of (algebra G))
    ((GroupScheme.baseChange b).obj H)
    (ambientProjection G b ((GroupScheme.baseChange b).map i))
    (jetIdeal (corepresentation G) D.ideal n) n U
    (D.originalBaseChangeJetEquiv b hi n U) ?_
  intro a c
  rw [jetCoordinateMap_eq]
  exact D.originalBaseChangeJetEquiv_tmul_mk b hi n U a c

@[simp]
theorem originalBaseChangeJetAlgEquiv_toLinearEquiv (hi : IsClosedSubgroup i)
    (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    (D.originalBaseChangeJetAlgEquiv b hi n U).toLinearEquiv =
      D.originalBaseChangeJetEquiv b hi n U := rfl

/-- Each retained ambient coordinate maps to its actual restriction on the original jet. -/
theorem originalBaseChangeJetAlgEquiv_tmul_mk (hi : IsClosedSubgroup i)
    (n : ℕ) (U : S.affineOpens) (a : Γ(S, U)) (c : algebra G) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    D.originalBaseChangeJetAlgEquiv b hi n U
        (a ⊗ₜ[R] Ideal.Quotient.mk (jetIdeal (corepresentation G) D.ideal n) c) =
      a • jetCoordinateMap ((GroupScheme.baseChange b).obj H)
        (ambientProjection G b ((GroupScheme.baseChange b).map i)) n U c := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  change D.originalBaseChangeJetEquiv b hi n U (a ⊗ₜ[R] Ideal.Quotient.mk _ c) = _
  rw [jetCoordinateMap_eq]
  exact D.originalBaseChangeJetEquiv_tmul_mk b hi n U a c

end Langlands.GroupScheme.SelfNormalizingAmbient.ProperQuotientJetData
