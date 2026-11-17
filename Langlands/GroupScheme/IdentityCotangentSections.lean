import Langlands.GroupScheme.IdentityJetSheaf
import Langlands.AlgebraicGeometry.RelativeDifferentialsAffineSections
import Langlands.AlgebraicGeometry.SmoothDifferentialsFiniteLocalBasisRank
import Langlands.RingTheory.Smooth.AugmentationCotangentDifferentials

/-! # Actual affine identity-cotangent sections and the augmentation quotient -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.IdentityCotangent

open Langlands.Scheme
open Langlands.Scheme.Modules
open IdentityJet

variable {S : Scheme.{u}} (G : GroupScheme S) [IsAffineHom G.X.hom]

attribute [local instance] sectionAlgebra

/-- Functions on the base are an algebra over group functions via the actual identity. -/
abbrev augmentationAlgebra (U : S.affineOpens) :
    Algebra Γ(G.X.left, G.X.hom ⁻¹ᵁ U) Γ(S, U) :=
  (augmentation G U).toRingHom.toAlgebra

attribute [local instance] augmentationAlgebra

instance augmentationScalarTower (U : S.affineOpens) :
    IsScalarTower Γ(S, U) Γ(G.X.left, G.X.hom ⁻¹ᵁ U) Γ(S, U) :=
  IsScalarTower.of_algebraMap_eq (fun r => (augmentation G U).commutes r |>.symm)

omit [IsAffineHom G.X.hom] in
theorem projection_appLE_self (U : S.affineOpens) :
    G.X.hom.appLE U (G.X.hom ⁻¹ᵁ U) le_rfl = G.X.hom.app U := by
  simp [Scheme.Hom.appLE]

/-- Actual differential sections above an affine base open are the Kähler
differentials of the actual group section ring. -/
def differentialSectionsEquiv (U : S.affineOpens) :
    Γ(relativeDifferentials G.X.hom, G.X.hom ⁻¹ᵁ U) ≃ₗ[Γ(G.X.left, G.X.hom ⁻¹ᵁ U)]
      KaehlerDifferential Γ(S, U) Γ(G.X.left, G.X.hom ⁻¹ᵁ U) := by
  have e := relativeDifferentialsSectionsIso G.X.hom U.2 (affineOpen G U).2 le_rfl
  have hAlg : (G.X.hom.appLE U (G.X.hom ⁻¹ᵁ U) le_rfl).hom.toAlgebra =
      sectionAlgebra G U := by
    rw [projection_appLE_self]
  exact (hAlg ▸ e).toLinearEquiv

omit [IsAffineHom G.X.hom] in
theorem smoothDifferentials_isQuasicoherent (hG : Smooth G.X.hom) :
    (relativeDifferentials G.X.hom).IsQuasicoherent := by
  obtain ⟨q, hq, -⟩ :=
    (smoothDifferentialsFiniteLocalBasisRank G.X.left S G.X.hom).1 hG
  let := hq
  let := q.isLocallyFree
  infer_instance

/-- The canonical affine pullback tensor map for the actual identity cotangent. -/
def pullbackSectionsEquiv [ (relativeDifferentials G.X.hom).IsQuasicoherent]
    (U : S.affineOpens) :
    (Γ(S, U) ⊗[Γ(G.X.left, G.X.hom ⁻¹ᵁ U)]
      Γ(relativeDifferentials G.X.hom, G.X.hom ⁻¹ᵁ U)) ≃ₗ[Γ(S, U)]
      Γ(G.cotangentAtIdentity, U) := by
  exact LinearEquiv.ofBijective
    (pullbackTensorMap G.identitySection (relativeDifferentials G.X.hom)
      (le_of_eq (identity_preimage G U).symm)).hom
    (pullbackTensorMap_bijective G.identitySection _ _
      U.2 (affineOpen G U).2)

theorem pullbackSectionsEquiv_one_tmul
    [(relativeDifferentials G.X.hom).IsQuasicoherent] (U : S.affineOpens)
    (m : Γ(relativeDifferentials G.X.hom, G.X.hom ⁻¹ᵁ U)) :
    pullbackSectionsEquiv G U ((1 : Γ(S, U)) ⊗ₜ[Γ(G.X.left, G.X.hom ⁻¹ᵁ U)] m) =
      sectionPullbackLE G.identitySection (relativeDifferentials G.X.hom)
        (le_of_eq (identity_preimage G U).symm) m :=
  pullbackTensorMap_one_tmul _ _ _ m

/-- The actual identity-cotangent sections are the actual augmentation quotient,
over every affine base open of a smooth affine group scheme. -/
def sectionsEquiv (hG : Smooth G.X.hom) (U : S.affineOpens) :
    Γ(G.cotangentAtIdentity, U) ≃ₗ[Γ(S, U)]
      (RingHom.ker (augmentation G U)).Cotangent := by
  let := smoothDifferentials_isQuasicoherent G hG
  exact (pullbackSectionsEquiv G U).symm.trans
    ((LinearEquiv.baseChange Γ(G.X.left, G.X.hom ⁻¹ᵁ U) Γ(S, U) _ _
      (differentialSectionsEquiv G U)).trans
      (Algebra.AugmentationCotangent.cotangentEquivTensor
        Γ(S, U) Γ(G.X.left, G.X.hom ⁻¹ᵁ U)).symm)

/-- The affine comparison sends a pulled-back algebraic differential to its
actual augmentation class. -/
theorem sectionsEquiv_pullback_model_D (hG : Smooth G.X.hom) (U : S.affineOpens)
    (a : Γ(G.X.left, G.X.hom ⁻¹ᵁ U)) :
    sectionsEquiv G hG U
        (sectionPullbackLE G.identitySection (relativeDifferentials G.X.hom)
          (le_of_eq (identity_preimage G U).symm)
          ((differentialSectionsEquiv G U).symm
            (KaehlerDifferential.D Γ(S, U) Γ(G.X.left, G.X.hom ⁻¹ᵁ U) a))) =
      CoordinateWeights.AugmentedAlgebra.classMap (augmentation G U) a := by
  let := smoothDifferentials_isQuasicoherent G hG
  rw [← pullbackSectionsEquiv_one_tmul]
  change (Algebra.AugmentationCotangent.cotangentEquivTensor
    Γ(S, U) Γ(G.X.left, G.X.hom ⁻¹ᵁ U)).symm
      ((LinearEquiv.baseChange Γ(G.X.left, G.X.hom ⁻¹ᵁ U) Γ(S, U) _ _
        (differentialSectionsEquiv G U))
        ((pullbackSectionsEquiv G U).symm
          (pullbackSectionsEquiv G U ((1 : Γ(S, U)) ⊗ₜ[Γ(G.X.left, G.X.hom ⁻¹ᵁ U)]
            ((differentialSectionsEquiv G U).symm
              (KaehlerDifferential.D Γ(S, U) Γ(G.X.left, G.X.hom ⁻¹ᵁ U) a)))))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.apply_symm_apply]
  change Algebra.AugmentationCotangent.fromTensor
      Γ(S, U) Γ(G.X.left, G.X.hom ⁻¹ᵁ U)
      ((1 : Γ(S, U)) ⊗ₜ[Γ(G.X.left, G.X.hom ⁻¹ᵁ U)]
        KaehlerDifferential.D Γ(S, U) Γ(G.X.left, G.X.hom ⁻¹ᵁ U) a) = _
  rw [Algebra.AugmentationCotangent.fromTensor_tmul_D, one_smul]
  rfl

end Langlands.GroupScheme.IdentityCotangent
