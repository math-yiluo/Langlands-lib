import Langlands.GroupScheme.Descent.SemilinearDatum
import Langlands.GroupScheme.Descent.FiniteGaloisTensor
import Langlands.GroupScheme.Reductive.SemilinearPinningCoherence

/-! # Actual finite Galois descent from a supplied pinning -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

namespace Langlands.GroupScheme
namespace Descent
variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]

/-- Multiplication transported to the small finite component index type. -/
def finiteGaloisIndexMul (i j : Fin (Module.finrank k K)) :
    Fin (Module.finrank k K) :=
  (galoisIndexEquiv k K).symm (galoisIndexEquiv k K i * galoisIndexEquiv k K j)

@[simp] theorem galoisIndexEquiv_mul (i j : Fin (Module.finrank k K)) :
    galoisIndexEquiv k K (finiteGaloisIndexMul k K i j) =
      galoisIndexEquiv k K i * galoisIndexEquiv k K j :=
  (galoisIndexEquiv k K).apply_symm_apply _

/-- Composition of the actual component base maps. -/
theorem finiteGaloisBaseMap_comp (i j : Fin (Module.finrank k K)) :
    galoisBaseMap k K (galoisIndexEquiv k K i) ≫
        galoisBaseMap k K (galoisIndexEquiv k K j) =
      galoisBaseMap k K (galoisIndexEquiv k K (finiteGaloisIndexMul k K i j)) := by
  rw [galoisIndexEquiv_mul, galoisBaseMap_mul]

end Descent

namespace SplitPinning
open Descent
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) (ρ : (K ≃ₐ[k] K) →* p.basedRootDatumAut)

/-- The actual semilinear pinned lift of a prescribed based Galois action. -/
def galoisSemilinearIso (σ : K ≃ₐ[k] K) :
    (GroupScheme.baseChange (galoisBaseMap k K σ)).obj G ≅ G :=
  (p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).groupIso

private theorem semilinear_comp_of_eq (σ τ υ : K ≃+* K)
    (hυ : σ.trans τ = υ)
    (hbc : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom σ.toRingHom) =
      Spec.map (CommRingCat.ofHom υ.toRingHom))
    (e d : p.basedRootDatumAut) :
    pullbackComparison
        (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (Spec.map (CommRingCat.ofHom τ.toRingHom))
        (Spec.map (CommRingCat.ofHom υ.toRingHom)) hbc G ≪≫
        (p.semilinearPinnedIso υ (d * e)).groupIso =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).mapIso
          (p.semilinearPinnedIso σ e).groupIso ≪≫
        (p.semilinearPinnedIso τ d).groupIso := by
  subst υ
  have h := p.semilinearPinnedIso_comp_groupIso σ τ e d
  rw [baseChangeAlongTowerIso_groupIso] at h
  exact h

theorem galoisSemilinearIso_mul (σ τ : K ≃ₐ[k] K) :
    pullbackComparison (galoisBaseMap k K τ) (galoisBaseMap k K σ)
        (galoisBaseMap k K (σ * τ)) (galoisBaseMap_mul k K σ τ).symm G ≪≫
        p.galoisSemilinearIso ρ (σ * τ) =
      (GroupScheme.baseChange (galoisBaseMap k K σ)).mapIso
          (p.galoisSemilinearIso ρ τ) ≪≫ p.galoisSemilinearIso ρ σ := by
  have hστ : τ.toRingEquiv.trans σ.toRingEquiv = (σ * τ).toRingEquiv := by
    ext x
    rfl
  unfold galoisSemilinearIso
  rw [map_mul]
  exact semilinear_comp_of_eq p τ.toRingEquiv σ.toRingEquiv
    (σ * τ).toRingEquiv hστ (galoisBaseMap_mul k K σ τ).symm (ρ τ) (ρ σ)

theorem galoisSemilinearIso_mul_of_eq (σ τ υ : K ≃ₐ[k] K)
    (hυ : σ * τ = υ)
    (hbc : galoisBaseMap k K σ ≫ galoisBaseMap k K τ = galoisBaseMap k K υ) :
    pullbackComparison (galoisBaseMap k K τ) (galoisBaseMap k K σ)
        (galoisBaseMap k K υ) hbc G ≪≫ p.galoisSemilinearIso ρ υ =
      (GroupScheme.baseChange (galoisBaseMap k K σ)).mapIso
          (p.galoisSemilinearIso ρ τ) ≪≫ p.galoisSemilinearIso ρ σ := by
  subst υ
  exact p.galoisSemilinearIso_mul ρ σ τ

variable [FiniteDimensional k K] [IsGalois k K]

theorem finiteGaloisSemilinearIso_mul (i j : Fin (Module.finrank k K)) :
    pullbackComparison
        (galoisBaseMap k K (galoisIndexEquiv k K j))
        (galoisBaseMap k K (galoisIndexEquiv k K i))
        (galoisBaseMap k K (galoisIndexEquiv k K (finiteGaloisIndexMul k K i j)))
        (finiteGaloisBaseMap_comp k K i j) G ≪≫
        p.galoisSemilinearIso ρ (galoisIndexEquiv k K (finiteGaloisIndexMul k K i j)) =
      (GroupScheme.baseChange (galoisBaseMap k K (galoisIndexEquiv k K i))).mapIso
          (p.galoisSemilinearIso ρ (galoisIndexEquiv k K j)) ≪≫
        p.galoisSemilinearIso ρ (galoisIndexEquiv k K i) :=
  p.galoisSemilinearIso_mul_of_eq ρ _ _ _
    (galoisIndexEquiv_mul k K i j).symm (finiteGaloisBaseMap_comp k K i j)

/-- Actual ambient Čech data constructed from the supplied pinning and based action. -/
def galoisDatum : Datum (fieldMap k K) G :=
  SemilinearComponents.datumOfSemilinear (fieldMap k K)
    (finiteGaloisComponent k K)
    (fun i => galoisBaseMap k K (galoisIndexEquiv k K i))
    (finiteGaloisComponent_fst k K) (finiteGaloisComponent_snd k K)
    (finiteGaloisIndexMul k K) (finiteGaloisBaseMap_comp k K) G
    (fun i => p.galoisSemilinearIso ρ (galoisIndexEquiv k K i))
    (p.finiteGaloisSemilinearIso_mul ρ)

@[simp] theorem pullIso_galoisDatum (i : Fin (Module.finrank k K)) :
    pullIso (finiteGaloisComponent k K i) (finiteGaloisComponent_fst k K i)
        (finiteGaloisComponent_snd k K i) (p.galoisDatum ρ).overlap =
      semilinearComponent G (p.galoisSemilinearIso ρ (galoisIndexEquiv k K i)) :=
  SemilinearComponents.pullIso_datumOfSemilinear _ _ _ _ _ _ _ _ _ _ _

end SplitPinning
end Langlands.GroupScheme
