import Langlands.GroupScheme.Reductive.PinnedGaloisBorel
import Langlands.GroupScheme.Descent.RelativeSubgroups

/-! # Actual torus descent for a supplied pinned Galois action -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitPinning

open Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) (ρ : (K ≃ₐ[k] K) →* p.basedRootDatumAut)

/-- The torus part of the actual semilinear pinned lift. -/
def galoisSemilinearTorusIso (σ : K ≃ₐ[k] K) :
    (GroupScheme.baseChange (galoisBaseMap k K σ)).obj p.torus.toGrp ≅ p.torus.toGrp where
  hom := CommGroupScheme.groupHom (p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.hom
  inv := CommGroupScheme.groupHom (p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.inv
  hom_inv_id := by
    change CommGroupScheme.groupHom
      ((p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.hom ≫
        (p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.inv) = _
    rw [Iso.hom_inv_id]
    rfl
  inv_hom_id := by
    change CommGroupScheme.groupHom
      ((p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.inv ≫
        (p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.hom) = _
    rw [Iso.inv_hom_id]
    rfl

theorem galoisSemilinearTorusIso_hom_comp (σ : K ≃ₐ[k] K) :
    (p.galoisSemilinearTorusIso ρ σ).hom ≫ p.inclusion =
      (GroupScheme.baseChange (galoisBaseMap k K σ)).map p.inclusion ≫
        (p.galoisSemilinearIso ρ σ).hom :=
  (p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).square.symm

variable [FiniteDimensional k K] [IsGalois k K]

/-- The torus overlap assembled on the actual finite Galois components. -/
def galoisTorusOverlap : OverlapIso (fieldMap k K) p.torus.toGrp :=
  SemilinearComponents.overlap (fieldMap k K) (finiteGaloisComponent k K)
    (fun i => galoisBaseMap k K (galoisIndexEquiv k K i))
    (finiteGaloisComponent_fst k K) (finiteGaloisComponent_snd k K)
    p.torus.toGrp
    (fun i => semilinearComponent p.torus.toGrp
      (p.galoisSemilinearTorusIso ρ (galoisIndexEquiv k K i)))

@[simp] theorem pullIso_galoisTorusOverlap (i : Fin (Module.finrank k K)) :
    pullIso (finiteGaloisComponent k K i) (finiteGaloisComponent_fst k K i)
        (finiteGaloisComponent_snd k K i) (p.galoisTorusOverlap ρ) =
      semilinearComponent p.torus.toGrp
        (p.galoisSemilinearTorusIso ρ (galoisIndexEquiv k K i)) :=
  SemilinearComponents.pullIso_overlap _ _ _ _ _ _ _ _

theorem galoisTorusOverlap_hom_comp :
    (GroupScheme.baseChange (fst (fieldMap k K))).map p.inclusion ≫
        (p.galoisDatum ρ).overlap.hom =
      (p.galoisTorusOverlap ρ).hom ≫
        (GroupScheme.baseChange (snd (fieldMap k K))).map p.inclusion := by
  apply FiniteComponents.pullHom_ext_along (finiteGaloisComponent k K)
    (finiteGaloisComponent_fst k K) (finiteGaloisComponent_snd k K)
  intro i
  rw [pullHom_comp _ _ (finiteGaloisComponent_fst k K i),
    pullHom_comp _ _ (finiteGaloisComponent_snd k K i),
    pullHom_map, pullHom_map]
  change (GroupScheme.baseChange (𝟙 _)).map p.inclusion ≫
      (pullIso (finiteGaloisComponent k K i) (finiteGaloisComponent_fst k K i)
        (finiteGaloisComponent_snd k K i) (p.galoisDatum ρ).overlap).hom =
    (pullIso (finiteGaloisComponent k K i) (finiteGaloisComponent_fst k K i)
      (finiteGaloisComponent_snd k K i) (p.galoisTorusOverlap ρ)).hom ≫
      (GroupScheme.baseChange _).map p.inclusion
  rw [pullIso_galoisDatum, pullIso_galoisTorusOverlap]
  exact semilinearComponent_naturality p.inclusion _ _
    (p.galoisSemilinearTorusIso_hom_comp ρ (galoisIndexEquiv k K i))

/-- The torus Čech datum, with cocycle proved by its closed inclusion. -/
def galoisTorusDatum : Datum (fieldMap k K) p.torus.toGrp where
  overlap := p.galoisTorusOverlap ρ
  cocycle := cocycle_of_closedSubgroup_lift (p.galoisDatum ρ)
    p.isMaximalTorus.2.1 (p.galoisTorusOverlap ρ) (p.galoisTorusOverlap_hom_comp ρ).symm

theorem compatible_galoisTorusDatum :
    Compatible (p.galoisTorusDatum ρ) (p.galoisDatum ρ) p.inclusion :=
  p.galoisTorusOverlap_hom_comp ρ

@[simp] theorem pullIso_galoisTorusDatum (i : Fin (Module.finrank k K)) :
    pullIso (finiteGaloisComponent k K i) (finiteGaloisComponent_fst k K i)
        (finiteGaloisComponent_snd k K i) (p.galoisTorusDatum ρ).overlap =
      semilinearComponent p.torus.toGrp
        (p.galoisSemilinearTorusIso ρ (galoisIndexEquiv k K i)) :=
  p.pullIso_galoisTorusOverlap ρ i

end Langlands.GroupScheme.SplitPinning
