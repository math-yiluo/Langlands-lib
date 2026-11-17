import Langlands.GroupScheme.Reductive.PinnedGaloisTorusSolution
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Descent.SemilinearSolution

/-! # The star action of an actual pinned Galois twist -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitPinning.GaloisTorusSolution

open Descent StarActionIndependence

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {ρ : (K ≃ₐ[k] K) →* p.basedRootDatumAut}
    (s : GaloisTorusSolution p ρ)

/-- The torus comparison in an actual solution is itself an effective torus solution. -/
def torusSolution : Solution (p.galoisTorusDatum ρ) where
  obj := s.torus.toGrp
  iso :=
    { hom := CommGroupScheme.groupHom s.torusIso.hom
      inv := CommGroupScheme.groupHom s.torusIso.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom s.torusIso.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom s.torusIso.inv_hom_id }
  compatible := s.torusCompatible

/-- The actual torus identification intertwines canonical and pinned semilinear maps. -/
theorem torusIso_semilinear (σ : K ≃ₐ[k] K) :
    (CommGroupScheme.baseChange (galoisBaseMap k K σ)).map s.torusIso.hom ≫
        (p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.hom =
      (CommGroupScheme.descentBaseChangeIso (fieldMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) s.torus).hom ≫ s.torusIso.hom := by
  obtain ⟨j, rfl⟩ := (galoisIndexEquiv k K).surjective σ
  exact congrArg Additive.ofMul
    (s.torusSolution.semilinear
      (galoisBaseMap k K (galoisIndexEquiv k K j))
      (galoisBaseMap_over k K (galoisIndexEquiv k K j))
      (finiteGaloisComponent k K j) (finiteGaloisComponent_fst k K j)
      (finiteGaloisComponent_snd k K j)
      (p.galoisSemilinearTorusIso ρ (galoisIndexEquiv k K j))
      (p.pullIso_galoisTorusDatum ρ j))

/-- The ordinary Galois action transported to the original characters is the supplied action. -/
theorem galoisRepresentation_rootEquiv (σ : K ≃ₐ[k] K)
    (χ : characterLattice p.torus) :
    characterLattice.galoisRepresentation k K s.torus σ (s.rootEquiv.weightMap χ) =
      s.rootEquiv.weightMap ((ρ σ).val.weightMap χ) := by
  let a := galoisBaseMap k K σ
  let D := CommGroupScheme.descentBaseChangeIso (fieldMap k K) a
    (galoisBaseMap_over k K σ) s.torus
  let E := (p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso
  have ht : D.inv ≫ (CommGroupScheme.baseChange a).map s.torusIso.hom =
      s.torusIso.hom ≫ E.inv := by
    apply (cancel_mono E.hom).mp
    rw [Category.assoc, s.torusIso_semilinear σ, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hχ := p.semilinearPinnedIso_character σ.toRingEquiv (ρ σ) χ
  change E.inv ≫ (CommGroupScheme.baseChange a).map χ ≫
      (Gm.commBaseChangeIso a).hom = (ρ σ).val.weightMap χ at hχ
  rw [s.rootEquiv_weightMap, s.rootEquiv_weightMap]
  change D.inv ≫ (CommGroupScheme.baseChange a).map (s.torusIso.hom ≫ χ) ≫
    (Gm.commBaseChangeIso a).hom = s.torusIso.hom ≫ (ρ σ).val.weightMap χ
  simp only [Functor.map_comp, ← Category.assoc]
  rw [ht]
  simp only [Category.assoc]
  rw [hχ]

local instance starBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange (fieldMap k K)).obj s.group.obj).X.hom := by
  change IsAffineHom (pullback.snd s.group.obj.X.hom (fieldMap k K))
  infer_instance

/-- The ordinary root-datum action is conjugate to the prescribed based action. -/
theorem galoisAction_eq_conjAut (σ : K ≃ₐ[k] K) :
    s.pinningData.galoisAction σ = conjAut s.rootEquiv (ρ σ).val := by
  apply equiv_ext_of_weightMap
  intro x
  obtain ⟨χ, rfl⟩ := s.rootEquiv.weightEquiv.surjective x
  rw [galoisAction_weightMap_apply, conjAut_weightMap, LinearEquiv.symm_apply_apply]
  exact s.galoisRepresentation_rootEquiv σ χ

/-- The full star action of the descended group is the supplied based action
through the actual base-preserving root equivalence. -/
theorem starAction_intertwine (σ : K ≃ₐ[k] K) :
    RootPairing.Equiv.comp s.rootEquiv (ρ σ).val =
      RootPairing.Equiv.comp (s.pinningData.starAction σ).val s.rootEquiv := by
  have hmem : s.pinningData.galoisAction σ ∈ s.pinningData.toSplitPinning.basedRootDatumAut := by
    rw [s.galoisAction_eq_conjAut]
    exact conjAut_mem_basedRootDatumAut p s.pinningData.toSplitPinning s.rootEquiv
      s.rootEquiv_preserves_base (ρ σ).property
  rw [s.pinningData.starAction_eq_galoisAction σ hmem, s.galoisAction_eq_conjAut]
  exact comp_eq_conjAut_comp s.rootEquiv (ρ σ).val

end Langlands.GroupScheme.SplitPinning.GaloisTorusSolution
