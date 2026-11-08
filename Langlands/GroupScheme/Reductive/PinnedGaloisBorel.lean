import Langlands.GroupScheme.Reductive.PinnedGaloisDatum
import Langlands.GroupScheme.Reductive.PinnedGeometricBorel
import Langlands.GroupScheme.Descent.QuasiSplitDatum

/-! # Actual quasi-split descent from a supplied pinned Galois action -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

namespace Langlands.GroupScheme

namespace Descent

/-- An equivariant actual map respects the normalized semilinear components. -/
theorem semilinearComponent_naturality {S : Scheme.{u}} {B G : GroupScheme S}
    (i : B ⟶ G) {b : S ⟶ S}
    (eB : (GroupScheme.baseChange b).obj B ≅ B)
    (eG : (GroupScheme.baseChange b).obj G ≅ G)
    (he : eB.hom ≫ i = (GroupScheme.baseChange b).map i ≫ eG.hom) :
    (GroupScheme.baseChange (𝟙 S)).map i ≫ (semilinearComponent G eG).hom =
      (semilinearComponent B eB).hom ≫ (GroupScheme.baseChange b).map i := by
  apply (cancel_mono eG.hom).mp
  simp only [semilinearComponent, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← he, Iso.inv_hom_id_assoc]
  exact (((Functor.mapGrpNatIso Over.pullbackId) ≪≫
    Functor.mapGrpIdIso).hom.naturality i)

end Descent

namespace SplitPinning
open Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) (ρ : (K ≃ₐ[k] K) →* p.basedRootDatumAut)

/-- The actual semilinear Borel map supplied by the pinned lift. -/
def galoisSemilinearBorelIso (σ : K ≃ₐ[k] K) :
    (GroupScheme.baseChange (galoisBaseMap k K σ)).obj p.negativeBorel ≅
      p.negativeBorel :=
  p.semilinearNegativeBorelIso σ.toRingEquiv (ρ σ)

theorem galoisSemilinearBorelIso_hom_comp (σ : K ≃ₐ[k] K) :
    (p.galoisSemilinearBorelIso ρ σ).hom ≫ p.negativeBorelHom =
      (GroupScheme.baseChange (galoisBaseMap k K σ)).map p.negativeBorelHom ≫
        (p.galoisSemilinearIso ρ σ).hom :=
  p.semilinearNegativeBorelIso_hom_comp σ.toRingEquiv (ρ σ)

variable [FiniteDimensional k K] [IsGalois k K]

/-- Assemble the Borel overlap from the exact pinned component maps. -/
def galoisBorelOverlap : OverlapIso (fieldMap k K) p.negativeBorel :=
  SemilinearComponents.overlap (fieldMap k K) (finiteGaloisComponent k K)
    (fun i => galoisBaseMap k K (galoisIndexEquiv k K i))
    (finiteGaloisComponent_fst k K) (finiteGaloisComponent_snd k K)
    p.negativeBorel
    (fun i => semilinearComponent p.negativeBorel
      (p.galoisSemilinearBorelIso ρ (galoisIndexEquiv k K i)))

@[simp] theorem pullIso_galoisBorelOverlap (i : Fin (Module.finrank k K)) :
    pullIso (finiteGaloisComponent k K i) (finiteGaloisComponent_fst k K i)
        (finiteGaloisComponent_snd k K i) (p.galoisBorelOverlap ρ) =
      semilinearComponent p.negativeBorel
        (p.galoisSemilinearBorelIso ρ (galoisIndexEquiv k K i)) :=
  SemilinearComponents.pullIso_overlap _ _ _ _ _ _ _ _

/-- The assembled overlap maps respect the actual Borel inclusion. -/
theorem galoisBorelOverlap_hom_comp :
    (GroupScheme.baseChange (fst (fieldMap k K))).map p.negativeBorelHom ≫
        (p.galoisDatum ρ).overlap.hom =
      (p.galoisBorelOverlap ρ).hom ≫
        (GroupScheme.baseChange (snd (fieldMap k K))).map p.negativeBorelHom := by
  apply FiniteComponents.pullHom_ext_along (finiteGaloisComponent k K)
    (finiteGaloisComponent_fst k K) (finiteGaloisComponent_snd k K)
  intro i
  rw [pullHom_comp _ _ (finiteGaloisComponent_fst k K i),
    pullHom_comp _ _ (finiteGaloisComponent_snd k K i),
    pullHom_map, pullHom_map]
  change (GroupScheme.baseChange (𝟙 _)).map p.negativeBorelHom ≫
      (pullIso (finiteGaloisComponent k K i) (finiteGaloisComponent_fst k K i)
        (finiteGaloisComponent_snd k K i) (p.galoisDatum ρ).overlap).hom =
    (pullIso (finiteGaloisComponent k K i) (finiteGaloisComponent_fst k K i)
      (finiteGaloisComponent_snd k K i) (p.galoisBorelOverlap ρ)).hom ≫
      (GroupScheme.baseChange _).map p.negativeBorelHom
  rw [pullIso_galoisDatum, pullIso_galoisBorelOverlap]
  exact semilinearComponent_naturality p.negativeBorelHom _ _
    (p.galoisSemilinearBorelIso_hom_comp ρ (galoisIndexEquiv k K i))

/-- The Borel's all-test subgroup range is invariant over the actual overlap. -/
theorem range_galoisDatum_negativeBorelHom :
    SubgroupFunctor.range
        ((GroupScheme.baseChange (fst (fieldMap k K))).map p.negativeBorelHom ≫
          (p.galoisDatum ρ).overlap.hom) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (snd (fieldMap k K))).map p.negativeBorelHom) := by
  rw [p.galoisBorelOverlap_hom_comp ρ]
  exact SubgroupFunctor.range_iso_comp (p.galoisBorelOverlap ρ) _

/-- The actual Borel datum; its cocycle follows by closed-inclusion cancellation. -/
def galoisBorelDatum : Datum (fieldMap k K) p.negativeBorel where
  overlap := p.galoisBorelOverlap ρ
  cocycle := cocycle_of_closedSubgroup_lift (p.galoisDatum ρ)
    p.isGeometricBorelSubgroup_negativeBorelHom.1.isClosedSubgroup
    (p.galoisBorelOverlap ρ) (p.galoisBorelOverlap_hom_comp ρ).symm

theorem compatible_galoisBorelDatum :
    Compatible (p.galoisBorelDatum ρ) (p.galoisDatum ρ) p.negativeBorelHom :=
  p.galoisBorelOverlap_hom_comp ρ

@[simp] theorem pullIso_galoisBorelDatum (i : Fin (Module.finrank k K)) :
    pullIso (finiteGaloisComponent k K i) (finiteGaloisComponent_fst k K i)
        (finiteGaloisComponent_snd k K i) (p.galoisBorelDatum ρ).overlap =
      semilinearComponent p.negativeBorel
        (p.galoisSemilinearBorelIso ρ (galoisIndexEquiv k K i)) :=
  p.pullIso_galoisBorelOverlap ρ i

/-- Construct the actual quasi-split ground-field group and its descended Borel. -/
def galoisQuasiSplitSolution :
    QuasiSplitSolution (p.galoisDatum ρ) (p.galoisBorelDatum ρ) p.negativeBorelHom :=
  (p.galoisDatum ρ).quasiSplitSolution (p.galoisBorelDatum ρ)
    p.isConnectedReductive p.isGeometricBorelSubgroup_negativeBorelHom
    (p.compatible_galoisBorelDatum ρ)

theorem isQuasiSplit_galoisQuasiSplitSolution :
    IsQuasiSplit (p.galoisQuasiSplitSolution ρ).group.obj :=
  (p.galoisQuasiSplitSolution ρ).quasiSplit

end SplitPinning
end Langlands.GroupScheme
