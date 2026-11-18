import Langlands.GroupScheme.Reductive.RootDatumTorusTransport
import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.SimplyConnected.NormOneMatrixRepresentation
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition

/-! # Actual pinnings and highest weights under an ambient group isomorphism -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

section WeightSpace

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The ambient differential identifies weight spaces while retaining the same torus character. -/
def weightSpaceCompIsoEquiv (i : T.toGrp ⟶ G) (e : G ≅ H)
    (lam : characterLattice T) :
    weightSpace i lam ≃ₗ[k] weightSpace (i ≫ e.hom) lam where
  toFun x := ⟨Lie.targetMapLinear e.hom (CommRingCat.of k) x.val, by
    have h := lieKernelHomLinear_mem_weightSpace_of_transport (Iso.refl T) e.hom
      (show i ≫ e.hom =
        CommGroupScheme.groupHom (Iso.refl T).hom ≫ (i ≫ e.hom) from
          (Category.id_comp _).symm) lam x.property
    have hc : characterLattice.congr (Iso.refl T) lam = lam := Category.id_comp lam
    rw [hc] at h
    exact h⟩
  invFun y := ⟨Lie.targetMapLinear e.inv (CommRingCat.of k) y.val, by
    apply (lieKernelHomLinear_mem_weightSpace_transport_iff (Iso.refl T) e
      (show i ≫ e.hom =
        CommGroupScheme.groupHom (Iso.refl T).hom ≫ (i ≫ e.hom) from
          (Category.id_comp _).symm) lam _).mp
    have hc : characterLattice.congr (Iso.refl T) lam = lam := Category.id_comp lam
    rw [hc, Lie.targetMapLinear_inv_hom]
    exact y.property⟩
  left_inv x := Subtype.ext (Lie.targetMapLinear_hom_inv e (CommRingCat.of k) x.val)
  right_inv y := Subtype.ext (Lie.targetMapLinear_inv_hom e (CommRingCat.of k) y.val)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' c x := Subtype.ext (map_smul _ c x.val)

end WeightSpace

namespace SplitPinning

variable (p : SplitPinning G) (e : G ≅ H)

/-- Transport an actual pinning through the group isomorphism, retaining its torus and lattices. -/
def mapGroupIso : SplitPinning H where
  isConnectedReductive := p.isConnectedReductive.of_iso e.symm
  torus := p.torus
  inclusion := p.inclusion ≫ e.hom
  isSplitTorus := p.isSplitTorus
  isMaximalTorus := p.isMaximalTorus.comp_iso e
  rootIndex := p.rootIndex
  rootDatum := p.rootDatum
  isRootDatum := p.isRootDatum.comp_iso e
  isReduced := p.isReduced
  base := p.base
  pinning.trivialization a := (p.pinning.trivialization a).trans
    (weightSpaceCompIsoEquiv p.inclusion e (p.rootDatum.root a))

@[simp] theorem mapGroupIso_inclusion :
    (p.mapGroupIso e).inclusion = p.inclusion ≫ e.hom := rfl

@[simp] theorem mapGroupIso_rootVector (a : p.base.support) :
    (p.mapGroupIso e).pinning.rootVector a =
      Lie.targetMapLinear e.hom (CommRingCat.of k) (p.pinning.rootVector a) := rfl

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The actual character spaces agree after the corresponding representation pullback. -/
theorem mapGroupIso_representationWeightSpace (ρ : MatrixRepresentation H I)
    (lam : characterLattice p.torus) :
    (p.mapGroupIso e).representationWeightSpace ρ lam =
      p.representationWeightSpace (ρ.restrict e.hom) lam := by
  let := p.isSplitTorus.isAffineHom
  change (ρ.restrict (p.inclusion ≫ e.hom)).characterSpace _ =
    ((ρ.restrict e.hom).restrict p.inclusion).characterSpace _
  rw [MatrixRepresentation.restrict_comp]
  rfl

/-- The representation transported by the inverse group isomorphism retains every weight space. -/
theorem mapGroupIso_representationWeightSpace_inverse (ρ : MatrixRepresentation G I)
    (lam : characterLattice p.torus) :
    (p.mapGroupIso e).representationWeightSpace (ρ.restrict e.inv) lam =
      p.representationWeightSpace ρ lam := by
  rw [mapGroupIso_representationWeightSpace, MatrixRepresentation.restrict_comp,
    e.hom_inv_id, MatrixRepresentation.restrict_id]

variable {p e}

/-- An actual highest-weight representation transports with the actual pinning. -/
theorem IsHighestWeight.mapGroupIso {ρ : MatrixRepresentation G I}
    {lam : characterLattice p.torus} (hρ : p.IsHighestWeight ρ lam) (e : G ≅ H) :
    (p.mapGroupIso e).IsHighestWeight (ρ.restrict e.inv) lam := by
  refine ⟨hρ.1.restrict_iso e.symm,
    (p.mapGroupIso e).iSup_representationWeightSpace_eq_top _, ?_, ?_⟩
  · rw [mapGroupIso_representationWeightSpace_inverse]
    exact hρ.2.2.1
  · intro mu hmu
    rw [mapGroupIso_representationWeightSpace_inverse] at hmu
    exact hρ.2.2.2 mu hmu

end SplitPinning

end Langlands.GroupScheme
