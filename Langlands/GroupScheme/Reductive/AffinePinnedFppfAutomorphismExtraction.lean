import Langlands.GroupScheme.Reductive.AffinePinnedAutomorphismExtraction
import Langlands.GroupScheme.Reductive.AffinePinnedAutomorphismLocalPinning
import Langlands.GroupScheme.Reductive.AffinePinnedFppfCoefficientRigidity

/-! # Exact affine pinning from fppf-local pinning and global coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace splitTorus

/-- The coordinate split-torus comparison along the identity is the canonical
actual identity-pullback isomorphism. -/
theorem baseChangeIso_id (S : Scheme.{u}) (I : Type u) [Finite I] :
    baseChangeIso (𝟙 S) I = baseChangeIdIso (splitTorus S I) := by
  apply Iso.ext
  apply hom_ext_points
  intro U x
  apply (pointsEquiv I U).injective
  rw [pointsEquiv_baseChangeIso_hom]
  have h := congrArg (pointsEquiv I U)
    (GroupScheme.baseChangePointsEquiv_id (splitTorus S I) U x)
  rw [pointsEquiv_naturality] at h
  funext j
  simpa [baseChangePointsEquiv, unitsRestrict] using congrFun h j

end splitTorus

namespace AffinePinnedModel

variable (M : AffinePinnedModel.{u})

/-- Normalized coordinate inclusion along the identity recovers the original
actual inclusion through the canonical identity-pullback comparison. -/
theorem inclusionOver_id_comp :
    M.inclusionOver (𝟙 M.base) ≫ (baseChangeIdIso M.group).hom = M.inclusion := by
  have hn := ((Functor.mapGrpNatIso Over.pullbackId) ≪≫
    Functor.mapGrpIdIso).hom.naturality M.inclusion
  change (baseChange (𝟙 M.base)).map M.inclusion ≫ (baseChangeIdIso M.group).hom =
    (baseChangeIdIso (splitTorus M.base M.coordinates)).hom ≫ M.inclusion at hn
  rw [← splitTorus.baseChangeIso_id M.base M.coordinates] at hn
  change (splitTorus.baseChangeIso (𝟙 M.base) M.coordinates).inv ≫
    (baseChange (𝟙 M.base)).map M.inclusion ≫ (baseChangeIdIso M.group).hom = _
  rw [hn, Iso.inv_hom_id_assoc]

/-- A supplied actual normalized identity-pullback coordinate alignment gives
coordinate alignment for the original ambient automorphism. -/
def originalCoordinateIso
    (σ : CategoryTheory.Aut M.group)
    (d : BasedCoordinateIso (M.inclusionOver (𝟙 M.base)) (M.inclusionOver (𝟙 M.base))
      M.rootDatum M.rootDatum M.basis M.basis)
    (hd : d.groupIso = (baseChange (𝟙 M.base)).mapIso σ.asIso) :
    BasedCoordinateIso M.inclusion M.inclusion
      M.rootDatum M.rootDatum M.basis M.basis where
  groupIso := σ.asIso
  torusIso := d.torusIso
  rootEquiv := d.rootEquiv
  sourcePairing := d.sourcePairing
  targetPairing := d.targetPairing
  simple_iff := d.simple_iff
  characters := d.characters
  square := by
    have hn := ((Functor.mapGrpNatIso Over.pullbackId) ≪≫
      Functor.mapGrpIdIso).hom.naturality σ.asIso.hom
    change (baseChange (𝟙 M.base)).map σ.asIso.hom ≫ (baseChangeIdIso M.group).hom =
      (baseChangeIdIso M.group).hom ≫ σ.asIso.hom at hn
    have hs := d.square
    rw [hd] at hs
    simp only [Functor.mapIso_hom] at hs
    calc
      M.inclusion ≫ σ.asIso.hom =
          M.inclusionOver (𝟙 M.base) ≫ (baseChangeIdIso M.group).hom ≫ σ.asIso.hom := by
        rw [← Category.assoc, M.inclusionOver_id_comp]
      _ = M.inclusionOver (𝟙 M.base) ≫
          (baseChange (𝟙 M.base)).map σ.asIso.hom ≫ (baseChangeIdIso M.group).hom := by rw [hn]
      _ = d.torusIso.hom ≫ M.inclusion := by
        rw [← Category.assoc, hs, Category.assoc, M.inclusionOver_id_comp]

/-- A single full based coordinate alignment turns fppf-local concrete
pinning into the exact affine target predicate. -/
theorem isPinnedAutomorphism_of_basedCoordinateIso_of_fppfLocalPinning
    (d : BasedCoordinateIso M.inclusion M.inclusion
      M.rootDatum M.rootDatum M.basis M.basis)
    (hpin : IsFppfLocallyPinned ((baseChange (𝟙 M.base)).mapIso d.groupIso)) :
    M.IsPinnedAutomorphism (Aut.of d.groupIso) d.rootEquiv⁻¹ := by
  classical
  have hr : d.rootEquiv ∈ M.basedAutomorphisms := d.simple_iff
  have hθ : d.rootEquiv⁻¹ ∈ M.basedAutomorphisms :=
    M.basedAutomorphisms.inv_mem hr
  let p : M.basis.support ≃ M.basis.support :=
    (d.rootEquiv⁻¹).indexEquiv.subtypeEquiv hθ
  have hX (s : M.basis.support) :
      Lie.targetMapLinear d.groupIso.hom (CommRingCat.of M.ring) (M.pinning s 1).val =
        (M.pinning (p s) 1).val := by
    let τ : splitTorus.commGroupScheme M.base M.coordinates ≅
        splitTorus.commGroupScheme M.base M.coordinates :=
      CommGroupScheme.isoOfGroupIso d.torusIso
    have hroot : d.rootEquiv.weightMap (M.rootDatum.root (p s)) = M.rootDatum.root s := by
      rw [RootPairing.Hom.root_weightMap_apply]
      change M.rootDatum.root
        (d.rootEquiv.indexEquiv (d.rootEquiv.indexEquiv.symm s)) = M.rootDatum.root s
      rw [Equiv.apply_symm_apply]
    have hc := d.exponentCharacter_comp (M.rootDatum.root (p s))
    rw [hroot] at hc
    have hχ : characterLattice.congr τ
        (splitTorus.exponentCharacter M.base M.coordinates (M.rootDatum.root s)) =
      splitTorus.exponentCharacter M.base M.coordinates (M.rootDatum.root (p s)) := by
      change τ.inv ≫ _ = _
      rw [← hc, ← Category.assoc]
      change (τ.inv ≫ τ.hom) ≫ _ = _
      rw [Iso.inv_hom_id, Category.id_comp]
    obtain ⟨c, hvec, _⟩ := splitTorus.existsUnique_unit_smul_of_aligned_weightLines
      τ d.groupIso d.square (M.rootDatum.root s) (M.rootDatum.root (p s)) hχ
      (M.pinning s) (M.pinning (p s))
    have hc1 := pinning_unit_eq_one_of_fppfLocalPinning (Aut.of d.groupIso) hpin hvec
    simpa only [hc1, Units.val_one, one_smul] using hvec
  exact M.isPinnedAutomorphism_of_basedCoordinateIso d
    (preservesLocalPinning_baseChange_of_vector_permutation (Aut.of d.groupIso) p hX (𝟙 M.base))

/-- Exact extraction is compatible with the actual identity-pullback models. -/
theorem isPinnedAutomorphism_of_identityCoordinateIso_of_fppfLocalPinning
    (σ : CategoryTheory.Aut M.group)
    (d : BasedCoordinateIso (M.inclusionOver (𝟙 M.base)) (M.inclusionOver (𝟙 M.base))
      M.rootDatum M.rootDatum M.basis M.basis)
    (hd : d.groupIso = (baseChange (𝟙 M.base)).mapIso σ.asIso)
    (hpin : IsFppfLocallyPinned ((baseChange (𝟙 M.base)).mapIso σ.asIso)) :
    M.IsPinnedAutomorphism σ d.rootEquiv⁻¹ :=
  M.isPinnedAutomorphism_of_basedCoordinateIso_of_fppfLocalPinning
    (M.originalCoordinateIso σ d hd) hpin

end AffinePinnedModel

end Langlands.GroupScheme
