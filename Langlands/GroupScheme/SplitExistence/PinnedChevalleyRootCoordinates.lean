import Langlands.GroupScheme.SplitExistence.PinnedChevalleyModel
import Langlands.GroupScheme.SplitExistence.OppositeFactorPairs
import Langlands.GroupScheme.Rational.SteinbergRootMapUniqueness

/-! # Chevalley root coordinates on a supplied split pinning -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.SplitExistence.ChevalleyData

namespace Langlands.GroupScheme.SplitPinning

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (p : SplitPinning G)
    {D : SplitExistence.ChevalleyData p.rootDatum p.base} (M : D.ChevGroup k)

local instance : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom :=
  VectorGroup.isAffineHom_groupScheme (CommRingCat.of k) 1

local instance : Module.Finite ℤ (characterLattice p.torus) :=
  (TorusSurjectionIsogenySection.characterLattice_free_finite p.isSplitTorus).2

local instance : Module.Free ℤ (characterLattice p.torus) :=
  (TorusSurjectionIsogenySection.characterLattice_free_finite p.isSplitTorus).1

local instance : p.rootDatum.IsReduced := p.isReduced
local instance : IsAffineHom M.H.X.hom := M.affine
local instance : IsAffine M.H.X.left := isAffine_of_isAffineHom M.H.X.hom
local instance : Smooth M.H.X.hom := M.smooth

private theorem chevalleyRoot_represents (a : p.rootIndex) :
    (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).IsRepresentedBy
      (M.u a ≫ (p.chevalleyIso M).groupIso.hom) := by
  let f := p.chevalleyIso M
  have hroot : characterLattice.congr f.torusIso.symm (p.rootDatum.root a) =
      charOf k (p.rootDatum.root a) := by
    let e := characterLattice.congr f.torusIso
    change e.symm (p.rootDatum.root a) = charOf k (p.rootDatum.root a)
    calc
      _ = e.symm (e (charOf k (p.rootDatum.root a))) :=
        congrArg e.symm (p.chevalleyIso_root M a).symm
      _ = _ := e.symm_apply_apply _
  have h := RelativeRoot.subgroup_comap_of_transport f.torusIso.symm f.groupIso.symm
    (RelativeRoot.inverse_transport_square f.torusIso f.groupIso (p.chevalleyIso_square M))
    (p.rootDatum.root a)
  rw [hroot, Iso.symm_hom] at h
  rw [← h]
  exact (M.represents_root a).comp_iso f.groupIso

private theorem chevalleyRoot_torus_equivariant (a : p.rootIndex) :
    VectorGroup.IsTorusEquivariant p.inclusion
      (M.u a ≫ (p.chevalleyIso M).groupIso.hom) (p.rootDatum.root a) := by
  intro Z t c
  let f := p.chevalleyIso M
  let m := t ≫ (CommGroupScheme.groupHom f.torusIso.inv).hom.hom
  have hsq := RelativeRoot.inverse_transport_square f.torusIso f.groupIso
    (p.chevalleyIso_square M)
  have ht : m ≫ M.t.hom.hom = (t ≫ p.inclusion.hom.hom) ≫ f.groupIso.inv.hom.hom := by
    simp only [m, Category.assoc, ← Grp.comp_hom_hom, hsq]
  have ht' : (m ≫ M.t.hom.hom) ≫ f.groupIso.hom.hom.hom = t ≫ p.inclusion.hom.hom := by
    rw [ht, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id]
  have hroot : f.torusIso.inv ≫ charOf k (p.rootDatum.root a) = p.rootDatum.root a :=
    p.chevalleyIso_root M a
  have hχ : VectorGroup.charValue (charOf k (p.rootDatum.root a)) Z m =
      VectorGroup.charValue (p.rootDatum.root a) Z t := by
    simp only [m, VectorGroup.charValue, ← comp_groupHom_comp, hroot]
  have h := congrArg (fun g : Z ⟶ M.H.X => g ≫ f.groupIso.hom.hom.hom)
    (M.u_isTorusEquivariant a Z m c)
  simp only [MonObj.mul_comp, GrpObj.inv_comp, ht', hχ] at h
  simpa only [Grp.comp_hom_hom, Category.assoc] using h

/-- Transport the raw additive root map of a fixed Chevalley model to the whole
intrinsic root subgroup of the supplied pinning. -/
def chevalleyRootParametrization (a : p.rootIndex) : p.RootParametrization a where
  hom := M.u a ≫ (p.chevalleyIso M).groupIso.hom
  represents := p.chevalleyRoot_represents M a
  isClosedSubgroup := by
    let : Smooth (Gak k).X.hom := (gak_geometry k).1
    let : ConnectedSpace (Gak k).X.left := (gak_geometry k).2.2
    exact (HomImage.isClosedSubgroup_of_mono (M.u a)).comp_iso (p.chevalleyIso M).groupIso
  torus_equivariant := p.chevalleyRoot_torus_equivariant M a

/-- The field coordinates on the rational points of the full intrinsic root subgroup. -/
def chevalleyRootCoordEquiv (a : p.rootIndex) :
    Multiplicative k ≃*
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
  (gaRationalEquiv k).trans ((p.chevalleyRootParametrization M a).represents.pointsEquiv _)

/-- The point with parameter `s` is the image of the raw Chevalley point with the same
root index and parameter. -/
theorem chevalleyRootCoordEquiv_apply (a : p.rootIndex) (s : k) :
    (p.chevalleyRootCoordEquiv M a (Multiplicative.ofAdd s) : rationalPoints G) =
      rationalPoints.map (p.chevalleyIso M).groupIso.hom (M.rootPt a s) := by
  change gaRationalEquiv k (Multiplicative.ofAdd s) ≫
      (M.u a ≫ (p.chevalleyIso M).groupIso.hom).hom.hom =
    (gaRationalEquiv k (Multiplicative.ofAdd s) ≫ (M.u a).hom.hom) ≫
      (p.chevalleyIso M).groupIso.hom.hom.hom
  rw [Grp.comp_hom_hom, Category.assoc]

/-- Evaluation by the root parametrization agrees with the field coordinate equivalence. -/
theorem chevalleyRootParametrization_rationalPoint (a : p.rootIndex) (s : k) :
    (p.chevalleyRootParametrization M a).rationalPoint s =
      (p.chevalleyRootCoordEquiv M a (Multiplicative.ofAdd s) : rationalPoints G) := by
  change VectorGroup.scalarPoint (CommRingCat.of k) _ ((Scheme.ΓSpecIso _).inv s) ≫
      (p.chevalleyRootParametrization M a).hom.hom.hom =
    gaRationalEquiv k (Multiplicative.ofAdd s) ≫ (p.chevalleyRootParametrization M a).hom.hom.hom
  have h := gaCoord_gaRationalEquiv k (Multiplicative.ofAdd s)
  change (VectorGroup.coordinates (CommRingCat.of k) 1 _
    (gaRationalEquiv k (Multiplicative.ofAdd s))).toAdd 0 = (Scheme.ΓSpecIso _).inv s at h
  rw [← h, VectorGroup.scalarPoint_coordinate]

/-- The transported differential at the standard epsilon vector is the
given simple Lie vector. -/
theorem chevalleyRootParametrization_derivative (a : p.base.support) :
    Lie.targetMapLinear (p.chevalleyRootParametrization M a.val).hom (CommRingCat.of k)
      (VectorGroup.standardEpsilon k) = p.pinning.rootVector a := by
  let b : (p.chevalleyPinning M).base.support :=
    ⟨a.val, (p.chevalleyPinning_simple_iff M a.val).2 a.property⟩
  let f := p.chevalleyIso M
  change Lie.targetMapLinear (M.u b.val ≫ f.groupIso.hom) k
    (VectorGroup.standardEpsilon k) = _
  rw [Lie.targetMapLinear_comp, LinearMap.comp_apply, ← p.chevalleyPinning_rootVector M b]
  have hab : (⟨f.indexEquiv b.val, (f.simple_iff b.val).mp b.property⟩ : p.base.support) = a :=
    Subtype.ext (p.chevalleyIso_index M a.val)
  have h := f.rootVector_eq b
  rwa [hab] at h

/-- On each simple root the transported Chevalley map gives normalized
coordinates for the supplied pinning. -/
def chevalleyNormalizedRootParametrization (a : p.base.support) :
    p.NormalizedRootParametrization a where
  hom := (p.chevalleyRootParametrization M a.val).hom
  represents := (p.chevalleyRootParametrization M a.val).represents
  isClosedSubgroup := (p.chevalleyRootParametrization M a.val).isClosedSubgroup
  torus_equivariant := (p.chevalleyRootParametrization M a.val).torus_equivariant
  derivative := p.chevalleyRootParametrization_derivative M a

/-- Uniqueness identifies the transported simple-root morphism with the homomorphism
of any normalized parametrization of that root. -/
theorem chevalleyRootParametrization_eq_normalized (a : p.base.support)
    (x : p.NormalizedRootParametrization a) :
    (p.chevalleyRootParametrization M a.val).hom = x.hom :=
  NormalizedRootParametrization.hom_eq (p.chevalleyNormalizedRootParametrization M a) x

end Langlands.GroupScheme.SplitPinning
