import Langlands.GroupScheme.Quaternionic.SpinKernelSplitReduction
import Langlands.GroupScheme.OrthogonalMatrix.CentralCoverKernel
import Langlands.GroupScheme.IdentityComponent.Transport
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.CentralIsogeny.Transport
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof

/-! # Reduction of the quaternionic kernel comparison to split orthogonal coordinates -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

section IdentityTransport

variable {K L : Type u} [Field K] [Field L]
  (H : GroupScheme (Spec (CommRingCat.of K)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]
  (φ : K →+* L) {l : Type} [Fintype l] [DecidableEq l]
  (Φ : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).obj H ≅
    OrthogonalMatrix.groupScheme l (CommRingCat.of L))

/-- The original identity component after base change in the supplied full
orthogonal coordinates. -/
def orthogonalIdentityComponentIso :
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).obj (identityComponent H) ≅
      identityComponent (OrthogonalMatrix.groupScheme l (CommRingCat.of L)) :=
  IdentityComponent.baseChangeIso H φ ≪≫ IdentityComponent.mapIso Φ

@[reassoc (attr := simp)]
theorem orthogonalIdentityComponentIso_hom_comp :
    (orthogonalIdentityComponentIso H φ Φ).hom ≫
        identityComponentι (OrthogonalMatrix.groupScheme l (CommRingCat.of L)) =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).map (identityComponentι H) ≫
        Φ.hom := by
  simp only [orthogonalIdentityComponentIso, Iso.trans_hom, Category.assoc,
    IdentityComponent.mapIso_hom_identityComponentι,
    IdentityComponent.baseChangeIso_hom_identityComponentι_assoc]

end IdentityTransport

section OrthogonalKernel

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  [Smooth H.X.hom] [IsAffineHom H.X.hom]
  (hG : IsSimplyConnected G)
  {p : G ⟶ identityComponent H} (hp : IsCentralIsogeny p)
  {f : G ⟶ H} (hf : p ≫ identityComponentι H = f)
  {l : Type} [Fintype l] [DecidableEq l] (hl : 3 ≤ Fintype.card l)
  (Φ : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj H ≅
    OrthogonalMatrix.groupScheme l (CommRingCat.of L))
  (a : (Gm (Spec (CommRingCat.of L))).toGrp ⟶
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj G)
  (ν : cocharacterLattice
    (splitTorus.commGroupScheme (Spec (CommRingCat.of L)) (ULift l)))
  (ha : a ≫ (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f ≫ Φ.hom =
    CommGroupScheme.groupHom ν ≫ OrthogonalMatrix.diagonalTorus l (CommRingCat.of L))
  (i₀ : l) (hν : GeneralLinear.cocharacterCoordEquiv l L ν = Pi.single i₀ 2)

include hG hp hf hl ha hν

/-- A lifted coordinate `2e_i` in full orthogonal coordinates gives a unique
square-root parameter for every point of the original cover kernel after base change. -/
theorem existsUnique_kernel_of_orthogonalCoordinates
    {U : Over (Spec (CommRingCat.of L))}
    (x : U ⟶ ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj G).X)
    (hx : x ≫ ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f).hom.hom = 1) :
    ∃! z : {z : U ⟶ (Gm (Spec (CommRingCat.of L))).X // z * z = 1},
      z.val ≫ a.hom.hom = x := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let F := GroupScheme.baseChange b
  let e := orthogonalIdentityComponentIso H (algebraMap K L) Φ
  let pL := F.map p ≫ e.hom
  have hpL : IsCentralIsogeny pL := (hp.baseChange b).comp_iso e
  have hGL : IsSimplyConnected (F.obj G) := isSimplyConnectedFieldExtension K L G hG
  have hpLi : pL ≫ identityComponentι (OrthogonalMatrix.groupScheme l (CommRingCat.of L)) =
      F.map f ≫ Φ.hom := by
    dsimp only [pL, e]
    rw [Category.assoc, orthogonalIdentityComponentIso_hom_comp, ← Category.assoc,
      ← F.map_comp, hf]
  have haL : a ≫ pL = CommGroupScheme.groupHom ν ≫ OrthogonalMatrix.identityTorus l L := by
    apply IdentityComponent.hom_ext_of_isOpenImmersion
      (identityComponentι (OrthogonalMatrix.groupScheme l (CommRingCat.of L)))
    rw [Category.assoc, hpLi, Category.assoc, OrthogonalMatrix.identityTorus_comp]
    exact ha
  have hxL : x ≫ pL.hom.hom = 1 := by
    apply (cancel_mono
      (identityComponentι (OrthogonalMatrix.groupScheme l (CommRingCat.of L))).hom.hom).mp
    rw [Category.assoc, ← Grp.comp_hom_hom, hpLi, Grp.comp_hom_hom,
      ← Category.assoc, hx, MonObj.one_comp, MonObj.one_comp]
  obtain ⟨z, hz, huniq⟩ := OrthogonalMatrix.existsUnique_kernel_lift_comp_eq
    hpL hGL hl a ν haL i₀ hν x hxL
  refine ⟨⟨z, hz.1⟩, hz.2, ?_⟩
  intro w hw
  exact Subtype.ext (huniq w.val ⟨w.2, hw⟩)

end OrthogonalKernel

section SpinKernel

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] [Infinite K]
  [Field L] [Algebra K L]
  (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {e f : n → D} (h : σ.IsHyperbolicPair q e f)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}
  (hπ : σ.IsSpinCover q π)
  (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})
  {l : Type} [Fintype l] [DecidableEq l] (hl : 3 ≤ Fintype.card l)
  (Φ : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj
      (σ.isometryGroup q) ≅ OrthogonalMatrix.groupScheme l (CommRingCat.of L))
  (a : (Gm (Spec (CommRingCat.of L))).toGrp ⟶
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj S)
  (ν : cocharacterLattice
    (splitTorus.commGroupScheme (Spec (CommRingCat.of L)) (ULift l)))
  (ha : a ≫ (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map π ≫ Φ.hom =
    CommGroupScheme.groupHom ν ≫ OrthogonalMatrix.diagonalTorus l (CommRingCat.of L))
  (i₀ : l) (hν : GeneralLinear.cocharacterCoordEquiv l L ν = Pi.single i₀ 2)
  (hc : ∀ (U : Over (Spec (CommRingCat.of L)))
    (z : {z : U ⟶ (Gm (Spec (CommRingCat.of L))).X // z * z = 1}),
    baseChangePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap K L))) S U
        (z.val ≫ a.hom.hom) =
      binaryRootPointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap K L))) U z ≫
        (BinarySpinLift.diagonalSpin σ hdim hsym h hπ hsc).hom.hom)

include hl ha hν hc

/-- Supplied full orthogonal coordinates and their comparison with the original
binary diagonal imply kernel generation for every Levi lift pair. -/
theorem kernelGenerator_of_orthogonalCoordinates
    {mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S}
    {psi : CentralSimpleUnits.normOne K D ⟶ S}
    (hlift : IsLeviLift h π mu psi) :
    KernelGenerator (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim)
      π mu psi := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let := hπ.smooth
  obtain ⟨p, hp, hpπ⟩ := hπ.exists_centralIsogeny
  have : IsIso ((GroupScheme.baseChange b).map
      (BinarySpinLift.diagonalKernel σ hdim hsym h hπ hsc)) := by
    apply isIso_baseChange_diagonalKernel_of_squareRootParametrization
      σ hdim hsym h hπ hsc b a
    · intro U x hx
      exact existsUnique_kernel_of_orthogonalCoordinates hπ.isSimplyConnected hp hpπ
        hl Φ a ν ha i₀ hν x hx
    · exact hc
  exact kernelGenerator_of_isIso_diagonalKernel_fieldExtension
    σ hdim hsym h hπ hsc L hlift

end SpinKernel

end Langlands.GroupScheme.Quaternionic.SpinKernel
