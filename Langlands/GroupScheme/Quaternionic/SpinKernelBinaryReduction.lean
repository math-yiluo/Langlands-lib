import Langlands.GroupScheme.Quaternionic.SpinLeviLift
import Langlands.GroupScheme.Quaternionic.SpinLeviUniqueness
import Langlands.GroupScheme.Quaternionic.BinaryQuaternionSpinCoordinates

/-! # Affine kernel generation from the binary spin subgroup -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite Langlands.CentralSimple
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- Square roots of one transported from an affine coefficient algebra to its sections. -/
def affineRootCoordinates (A : CommAlgCat.{u} (CommRingCat.of K)) :
    rootsOfUnity 2 A ≃* rootsOfUnity 2
      (BinaryScheme.coefficients ((algSpec (CommRingCat.of K)).obj (op A))) :=
  (Corepresented.affineSectionsAlgEquiv A).symm.toMulEquiv.restrictRootsOfUnity 2

@[simp] theorem affineRootCoordinates_val (A : CommAlgCat.{u} (CommRingCat.of K))
    (u : rootsOfUnity 2 A) :
    (affineRootCoordinates A u).val =
      Units.map (Corepresented.affineSectionsIso A).inv.hom.toRingHom.toMonoidHom u.val := by
  apply Units.ext
  rfl

/-- The all-test norm-one coordinates of an affine norm-one point. -/
theorem normOnePointsEquiv_normOnePoint (A : CommAlgCat.{u} (CommRingCat.of K))
    (b : reducedNormOne K D A) :
    CentralSimpleUnits.normOnePointsEquiv K D
        ((algSpec (CommRingCat.of K)).obj (op A)) (normOnePoint A b) =
      normOneMap (Corepresented.affineSectionsIso A).inv b := by
  apply Subtype.ext
  rw [CentralSimpleUnits.normOnePointsEquiv_val, LeviScheme.pointsEquiv_affine,
    normOnePoint_comp_normOneι]
  simp only [unitPoint, MulEquiv.apply_symm_apply, normOneMap_val]

/-- Scalar norm-one coordinates commute with the affine section comparison. -/
theorem rootScalarNormOne_affineRootCoordinates (hdim : Module.finrank K D = 4)
    (A : CommAlgCat.{u} (CommRingCat.of K)) (u : rootsOfUnity 2 A) :
    BinaryKernel.rootScalarNormOne hdim _ (affineRootCoordinates A u) =
      normOneMap (Corepresented.affineSectionsIso A).inv
        (scalarNormOne (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim) A u) := by
  apply Subtype.ext
  rw [BinaryKernel.rootScalarNormOne_val, normOneMap_val, scalarNormOne_val,
    normCoverScalarUnits_map, affineRootCoordinates_val]

variable [Infinite K] (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {e f : n → D} (h : σ.IsHyperbolicPair q e f)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}
  (hπ : σ.IsSpinCover q π)
  (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})

/-- On an affine test, the diagonal binary spin point is the original kernel point. -/
theorem diagonalSpin_affineRoot_points
    (A : CommAlgCat.{u} (CommRingCat.of K)) (u : rootsOfUnity 2 A) :
    ((BinaryKernel.rootsPointsEquiv ((algSpec (CommRingCat.of K)).obj (op A))).symm
        (affineRootCoordinates A u)) ≫
        (BinarySpinLift.diagonalSpin σ hdim hsym h hπ hsc).hom.hom =
      kernelPoint (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim)
        (BinarySpinLift.scalar σ hdim hsym h hπ hsc)
        (BinarySpinLift.normOne σ hdim hsym h hπ hsc) A u := by
  rw [BinarySpinLift.diagonalSpin_root_points]
  have hg : (Gm.pointsEquiv (Spec (CommRingCat.of K))
      ((algSpec (CommRingCat.of K)).obj (op A))).symm (affineRootCoordinates A u).val =
      gmPoint A u.val := by
    apply (Gm.pointsEquiv (Spec (CommRingCat.of K)) _).injective
    rw [MulEquiv.apply_symm_apply, gm_pointsEquiv_gmPoint, affineRootCoordinates_val]
  have hn : (CentralSimpleUnits.normOnePointsEquiv K D
      ((algSpec (CommRingCat.of K)).obj (op A))).symm
        (BinaryKernel.rootScalarNormOne hdim _ (affineRootCoordinates A u)) =
      normOnePoint A
        (scalarNormOne (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim) A u) := by
    apply (CentralSimpleUnits.normOnePointsEquiv K D _).injective
    rw [MulEquiv.apply_symm_apply, normOnePointsEquiv_normOnePoint,
      rootScalarNormOne_affineRootCoordinates]
  rw [hg, hn]
  rfl

/-- Binary diagonal monomorphy and kernel coverage imply the coefficient-algebra
kernel-generation condition for the constructed binary lifts. -/
theorem kernelGenerator_binary
    (hm : Mono (BinarySpinLift.diagonalSpin σ hdim hsym h hπ hsc).hom.hom)
    (hcover : SubgroupFunctor.range (kernelι π) ≤
      SubgroupFunctor.range (BinarySpinLift.productHom σ hdim hsym h hπ hsc)) :
    KernelGenerator (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim) π
      (BinarySpinLift.scalar σ hdim hsym h hπ hsc)
      (BinarySpinLift.normOne σ hdim hsym h hπ hsc) := by
  intro A k hk
  obtain ⟨v, hv, huniq⟩ := BinarySpinLift.existsUnique_root_of_kernel
    σ hdim hsym h hπ hsc hm hcover ((algSpec (CommRingCat.of K)).obj (op A)) k hk
  refine ⟨(affineRootCoordinates A).symm v, ?_, ?_⟩
  · dsimp only
    rw [← diagonalSpin_affineRoot_points, MulEquiv.apply_symm_apply]
    exact hv
  · intro u hu
    apply (affineRootCoordinates A).injective
    rw [MulEquiv.apply_symm_apply]
    apply huniq
    rw [diagonalSpin_affineRoot_points]
    exact hu

/-- The same geometric conditions imply kernel generation for every Levi lift pair. -/
theorem kernelGenerator_of_binary
    (hm : Mono (BinarySpinLift.diagonalSpin σ hdim hsym h hπ hsc).hom.hom)
    (hcover : SubgroupFunctor.range (kernelι π) ≤
      SubgroupFunctor.range (BinarySpinLift.productHom σ hdim hsym h hπ hsc))
    {mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S}
    {psi : CentralSimpleUnits.normOne K D ⟶ S}
    (hl : IsLeviLift h π mu psi) :
    KernelGenerator (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim) π mu psi := by
  obtain ⟨rfl, rfl⟩ := hl.unique (isLeviLift_binarySpinLift σ hdim hsym h hπ hsc) hπ
    (hsc K D hdim).isSemisimple.isConnectedReductive
  exact kernelGenerator_binary σ hdim hsym h hπ hsc hm hcover

end Langlands.GroupScheme.Quaternionic.SpinKernel
