import Langlands.GroupScheme.Reductive.RootComponentCommutation
import Langlands.GroupScheme.Reductive.RootPartitionFiniteProduct

/-! # Actual field products indexed by integral Cartan components -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RootComponentCoordinates
open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

variable {M : AffinePinnedModel.{u}} (D : RootComponentCoordinates M)
    (k : Type u) [Field k] [Algebra M.ring k]

private local instance : Smooth M.group.X.hom := M.reductive.smooth
local instance : IsAffineHom M.group.X.hom := M.reductive.isAffineHom

private local instance : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap M.ring k)).obj M.group).X.hom :=
  (M.reductive.isConnectedReductive_algebraMap k).isAffineHom

omit [Algebra M.ring k] in
/-- Distinct integral Cartan components have disjoint actual field root sets. -/
theorem componentRoots_pairwise_disjoint :
    Pairwise fun c d : Component M.basis => Disjoint (D.componentRoots k c) (D.componentRoots k d) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  rintro α ⟨r, hr, her⟩ ⟨q, hq, heq⟩
  have hroot : M.rootDatum.root r = M.rootDatum.root q := by
    apply (splitTorus.characterLatticeEquiv k M.coordinates).symm.injective
    simpa only [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm] using
      her.trans heq.symm
  have hrq : r = q := M.rootDatum.root.injective hroot
  exact hcd (hr.symm.trans ((congrArg D.rootComponent hrq).trans hq))

variable [IsAlgClosed k]
    (N : ∀ c : Component M.basis, RootPartitionNormalModel
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
      (D.fieldTorusInclusion k) (D.componentRoots k c))

/-- The supplied component models form the actual simply connected field group. -/
def componentNormalProductIso_of_isSimplyConnected
    (hG : IsSimplyConnected ((GroupScheme.baseChange (algebraBaseMap M.ring k)).obj M.group)) :
    GroupScheme.pi (fun c : Component M.basis => (N c).group) ≅ (GroupScheme.baseChange (algebraBaseMap M.ring k)).obj M.group := by
  have hmax := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
    M.coordinates M.group M.inclusion M.maximal k
  exact RootPartitionFamily.simplyConnectedIso
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
    (D.fieldTorusInclusion k)
    (D.componentRoots k) N (D.componentRoots_pairwise_disjoint k) hG
    ⟨isSplitTorus_splitTorus M.coordinates, hmax.2.1⟩ hmax
    (fun _ hα => D.exists_mem_componentRoots k hα)

/-- The supplied component models form the actual adjoint field group. -/
def componentNormalProductIso_of_isAdjoint
    (hG : IsAdjoint ((GroupScheme.baseChange (algebraBaseMap M.ring k)).obj M.group)) :
    GroupScheme.pi (fun c : Component M.basis => (N c).group) ≅ (GroupScheme.baseChange (algebraBaseMap M.ring k)).obj M.group := by
  have hmax := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
    M.coordinates M.group M.inclusion M.maximal k
  exact RootPartitionFamily.adjointIso
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
    (D.fieldTorusInclusion k)
    (D.componentRoots k) N (D.componentRoots_pairwise_disjoint k) hG.isSemisimple hG.center_eq_bot
    ⟨isSplitTorus_splitTorus M.coordinates, hmax.2.1⟩ hmax
    (fun _ hα => D.exists_mem_componentRoots k hα)

/-- The simply connected comparison is compatible with the actual model inclusions. -/
@[reassoc (attr := simp)] theorem inclusion_componentNormalProductIso_of_isSimplyConnected
    (hG : IsSimplyConnected ((GroupScheme.baseChange (algebraBaseMap M.ring k)).obj M.group))
    (c : Component M.basis) :
    piFactorInclusionHom (fun c : Component M.basis => (N c).group) c ≫
      (D.componentNormalProductIso_of_isSimplyConnected k N hG).hom = (N c).inclusion :=
  RootPartitionFamily.inclusion_multiplication
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
    (D.fieldTorusInclusion k) (D.componentRoots k) N
    (D.componentRoots_pairwise_disjoint k) c

/-- The adjoint comparison is compatible with the actual model inclusions. -/
@[reassoc (attr := simp)] theorem inclusion_componentNormalProductIso_of_isAdjoint
    (hG : IsAdjoint ((GroupScheme.baseChange (algebraBaseMap M.ring k)).obj M.group))
    (c : Component M.basis) :
    piFactorInclusionHom (fun c : Component M.basis => (N c).group) c ≫
      (D.componentNormalProductIso_of_isAdjoint k N hG).hom = (N c).inclusion :=
  RootPartitionFamily.inclusion_multiplication
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
    (D.fieldTorusInclusion k) (D.componentRoots k) N
    (D.componentRoots_pairwise_disjoint k) c

end Langlands.GroupScheme.RootComponentCoordinates
