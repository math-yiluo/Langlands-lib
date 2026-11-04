import Langlands.GroupScheme.AutomorphicAction.SemidirectComplement
import Langlands.GroupScheme.Absolute.SolvableMaximalTorusSemidirectStatement
import Langlands.GroupScheme.Rational.SemigroupSubgroupFactorization
import Langlands.GroupScheme.Rational.SemigroupFieldReduction
import Langlands.GroupScheme.Rational.UnipotentSemigroupProduct
import Langlands.GroupScheme.Rational.SemigroupFunctorialityProof
import Langlands.GroupScheme.Rational.SemigroupSmoothQuotientProof

/-! # Action-compatible solvable factorization and exact semigroup reduction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace AutomorphicAction

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (a : AutomorphicAction S.toGrp G)

/-- Actual smooth connected factors of the original group, with unipotent
normal factor stable under the action and a torus fixed pointwise by it. -/
structure FixedTorusUnipotentFactorization where
  normalFactor : GroupScheme (Spec (CommRingCat.of k))
  torusFactor : CommGroupScheme (Spec (CommRingCat.of k))
  normalInclusion : normalFactor ⟶ G
  torusInclusion : torusFactor.toGrp ⟶ G
  normal_closed : IsClosedSubgroup normalInclusion
  normal_affine : IsAffineHom normalFactor.X.hom
  normal_smooth : Smooth normalFactor.X.hom
  normal_connected : ConnectedSpace normalFactor.X.left
  normal_unipotent : IsUnipotent normalFactor
  normal_normal : (SubgroupFunctor.range normalInclusion).IsNormal
  normal_stable : a.IsStable (SubgroupFunctor.range normalInclusion)
  torus_closed : IsClosedSubgroup torusInclusion
  torus_affine : IsAffineHom torusFactor.X.hom
  torus_isTorus : IsTorus torusFactor.toGrp
  torus_smooth : Smooth torusFactor.X.hom
  torus_connected : ConnectedSpace torusFactor.X.left
  torus_fixed : ∀ (V : Over (Spec (CommRingCat.of k))) (s : V ⟶ S.X)
    (t : V ⟶ torusFactor.X),
    a.act s (t ≫ torusInclusion.hom.hom) = t ≫ torusInclusion.hom.hom
  multiplication_isIso : IsIso (subgroupMultiplication normalInclusion torusInclusion)

variable [IsAffineHom G.X.hom] [IsAlgClosed k]

/-- Construct compatible factors from the structural maximal-torus
decomposition statement, applied only to the external semidirect product. -/
def solvableFactorization
    (hdecomp : SolvableMaximalTorusSemidirectStatement.{u})
    (hS : IsSplitTorus S.toGrp) (hG : Smooth G.X.hom)
    (hConn : ConnectedSpace G.X.left) (hsolv : RelativeRoot.IsSolvableScheme G) :
    a.FixedTorusUnipotentFactorization :=
  Classical.choice (by
    let : IsAffineHom S.X.hom := hS.isAffineHom
    let : Smooth S.X.hom := hS.smooth
    let : Smooth G.X.hom := hG
    let : ConnectedSpace G.X.left := hConn
    let : ConnectedSpace S.X.left := hS.connectedSpace
    let : GeometricallyConnected G.X.hom := G.geometricallyConnected_of_connected
    have hExtConn : ConnectedSpace a.semidirectProduct.X.left := by
      change ConnectedSpace (pullback G.X.hom S.X.hom : Scheme.{u})
      infer_instance
    let := hExtConn
    have hSsolv : RelativeRoot.IsSolvableScheme S.toGrp :=
      RelativeRoot.isSolvableScheme_of_isSolvableGroupScheme hS.smooth
        (isSolvableGroupScheme_of_isCommMonObj S.toGrp)
    have hExtSolv : IsSolvableGroupScheme a.semidirectProduct :=
      (RelativeRoot.isSolvableScheme_semidirect a hSsolv hsolv).isSolvableGroupScheme
    obtain ⟨M, j, f, hM, hf, hT, hTc, hTa, hTs, hTconn, hTfixed⟩ :=
      a.exists_maximalTorus_with_fixed_intersection hS hG
    obtain ⟨U, u, huc, hUs, hUconn, hU, huNormal, _, hprod⟩ :=
      hdecomp k a.semidirectProduct hExtSolv M j hM
    let : IsClosedImmersion u.hom.hom.left := huc
    let : Mono u.hom.hom := Over.mono_of_mono_left _
    let i := a.semidirectNormalSubgroup u hU hS
    have hi : i ≫ a.semidirectInl = u :=
      a.semidirectNormalSubgroup_comp u hU hS
    have hic : IsClosedSubgroup i := by
      change IsClosedImmersion i.hom.hom.left
      let : IsClosedImmersion a.semidirectInl.hom.hom.left :=
        a.isClosedSubgroup_semidirectInl
      have he : i.hom.hom.left ≫ a.semidirectInl.hom.hom.left = u.hom.hom.left :=
        congrArg (fun g => g.hom.hom.left) hi
      let : IsClosedImmersion (i.hom.hom.left ≫ a.semidirectInl.hom.hom.left) :=
        he.symm ▸ huc
      exact IsClosedImmersion.of_comp_isClosedImmersion
        i.hom.hom.left a.semidirectInl.hom.hom.left
    have hUa : IsAffineHom U.X.hom := by
      let : IsClosedImmersion i.hom.hom.left := hic
      rw [← i.hom.hom.w]
      infer_instance
    let := hprod
    exact ⟨{
      normalFactor := U
      torusFactor := a.semidirectTorusIntersection j
      normalInclusion := i
      torusInclusion := a.semidirectTorusIntersectionInclusion j
      normal_closed := hic
      normal_affine := hUa
      normal_smooth := hUs
      normal_connected := hUconn
      normal_unipotent := hU
      normal_normal := a.semidirectNormalFactor_isNormal u i hi huNormal
      normal_stable := a.semidirectNormalFactor_isStable u i hi huNormal
      torus_closed := hTc
      torus_affine := hTa
      torus_isTorus := hT
      torus_smooth := hTs
      torus_connected := hTconn
      torus_fixed := hTfixed
      multiplication_isIso := a.isIso_subgroupMultiplication_semidirectIntersection u i hi j }⟩)

end AutomorphicAction

namespace RelativeRoot

/-- The structural solvable decomposition and exact intersection comparison
reduce the full target to its algebraically closed unipotent core. -/
theorem semigroupSolvableReduction_of_maximalTorusDecomposition
    (hdecomp : SolvableMaximalTorusSemidirectStatement.{u})
    (hinter : SemigroupIntersectionStatement.{u}) :
    SemigroupSolvableReductionStatement.{u} := by
  intro hCore
  apply semigroupOrderedProduct_of_algebraicallyClosed
  intro k _ _ G hG hAff hConn hsolv S hS a
  let := hAff
  let F := a.solvableFactorization hdecomp hS hG hConn hsolv
  let : IsAffineHom F.normalFactor.X.hom := F.normal_affine
  let : Smooth F.normalFactor.X.hom := F.normal_smooth
  let : ConnectedSpace F.normalFactor.X.left := F.normal_connected
  let : IsAffineHom F.torusFactor.X.hom := F.torus_affine
  let : Smooth F.torusFactor.X.hom := F.torus_smooth
  let : ConnectedSpace F.torusFactor.X.left := F.torus_connected
  let : IsClosedImmersion F.normalInclusion.hom.hom.left := F.normal_closed
  let : Mono F.normalInclusion.hom.hom := Over.mono_of_mono_left _
  let := F.multiplication_isIso
  have hn : (SubgroupFunctor.range F.normalInclusion).IsNormalizedBy
      (SubgroupFunctor.range F.torusInclusion) := by
    intro V g x _ hx
    exact F.normal_normal V g x (Subgroup.mem_top _) hx
  apply hasOrderedSemigroupProducts_of_subgroup_factorization a
    F.normalInclusion F.torusInclusion hn F.normal_stable F.torus_fixed
    hS semigroupFunctoriality hinter
  exact hCore k F.normalFactor F.normal_smooth F.normal_affine
    F.normal_connected F.normal_unipotent S hS
    (a.onRepresentedSubgroup F.normalInclusion ⟨inferInstance, rfl⟩ F.normal_stable)

/-- With realization and smooth-quotient comparison discharged by published
proofs, three structural premises suffice for the exact full target. -/
theorem semigroupOrderedProduct_of_structuralInputs
    (hdecomp : SolvableMaximalTorusSemidirectStatement.{u})
    (hinter : SemigroupIntersectionStatement.{u})
    (hcentral : CentralStableVectorSubgroupStatement.{u}) :
    SemigroupOrderedProductStatement.{u} :=
  semigroupSolvableReduction_of_maximalTorusDecomposition hdecomp hinter
    (unipotentSemigroupOrderedProduct_of_centralVector
      semigroupRealization semigroupSmoothQuotient hinter hcentral)

end RelativeRoot

end Langlands.GroupScheme
