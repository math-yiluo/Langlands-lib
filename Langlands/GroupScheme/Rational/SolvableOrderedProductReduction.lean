import Langlands.GroupScheme.Rational.SolvableIntersectionProduct
import Langlands.GroupScheme.Rational.SemigroupSolvableReduction
import Langlands.GroupScheme.Rational.SemigroupSubgroupFactorization
import Langlands.GroupScheme.Rational.SemigroupFunctorialityProof

/-! # Exact solvable ordered products from narrower structural inputs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Semidirect

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {K G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom K.X.hom] [IsAffineHom G.X.hom]
    [Smooth K.X.hom] [Smooth G.X.hom]
    [ConnectedSpace K.X.left] [ConnectedSpace G.X.left]
    (a : AutomorphicAction K G) (b : AutomorphicAction S.toGrp G)
    (hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (q : T ⟶ K.X) (g : T ⟶ G.X), b.act s (a.act q g) = a.act q (b.act s g))

/-- For a solvable normal factor, fixed-containment connectedness supplies
the local intersection needed by the actual semidirect ordered product. -/
theorem hasOrderedSemigroupProducts_semidirect_of_solvable
    (hS : IsSplitTorus S.toGrp)
    (hConn : Torus.SolvableFixedContainmentConnectedStatement.{u})
    (hsolv : IsSolvableScheme G) (hb : HasOrderedSemigroupProducts b) :
    HasOrderedSemigroupProducts (a.semidirectLift b hcomm) := by
  apply hasOrderedSemigroupProducts_semidirect_of_comap
    a b hcomm hS semigroupFunctoriality
  · intro A
    exact semigroup_comap_eq_of_solvable hConn hsolv hS
      (a.semidirectLift b hcomm) b a.semidirectInl a.isClosedSubgroup_semidirectInl
      (fun _ s g => (a.semidirectLift_inl b hcomm s g).symm) A
  · exact hb

end Semidirect

section Factorization

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {K N P : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom K.X.hom] [IsAffineHom N.X.hom] [IsAffineHom P.X.hom]
    [Smooth K.X.hom] [Smooth N.X.hom]
    [ConnectedSpace K.X.left] [ConnectedSpace N.X.left]
    (b : AutomorphicAction S.toGrp P) (i : N ⟶ P) (j : K ⟶ P)
    [Mono i.hom.hom] [IsIso (subgroupMultiplication i j)]
    (hn : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range j))
    (hstable : b.IsStable (SubgroupFunctor.range i))
    (hfixed : ∀ (T : Over (Spec (CommRingCat.of k)))
      (s : T ⟶ S.X) (q : T ⟶ K.X),
      b.act s (q ≫ j.hom.hom) = q ≫ j.hom.hom)

include hn hfixed in
/-- A compatible actual factorization with solvable normal factor transfers
ordered products using only the solvable fixed-containment criterion. -/
theorem hasOrderedSemigroupProducts_of_solvable_subgroup_factorization
    (hS : IsSplitTorus S.toGrp)
    (hConn : Torus.SolvableFixedContainmentConnectedStatement.{u})
    (hsolv : IsSolvableScheme N)
    (hN : HasOrderedSemigroupProducts
      (b.onRepresentedSubgroup i ⟨inferInstance, rfl⟩ hstable)) :
    HasOrderedSemigroupProducts b := by
  let a := AutomorphicAction.ofNormalizedConjugation i j hn
  let c := b.onRepresentedSubgroup i ⟨inferInstance, rfl⟩ hstable
  have hcomm := normalizedSubgroupActions_commute i j hn b hstable hfixed
  have hproducts := hasOrderedSemigroupProducts_semidirect_of_solvable
    a c hcomm hS hConn hsolv hN
  exact hproducts.map_equivariant_iso (a.semidirectLift c hcomm) b
    (normalizedSubgroupFactorIso i j hn)
    (normalizedSubgroupFactorIso_equivariant i j hn b hstable hfixed)

end Factorization

/-- The exact arbitrary-field target follows from maximal-torus decomposition,
solvable fixed-containment connectedness and central stable vector existence. -/
theorem semigroupOrderedProduct_of_solvableStructuralInputs
    (hdecomp : SolvableMaximalTorusSemidirectStatement.{u})
    (hConn : Torus.SolvableFixedContainmentConnectedStatement.{u})
    (hCentral : CentralStableVectorSubgroupStatement.{u}) :
    SemigroupOrderedProductStatement.{u} := by
  apply semigroupOrderedProduct_of_algebraicallyClosed
  intro k _ _ G hG hAff hconn hsolv S hS a
  let := hAff
  let F := a.solvableFactorization hdecomp hS hG hconn hsolv
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
  apply hasOrderedSemigroupProducts_of_solvable_subgroup_factorization a
    F.normalInclusion F.torusInclusion hn F.normal_stable F.torus_fixed
    hS hConn (hsolv.of_mono F.normalInclusion)
  exact unipotentSemigroupOrderedProduct_of_solvableIntersection hConn hCentral
    k F.normalFactor F.normal_smooth F.normal_affine
    F.normal_connected F.normal_unipotent S hS
    (a.onRepresentedSubgroup F.normalInclusion ⟨inferInstance, rfl⟩ F.normal_stable)

section Data

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) {n : ℕ}
    (Ψ : Fin n → Set (characterLattice S))

/-- Actual ordered semigroup factors of a solvable group over the original
field, conditional on the three stated structural inputs. -/
def solvableOrderedSemigroupProduct
    (hdecomp : SolvableMaximalTorusSemidirectStatement.{u})
    (hConn : Torus.SolvableFixedContainmentConnectedStatement.{u})
    (hCentral : CentralStableVectorSubgroupStatement.{u})
    (hG : Smooth G.X.hom) (hconn : ConnectedSpace G.X.left)
    (hsolv : IsSolvableScheme G) (hS : IsSplitTorus S.toGrp)
    (hcover : (⋃ r, Ψ r) = actionWeightSupport b ⊤)
    (hdisj : ∀ r s, r ≠ s → Disjoint (Ψ r) (Ψ s))
    (hcross : ∀ r s, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S))) :
    OrderedSemigroupProductData b Ψ :=
  Classical.choice (by
    obtain ⟨H, j, hj, hp⟩ :=
      semigroupOrderedProduct_of_solvableStructuralInputs hdecomp hConn hCentral
        k G hG inferInstance hconn hsolv S hS b n Ψ hcover hdisj hcross
    let := hp
    exact ⟨⟨H, j, hj, asIso (orderedMultiplication j), rfl⟩⟩)

end Data

end Langlands.GroupScheme.RelativeRoot
