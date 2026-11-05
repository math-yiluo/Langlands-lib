import Langlands.GroupScheme.Reductive.FixedCenterContainingTorusStatement
import Langlands.GroupScheme.AutomorphicAction.SemidirectTorus
import Langlands.GroupScheme.Reductive.NormalCenterCentralizerReduction
import Langlands.GroupScheme.Rational.SemigroupSemidirect
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # A fixed split torus containing the full centre, from a reductive semidirect product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- If the semidirect product `H = G ⋊ S` is connected reductive, self-centralization of
maximal tori over algebraically closed fields puts the full centre of `G` in the closed torus
`M ∩ G` fixed by `S`, where `M` is a maximal torus of `H` containing `S`. -/
theorem exists_fixed_splitTorus_containing_center_of_semidirect_reductive
    (hcent : AlgClosedMaximalTorusCentralizerStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (hH : IsConnectedReductive b.semidirectProduct) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsSplitTorus T.toGrp ∧ IsClosedSubgroup j ∧
      center G ≤ SubgroupFunctor.range j ∧
      ∀ (U : Over (Spec (CommRingCat.of k))) (s : U ⟶ S.X) (t : U ⟶ T.X),
        b.act s (t ≫ j.hom.hom) = t ≫ j.hom.hom := by
  have := hG.smooth
  have := hG.isAffineHom
  have : IsAffineHom S.toGrp.X.hom := hS.isAffineHom
  have : Smooth S.toGrp.X.hom := hS.smooth
  -- The torus `T₀ = M ∩ G`, closed in `G` and fixed by `S`.
  obtain ⟨M, j, f, hM, hf, hT, hTc, hTa, hTs, hTconn, hTfixed⟩ :=
    b.exists_maximalTorus_with_fixed_intersection hS hG.smooth
  refine ⟨b.semidirectTorusIntersection j, b.semidirectTorusIntersectionInclusion j,
    hT.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting, hTc, ?_, hTfixed⟩
  intro U x hx
  -- The centre of `G` lies in the centre of `H`, which lies in `C_H(M) = M`.
  have hxH := center_le_comap_of_normal_of_algClosedMaximalTorusCentralizer hcent hH hG
    b.semidirectInl b.isClosedSubgroup_semidirectInl
    (RelativeRoot.range_semidirectInl_isNormal b) U hx
  have hxM : x ≫ b.semidirectInl.hom.hom ∈ (SubgroupFunctor.range j).carrier U := by
    rw [← hcent k b.semidirectProduct hH M j hM]
    exact center_le_torusCentralizer j _ hxH
  obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp hxM
  have hmem : x ≫ b.semidirectInl.hom.hom ∈
      (SubgroupFunctor.range (b.semidirectTorusIntersectionFst j ≫ j)).carrier U := by
    change x ≫ b.semidirectInl.hom.hom ∈ (SubgroupFunctor.range
      (commutativeSubgroupIntersectionFst j b.semidirectInl ≫ j)).carrier U
    rw [range_commutativeSubgroupIntersection j b.semidirectInl]
    exact ⟨⟨m, hm⟩, ⟨x, rfl⟩⟩
  obtain ⟨q, hq⟩ := SubgroupFunctor.mem_range.mp hmem
  refine ⟨q, ?_⟩
  change q ≫ (b.semidirectTorusIntersectionInclusion j).hom.hom = x
  rw [b.semidirectTorusIntersection_condition j] at hq
  apply (cancel_mono b.semidirectInl.hom.hom).mp
  simpa only [Grp.comp_hom_hom, Category.assoc] using hq

/-- Self-centralization of maximal tori over algebraically closed fields, together with
reductivity of every semidirect product of a connected reductive group by a split torus,
implies the exact fixed centre-containing torus statement. -/
def FixedCenterContainingTorusSemidirectReductionStatement : Prop :=
  AlgClosedMaximalTorusCentralizerStatement.{u} →
    (∀ (k : Type u) [Field k] [IsAlgClosed k]
      (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))), IsSplitTorus S.toGrp →
      ∀ b : AutomorphicAction S.toGrp G, IsConnectedReductive b.semidirectProduct) →
    FixedCenterContainingTorusStatement.{u}

/-- Apply `exists_fixed_splitTorus_containing_center_of_semidirect_reductive` to each
instance of the target. -/
theorem fixedCenterContainingTorusSemidirectReduction :
    FixedCenterContainingTorusSemidirectReductionStatement.{u} :=
  fun hcent hsemi k _ _ G hG S hS b =>
    exists_fixed_splitTorus_containing_center_of_semidirect_reductive hcent G hG S hS b
      (hsemi k G hG S hS b)

end Langlands.GroupScheme
