import Langlands.GroupScheme.Reductive.FixedCenterContainingTorusStatement
import Langlands.GroupScheme.AutomorphicAction.SemidirectTorus
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerReduction
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.InnerAutomorphism

/-! # A fixed split torus containing the full centre, from conjugacy and self-centralization -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

section Center

variable {B : Scheme.{u}} {S G : GroupScheme B} (a : AutomorphicAction S G)

/-- An automorphic action carries central points to central points, on every test scheme. -/
theorem act_mem_center {U : Over B} (s : U ⟶ S.X) {x : U ⟶ G.X}
    (hx : x ∈ (center G).carrier U) : a.act s x ∈ (center G).carrier U := by
  intro V c h
  rw [a.naturality]
  have hc := (hx V c (a.act (c ≫ s)⁻¹ h)).map (a.pointsAction V (c ≫ s))
  simpa only [pointsAction_apply, act_act_inv] using hc

/-- Conjugating a central point of the normal factor by a point `g` of the semidirect
product: with `s` the acting coordinate of `g`, the point `g · (s⁻¹ · x) · g⁻¹` is `x`. -/
theorem semidirect_conj_inl_act_inv_of_mem_center {U : Over B}
    (g : U ⟶ a.semidirectProduct.X) {x : U ⟶ G.X} (hx : x ∈ (center G).carrier U) :
    g * (a.act (a.semidirectPointsEquiv U g).right⁻¹ x ≫ a.semidirectInl.hom.hom) * g⁻¹ =
      x ≫ a.semidirectInl.hom.hom := by
  apply (a.semidirectPointsEquiv U).injective
  rw [map_mul, map_mul, map_inv, semidirectInl_points, semidirectInl_points]
  set p := a.semidirectPointsEquiv U g
  have hl : p.left * x * p.left⁻¹ = x := by
    rw [← (commute_of_mem_center hx p.left).eq, mul_inv_cancel_right]
  refine SemidirectProduct.ext ?_ ?_
  · simpa only [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      SemidirectProduct.mul_right, mul_one, pointsAction_apply, act_act_inv,
      ← mul_assoc] using hl
  · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inl, mul_one, mul_inv_cancel]

end Center

end AutomorphicAction

/-- The exact fixed centre-containing torus statement follows from conjugacy of maximal tori
(Milne 17.10) and self-centralization of maximal tori of connected reductive groups over
algebraically closed fields (Milne 17.61(a)/17.84). -/
def FixedCenterContainingTorusReductionStatement : Prop :=
  MaximalTorusConjugacyStatement.{u} → AlgClosedMaximalTorusCentralizerStatement.{u} →
    FixedCenterContainingTorusStatement.{u}

/-- In `H = G ⋊ S`, a maximal torus `M` containing `S` meets `G` in a closed torus fixed by
`S`. A maximal torus `T₁` of `G` contains the centre and lies in a maximal torus `M'` of `H`.
Conjugating `M'` onto `M` by a rational point of `H` carries the centre (which it preserves)
into `M ∩ G`. -/
theorem fixedCenterContainingTorusReduction :
    FixedCenterContainingTorusReductionStatement.{u} := by
  intro hconj hcent k _ _ G hG S hS b
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  have : IsAffineHom S.toGrp.X.hom := hS.isAffineHom
  have : Smooth S.toGrp.X.hom := hS.smooth
  have : ConnectedSpace S.toGrp.X.left := hS.connectedSpace
  -- The torus `T₀ = M ∩ G`, closed in `G` and fixed by `S`.
  obtain ⟨M, j, f, hM, hf, hT, hTc, hTa, hTs, hTconn, hTfixed⟩ :=
    b.exists_maximalTorus_with_fixed_intersection hS hG.smooth
  -- A maximal torus `T₁` of `G`, extended to a maximal torus `M'` of `H`.
  obtain ⟨T₁, i₁, hi₁⟩ := maximalTorusExistence k G
  obtain ⟨M', j', hM', f', hf'⟩ :=
    exists_maximalTorus_extension_of_finiteType b.semidirectProduct (i₁ ≫ b.semidirectInl)
      hi₁.1 (hi₁.2.1.comp b.isClosedSubgroup_semidirectInl)
  -- `H` is smooth, affine and connected, so `M'` and `M` are conjugate.
  have : GeometricallyConnected G.X.hom := G.geometricallyConnected_of_connected
  have : ConnectedSpace b.semidirectProduct.X.left := by
    change ConnectedSpace (pullback G.X.hom S.toGrp.X.hom : Scheme.{u})
    infer_instance
  obtain ⟨g, φ, hg⟩ := hconj k b.semidirectProduct M' M j' j hM' hM
  refine ⟨b.semidirectTorusIntersection j, b.semidirectTorusIntersectionInclusion j,
    hT.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting, hTc, ?_, hTfixed⟩
  intro U x hx
  -- The central point `s⁻¹ · x`, with `s` the acting coordinate of `g`, lies in `T₁`.
  have hy₁ : b.act (b.semidirectPointsEquiv U (b.semidirectProduct.constantPoint g U)).right⁻¹ x ∈
      (SubgroupFunctor.range i₁).carrier U := by
    rw [← hcent k G hG T₁ i₁ hi₁]
    exact center_le_torusCentralizer i₁ _ (b.act_mem_center _ hx)
  obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.mp hy₁
  -- Conjugation by `g` carries this point of `T₁ ⊆ M'` to `x`, which therefore lies in `M`.
  have hxM : x ≫ b.semidirectInl.hom.hom =
      (t ≫ f'.hom.hom ≫ (CommGroupScheme.groupHom φ.hom).hom.hom) ≫ j.hom.hom := by
    have e1 := congrArg (fun e => (t ≫ f'.hom.hom) ≫ e.hom.hom) hg
    have e2 := congrArg (fun e => t ≫ e.hom.hom) hf'
    simp only [Grp.comp_hom_hom, ← Category.assoc] at e1 e2
    rw [e2, ht, comp_innerIso_hom, b.semidirect_conj_inl_act_inv_of_mem_center _ hx] at e1
    simpa only [Category.assoc] using e1
  have hmem : x ≫ b.semidirectInl.hom.hom ∈
      (SubgroupFunctor.range (b.semidirectTorusIntersectionFst j ≫ j)).carrier U := by
    change x ≫ b.semidirectInl.hom.hom ∈ (SubgroupFunctor.range
      (commutativeSubgroupIntersectionFst j b.semidirectInl ≫ j)).carrier U
    rw [range_commutativeSubgroupIntersection j b.semidirectInl]
    exact ⟨⟨_, hxM.symm⟩, ⟨x, rfl⟩⟩
  obtain ⟨q, hq⟩ := SubgroupFunctor.mem_range.mp hmem
  refine ⟨q, ?_⟩
  change q ≫ (b.semidirectTorusIntersectionInclusion j).hom.hom = x
  rw [b.semidirectTorusIntersection_condition j] at hq
  apply (cancel_mono b.semidirectInl.hom.hom).mp
  simpa only [Grp.comp_hom_hom, Category.assoc] using hq

end Langlands.GroupScheme
