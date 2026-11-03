import Langlands.GroupScheme.AutomorphicAction.SemidirectDynamic
import Langlands.GroupScheme.Dynamic.ActionAffineRepresentability
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ImproperParabolic
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Lie.SubgroupEqualityProof
import Langlands.GroupScheme.Lie.KernelTargetMaps

/-! # Full-Lie criteria for automorphic-action dynamic functors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (a : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G)

local instance gm_isAffineHom : IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom :=
  isSplitTorus_gm.isAffineHom

local instance gm_smooth : Smooth (Gm (Spec (CommRingCat.of k))).X.hom := smooth_gm _

local instance gm_connected : ConnectedSpace (Gm (Spec (CommRingCat.of k))).X.left :=
  isSplitTorus_gm.connectedSpace

local instance gm_geometricallyConnected :
    GeometricallyConnected (Gm (Spec (CommRingCat.of k))).X.hom :=
  geometricallyConnected_of_connected _

local instance semidirect_connected : ConnectedSpace a.semidirectProduct.X.left := by
  change ConnectedSpace ↥(CategoryTheory.Limits.pullback G.X.hom
    (Gm (Spec (CommRingCat.of k))).X.hom)
  infer_instance

local instance semidirect_isAffine : IsAffine a.semidirectProduct.X.left :=
  isAffine_of_isAffineHom a.semidirectProduct.X.hom

/-- A smooth closed subgroup of the semidirect product containing the acting
factor and all normal-factor Lie points is the whole semidirect product. -/
theorem semidirect_subgroup_eq_top_of_lieKernel
    {F : SubgroupFunctor a.semidirectProduct}
    {K : GroupScheme (Spec (CommRingCat.of k))} {κ : K ⟶ a.semidirectProduct}
    (hκ : F.IsRepresentedBy κ) (hκc : IsClosedSubgroup κ) [Smooth K.X.hom]
    (hinr : SubgroupFunctor.range a.semidirectInr ≤ F)
    (hinl : ∀ X : lieKernel G k, X.val ≫ a.semidirectInl.hom.hom ∈ F.carrier _) :
    F = ⊤ := by
  have : Mono κ.hom.hom := hκ.1
  rw [← hκ.2]
  refine lieSubgroupEquality k a.semidirectProduct K κ hκc fun X => ?_
  let t := Lie.targetMap a.semidirectProjection k X
  let Y : lieKernel a.semidirectProduct k := X * (Lie.targetMap a.semidirectInr k t)⁻¹
  have hYproj : Y.val ≫ a.semidirectProjection.hom.hom = 1 := by
    change (X.val * (t.val ≫ a.semidirectInr.hom.hom)⁻¹) ≫
      a.semidirectProjection.hom.hom = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, ← Grp.comp_hom_hom,
      semidirectInr_comp_projection, Grp.id_hom_hom, Category.comp_id]
    exact mul_inv_cancel _
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp
    ((a.mem_range_semidirectInl_iff Y.val).mpr hYproj)
  let Z : lieKernel G k := ⟨y, mem_lieKernel_of_comp a.semidirectInl y (by
    rw [hy]
    exact Y.property)⟩
  have hYF : Y.val ∈ F.carrier _ := by
    rw [← hy]
    exact hinl Z
  have htF : t.val ≫ a.semidirectInr.hom.hom ∈ F.carrier _ :=
    hinr _ (SubgroupFunctor.mem_range.mpr ⟨t.val, rfl⟩)
  have hXF : X.val ∈ F.carrier _ := by
    have hm := (F.carrier _).mul_mem hYF htF
    change X.val * (t.val ≫ a.semidirectInr.hom.hom)⁻¹ *
      (t.val ≫ a.semidirectInr.hom.hom) ∈ F.carrier _ at hm
    simpa only [inv_mul_cancel_right] using hm
  rw [← hκ.2] at hXF
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hXF
  exact ⟨⟨z, mem_lieKernel_of_comp κ z (by rw [hz]; exact X.property)⟩, hz⟩

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left] in
/-- The range of the acting factor lies in its own actual centralizer. -/
theorem range_semidirectInr_le_centralizer :
    SubgroupFunctor.range a.semidirectInr ≤ Dynamic.centralizer a.semidirectInr := by
  intro T x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have ht : t ∈ (Dynamic.centralizer (𝟙 (Gm (Spec (CommRingCat.of k))).toGrp)).carrier T := by
    rw [Dynamic.centralizer_eq_top_of_commutative]
    exact Subgroup.mem_top _
  simpa only [Category.id_comp, SubgroupFunctor.mem_comap] using
    Dynamic.centralizer_le_comap (𝟙 (Gm (Spec (CommRingCat.of k))).toGrp)
      a.semidirectInr T ht

/-- An affine action on a smooth connected group whose full Lie algebra admits
limits has a parabolic functor equal to the whole group. -/
theorem parabolic_eq_top_of_lieKernel
    (hLie : ∀ X : lieKernel G k, X.val ∈ a.parabolic.carrier _) :
    a.parabolic = ⊤ := by
  let K := Dynamic.Affine.parabolicScheme a.semidirectInr
  let κ := Dynamic.Affine.parabolicHom a.semidirectInr
  have hκ := Dynamic.Affine.isRepresentedBy_parabolicHom a.semidirectInr
  have : Smooth K.X.hom := (dynamicSmooth k a.semidirectProduct a.semidirectInr K κ).1 hκ
  have htop : Dynamic.parabolic a.semidirectInr = ⊤ := by
    apply a.semidirect_subgroup_eq_top_of_lieKernel hκ
      (Dynamic.Affine.isClosedSubgroup_parabolicHom a.semidirectInr)
      ((a.range_semidirectInr_le_centralizer).trans (Dynamic.centralizer_le_parabolic _))
    intro X
    have hX := hLie X
    have heq : a.parabolic =
        (Dynamic.parabolic a.semidirectInr).comap a.semidirectInl := by
      simpa only [restrict_id, Category.id_comp] using
        a.semidirect_parabolic_eq_comap (𝟙 _)
    rw [heq, SubgroupFunctor.mem_comap] at hX
    exact hX
  simpa only [restrict_id, Category.id_comp, htop, SubgroupFunctor.comap_top] using
    a.semidirect_parabolic_eq_comap (𝟙 _)

/-- An affine action on a smooth connected group fixing its full Lie algebra
fixes the whole group. -/
theorem centralizer_eq_top_of_lieKernel
    (hLie : ∀ X : lieKernel G k, X.val ∈ a.centralizer.carrier _) :
    a.centralizer = ⊤ := by
  let K := Dynamic.Affine.centralizerScheme a.semidirectInr
  let κ := Dynamic.Affine.centralizerHom a.semidirectInr
  have hκ := Dynamic.Affine.isRepresentedBy_centralizerHom a.semidirectInr
  have : Smooth K.X.hom := (dynamicSmooth k a.semidirectProduct a.semidirectInr K κ).2.1 hκ
  have htop : Dynamic.centralizer a.semidirectInr = ⊤ := by
    apply a.semidirect_subgroup_eq_top_of_lieKernel hκ
      (Dynamic.Affine.isClosedSubgroup_centralizerHom a.semidirectInr)
      a.range_semidirectInr_le_centralizer
    intro X
    have hX := hLie X
    have heq : a.centralizer =
        (Dynamic.centralizer a.semidirectInr).comap a.semidirectInl := by
      simpa only [restrict_id, Category.id_comp] using
        a.semidirect_centralizer_eq_comap (𝟙 _)
    rw [heq, SubgroupFunctor.mem_comap] at hX
    exact hX
  simpa only [restrict_id, Category.id_comp, htop, SubgroupFunctor.comap_top] using
    a.semidirect_centralizer_eq_comap (𝟙 _)

end Langlands.GroupScheme.AutomorphicAction
