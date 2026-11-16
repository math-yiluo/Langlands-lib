import Langlands.AlgebraicGeometry.AffineSmoothRetract
import Langlands.GroupScheme.AutomorphicAction.SemidirectSubgroup
import Langlands.GroupScheme.Dynamic.ActionAffineRepresentability
import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.Dynamic.ImproperParabolic

/-! # Smoothness of parabolics for automorphic Gm-actions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {N : GroupScheme S}
    (a : AutomorphicAction (Gm S).toGrp N)

/-- The acting multiplicative group lies in the centralizer of its inclusion,
over every base scheme. -/
theorem actingFactor_le_dynamicCentralizer :
    SubgroupFunctor.range a.semidirectInr ≤ Dynamic.centralizer a.semidirectInr := by
  intro T x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have ht : t ∈ (Dynamic.centralizer (𝟙 (Gm S).toGrp)).carrier T := by
    rw [Dynamic.centralizer_eq_top_of_commutative]
    exact Subgroup.mem_top _
  simpa only [Category.id_comp, SubgroupFunctor.mem_comap] using
    Dynamic.centralizer_le_comap (𝟙 (Gm S).toGrp) a.semidirectInr T ht

/-- The normal coordinate of an ambient dynamic parabolic point admits an
orbit limit for the original action. -/
theorem normalCoordinate_mem_parabolic {T : Over S}
    (x : T ⟶ a.semidirectProduct.X)
    (hx : x ∈ (Dynamic.parabolic a.semidirectInr).carrier T) :
    (a.semidirectPointsEquiv T x).left ∈ a.parabolic.carrier T := by
  let : IsAffineHom (Gm S).X.hom := isSplitTorus_gm.isAffineHom
  have heq : a.parabolic =
      (Dynamic.parabolic a.semidirectInr).comap a.semidirectInl := by
    simpa only [restrict_id, Category.id_comp] using
      a.semidirect_parabolic_eq_comap (𝟙 _)
  rw [heq, SubgroupFunctor.mem_comap]
  have ht : (a.semidirectPointsEquiv T x).right ≫ a.semidirectInr.hom.hom ∈
      (Dynamic.parabolic a.semidirectInr).carrier T :=
    ((a.actingFactor_le_dynamicCentralizer).trans
      (Dynamic.centralizer_le_parabolic _)) T ⟨_, rfl⟩
  have he : (a.semidirectPointsEquiv T x).left ≫ a.semidirectInl.hom.hom =
      x * ((a.semidirectPointsEquiv T x).right ≫ a.semidirectInr.hom.hom)⁻¹ :=
    eq_mul_inv_iff_mul_eq.mpr (a.semidirect_point_decomposition x).symm
  rw [he]
  exact (Dynamic.parabolic a.semidirectInr).carrier T |>.mul_mem hx
    ((Dynamic.parabolic a.semidirectInr).carrier T |>.inv_mem ht)

/-- The normal coordinate factors through any representative of the action
parabolic. -/
theorem exists_parabolicNormalProjection {V K : GroupScheme S}
    {v : V ⟶ a.semidirectProduct}
    (hv : (Dynamic.parabolic a.semidirectInr).IsRepresentedBy v)
    {j : K ⟶ N} (hj : a.parabolic.IsRepresentedBy j) :
    ∃ r : V.X ⟶ K.X,
      r ≫ j.hom.hom = (a.semidirectPointsEquiv V.X v.hom.hom).left := by
  have hvpoint : v.hom.hom ∈ (Dynamic.parabolic a.semidirectInr).carrier V.X := by
    rw [← hv.2, SubgroupFunctor.mem_range]
    exact ⟨𝟙 _, Category.id_comp _⟩
  have hnormal := a.normalCoordinate_mem_parabolic v.hom.hom hvpoint
  rwa [← hj.2, SubgroupFunctor.mem_range] at hnormal

/-- The scheme morphism obtained by restricting the semidirect normal
coordinate to the two represented parabolics. -/
def parabolicNormalProjection {V K : GroupScheme S}
    {v : V ⟶ a.semidirectProduct}
    (hv : (Dynamic.parabolic a.semidirectInr).IsRepresentedBy v)
    {j : K ⟶ N} (hj : a.parabolic.IsRepresentedBy j) : V.X ⟶ K.X :=
  (a.exists_parabolicNormalProjection hv hj).choose

theorem parabolicNormalProjection_comp {V K : GroupScheme S}
    {v : V ⟶ a.semidirectProduct}
    (hv : (Dynamic.parabolic a.semidirectInr).IsRepresentedBy v)
    {j : K ⟶ N} (hj : a.parabolic.IsRepresentedBy j) :
    a.parabolicNormalProjection hv hj ≫ j.hom.hom =
      (a.semidirectPointsEquiv V.X v.hom.hom).left :=
  (a.exists_parabolicNormalProjection hv hj).choose_spec

/-- Every affine representative of the action parabolic of a smooth affine
group is smooth, over an arbitrary base scheme. -/
theorem smooth_of_isRepresentedBy_parabolic
    [IsAffineHom N.X.hom] [Smooth N.X.hom]
    {K : GroupScheme S} [IsAffineHom K.X.hom] {j : K ⟶ N}
    (hj : a.parabolic.IsRepresentedBy j) : Smooth K.X.hom := by
  let : IsAffineHom (Gm S).X.hom := isSplitTorus_gm.isAffineHom
  let : Smooth (Gm S).X.hom := smooth_gm S
  obtain ⟨V, v, hvc, hvfp, hv⟩ :=
    (dynamicBaseRepresentability S a.semidirectProduct a.semidirectInr).1
  let : IsClosedImmersion v.hom.hom.left := hvc
  let : IsAffineHom V.X.hom := by
    rw [← Over.w v.hom.hom]
    infer_instance
  let : Smooth V.X.hom :=
    ((dynamicBaseSmoothConnected S a.semidirectProduct a.semidirectInr V v).2.1 hv).1
  let r := a.parabolicNormalProjection hv hj
  have hr : r ≫ j.hom.hom = (a.semidirectPointsEquiv V.X v.hom.hom).left :=
    a.parabolicNormalProjection_comp hv hj
  have heq : a.parabolic =
      (Dynamic.parabolic a.semidirectInr).comap a.semidirectInl := by
    simpa only [restrict_id, Category.id_comp] using
      a.semidirect_parabolic_eq_comap (𝟙 _)
  have hjpoint : j.hom.hom ∈ a.parabolic.carrier K.X := by
    rw [← hj.2, SubgroupFunctor.mem_range]
    exact ⟨𝟙 _, Category.id_comp _⟩
  rw [heq, SubgroupFunctor.mem_comap, ← hv.2, SubgroupFunctor.mem_range] at hjpoint
  obtain ⟨i, hi⟩ := hjpoint
  let : Mono j.hom.hom := hj.1
  have hret : i ≫ r = 𝟙 K.X := by
    apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, hr, semidirectPointsEquiv_left, ← Category.assoc, hi]
    simp only [Category.assoc, semidirectInl_hom, CategoryTheory.CartesianMonoidalCategory.lift_fst,
      Category.comp_id, Category.id_comp]
  exact AffineRetractGeometry.SchemeRetract.smooth ⟨i, r, hret⟩

end Langlands.GroupScheme.AutomorphicAction
