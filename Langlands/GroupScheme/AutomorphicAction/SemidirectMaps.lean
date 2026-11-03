import Langlands.GroupScheme.AutomorphicAction.SemidirectProduct
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Dynamic.Functoriality
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Canonical morphisms of the semidirect group scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {B : Scheme.{u}} {H G : GroupScheme B} (a : AutomorphicAction H G)

@[simp] theorem semidirectPointsEquiv_lift {T : Over B}
    (g : T ⟶ G.X) (h : T ⟶ H.X) :
    a.semidirectPointsEquiv T (lift g h) = ⟨g, h⟩ := by
  apply SemidirectProduct.ext
  · exact lift_fst _ _
  · exact lift_snd _ _

/-- The normal-factor inclusion on the full point presheaf. -/
def semidirectInlPoints : G.points ⟶ a.semidirectPoints where
  app T := GrpCat.ofHom SemidirectProduct.inl
  naturality {T V} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply SemidirectProduct.ext
    · rfl
    · exact (MonObj.comp_one f.unop).symm

/-- The acting-factor inclusion on the full point presheaf. -/
def semidirectInrPoints : H.points ⟶ a.semidirectPoints where
  app T := GrpCat.ofHom SemidirectProduct.inr
  naturality {T V} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro h
    apply SemidirectProduct.ext
    · exact (MonObj.comp_one f.unop).symm
    · rfl

/-- The projection to the acting factor on the full point presheaf. -/
def semidirectProjectionPoints : a.semidirectPoints ⟶ H.points where
  app T := GrpCat.ofHom SemidirectProduct.rightHom
  naturality {T V} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    rfl

/-- The inclusion of the normal factor, recovered as a group-scheme morphism. -/
def semidirectInl : G ⟶ a.semidirectProduct :=
  yonedaGrpFullyFaithful.preimage (a.semidirectInlPoints ≫ a.semidirectPointsIso.inv)

/-- The inclusion of the acting factor, recovered as a group-scheme morphism. -/
def semidirectInr : H ⟶ a.semidirectProduct :=
  yonedaGrpFullyFaithful.preimage (a.semidirectInrPoints ≫ a.semidirectPointsIso.inv)

/-- Projection to the acting factor, recovered as a group-scheme morphism. -/
def semidirectProjection : a.semidirectProduct ⟶ H :=
  yonedaGrpFullyFaithful.preimage (a.semidirectPointsIso.hom ≫ a.semidirectProjectionPoints)

@[simp] theorem semidirectInl_points {T : Over B} (g : T ⟶ G.X) :
    a.semidirectPointsEquiv T (g ≫ a.semidirectInl.hom.hom) =
      SemidirectProduct.inl g := by
  have hn : pointsMap a.semidirectInl ≫ a.semidirectPointsIso.hom =
      a.semidirectInlPoints := by
    calc
      _ = (a.semidirectInlPoints ≫ a.semidirectPointsIso.inv) ≫
          a.semidirectPointsIso.hom :=
        congrArg (fun k => k ≫ a.semidirectPointsIso.hom)
          (yonedaGrpFullyFaithful.map_preimage _)
      _ = _ := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun k => (k.app (op T)).hom g) hn

@[simp] theorem semidirectInr_points {T : Over B} (h : T ⟶ H.X) :
    a.semidirectPointsEquiv T (h ≫ a.semidirectInr.hom.hom) =
      SemidirectProduct.inr h := by
  have hn : pointsMap a.semidirectInr ≫ a.semidirectPointsIso.hom =
      a.semidirectInrPoints := by
    calc
      _ = (a.semidirectInrPoints ≫ a.semidirectPointsIso.inv) ≫
          a.semidirectPointsIso.hom :=
        congrArg (fun k => k ≫ a.semidirectPointsIso.hom)
          (yonedaGrpFullyFaithful.map_preimage _)
      _ = _ := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun k => (k.app (op T)).hom h) hn

@[simp] theorem semidirectProjection_points {T : Over B}
    (x : T ⟶ a.semidirectProduct.X) :
    x ≫ a.semidirectProjection.hom.hom = (a.semidirectPointsEquiv T x).right := by
  have hn : pointsMap a.semidirectProjection =
      a.semidirectPointsIso.hom ≫ a.semidirectProjectionPoints :=
    yonedaGrpFullyFaithful.map_preimage _
  exact congrArg (fun k => (k.app (op T)).hom x) hn

@[simp] theorem semidirectInl_hom :
    a.semidirectInl.hom.hom = lift (𝟙 G.X) (1 : G.X ⟶ H.X) := by
  apply (a.semidirectPointsEquiv G.X).injective
  rw [semidirectPointsEquiv_lift]
  calc
    _ = SemidirectProduct.inl (𝟙 G.X) := by
      simpa only [Category.id_comp] using a.semidirectInl_points (𝟙 G.X)
    _ = _ := rfl

@[simp] theorem semidirectInr_hom :
    a.semidirectInr.hom.hom = lift (1 : H.X ⟶ G.X) (𝟙 H.X) := by
  apply (a.semidirectPointsEquiv H.X).injective
  rw [semidirectPointsEquiv_lift]
  calc
    _ = SemidirectProduct.inr (𝟙 H.X) := by
      simpa only [Category.id_comp] using a.semidirectInr_points (𝟙 H.X)
    _ = _ := rfl

@[simp] theorem semidirectProjection_hom :
    a.semidirectProjection.hom.hom = snd G.X H.X := by
  have hn := a.semidirectProjection_points (𝟙 a.semidirectProduct.X)
  rw [semidirectPointsEquiv_right] at hn
  exact (Category.id_comp _).symm.trans (hn.trans (Category.id_comp _))

/-- Conjugation by the acting factor recovers the original actual action. -/
theorem semidirect_conjugation {T : Over B} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    (conjugation a.semidirectInr).act h (g ≫ a.semidirectInl.hom.hom) =
      a.act h g ≫ a.semidirectInl.hom.hom := by
  apply (a.semidirectPointsEquiv T).injective
  rw [conjugation_act, map_mul, map_mul, map_inv,
    semidirectInr_points, semidirectInl_points, semidirectInl_points]
  simpa only [map_inv, pointsAction_apply] using
    (SemidirectProduct.inl_aut (φ := a.pointsAction T) h g).symm

instance semidirectInl_mono : Mono a.semidirectInl.hom.hom := by
  constructor
  intro T f g he
  have hc := congrArg (a.semidirectPointsEquiv T) he
  rw [semidirectInl_points, semidirectInl_points] at hc
  exact congrArg SemidirectProduct.left hc

instance semidirectInr_mono : Mono a.semidirectInr.hom.hom := by
  constructor
  intro T f g he
  have hc := congrArg (a.semidirectPointsEquiv T) he
  rw [semidirectInr_points, semidirectInr_points] at hc
  exact congrArg SemidirectProduct.right hc

@[simp] theorem semidirectInr_comp_projection :
    a.semidirectInr ≫ a.semidirectProjection = 𝟙 H := by
  apply Grp.hom_ext
  change a.semidirectInr.hom.hom ≫ a.semidirectProjection.hom.hom = 𝟙 H.X
  calc
    _ = lift (1 : H.X ⟶ G.X) (𝟙 H.X) ≫ snd G.X H.X := by
      rw [semidirectInr_hom, semidirectProjection_hom]
      rfl
    _ = _ := lift_snd _ _

@[simp] theorem semidirectInl_comp_projection :
    a.semidirectInl.hom.hom ≫ a.semidirectProjection.hom.hom = (1 : G.X ⟶ H.X) := by
  calc
    _ = lift (𝟙 G.X) (1 : G.X ⟶ H.X) ≫ snd G.X H.X := by
      rw [semidirectInl_hom, semidirectProjection_hom]
      rfl
    _ = _ := lift_snd _ _

/-- The normal-factor inclusion has exactly the kernel points of the projection. -/
theorem mem_range_semidirectInl_iff {T : Over B} (x : T ⟶ a.semidirectProduct.X) :
    x ∈ (SubgroupFunctor.range a.semidirectInl).carrier T ↔
      x ≫ a.semidirectProjection.hom.hom = 1 := by
  rw [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    rw [Category.assoc, semidirectInl_comp_projection, MonObj.comp_one]
  · intro hx
    refine ⟨(a.semidirectPointsEquiv T x).left, ?_⟩
    apply (a.semidirectPointsEquiv T).injective
    rw [semidirectInl_points]
    apply SemidirectProduct.ext
    · rfl
    · change 1 = (a.semidirectPointsEquiv T x).right
      rw [← semidirectProjection_points, hx]

/-- The kernel is represented by the original normal factor on all tests. -/
theorem range_semidirectInl :
    SubgroupFunctor.range a.semidirectInl =
      (⊥ : SubgroupFunctor H).comap a.semidirectProjection := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.mem_comap, SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  exact a.mem_range_semidirectInl_iff x

/-- The normal-factor inclusion is closed when the acting factor is separated. -/
theorem isClosedSubgroup_semidirectInl [IsSeparated H.X.hom] :
    IsClosedSubgroup a.semidirectInl := by
  change IsClosedImmersion a.semidirectInl.hom.hom.left
  have hsep : IsSeparated (fst G.X H.X).left := by
    change IsSeparated (pullback.fst G.X.hom H.X.hom)
    infer_instance
  have he : a.semidirectInl.hom.hom.left ≫ (fst G.X H.X).left = 𝟙 G.X.left := by
    change (a.semidirectInl.hom.hom ≫ fst G.X H.X).left = _
    calc
      _ = (lift (𝟙 G.X) (1 : G.X ⟶ H.X) ≫ fst G.X H.X).left := by
        rw [semidirectInl_hom]
        rfl
      _ = _ := congrArg Over.Hom.left (lift_fst (𝟙 G.X) (1 : G.X ⟶ H.X))
  have hclosed : IsClosedImmersion (a.semidirectInl.hom.hom.left ≫ (fst G.X H.X).left) :=
    he.symm ▸ (inferInstance : IsClosedImmersion (𝟙 G.X.left))
  exact @IsClosedImmersion.of_comp _ _ _ _ _ hclosed hsep

/-- The acting-factor inclusion is closed when the normal factor is separated. -/
theorem isClosedSubgroup_semidirectInr [IsSeparated G.X.hom] :
    IsClosedSubgroup a.semidirectInr := by
  change IsClosedImmersion a.semidirectInr.hom.hom.left
  have hsep : IsSeparated (snd G.X H.X).left := by
    change IsSeparated (pullback.snd G.X.hom H.X.hom)
    infer_instance
  have he : a.semidirectInr.hom.hom.left ≫ (snd G.X H.X).left = 𝟙 H.X.left := by
    change (a.semidirectInr.hom.hom ≫ snd G.X H.X).left = _
    calc
      _ = (lift (1 : H.X ⟶ G.X) (𝟙 H.X) ≫ snd G.X H.X).left := by
        rw [semidirectInr_hom]
        rfl
      _ = _ := congrArg Over.Hom.left (lift_snd (1 : H.X ⟶ G.X) (𝟙 H.X))
  have hclosed : IsClosedImmersion (a.semidirectInr.hom.hom.left ≫ (snd G.X H.X).left) :=
    he.symm ▸ (inferInstance : IsClosedImmersion (𝟙 H.X.left))
  exact @IsClosedImmersion.of_comp _ _ _ _ _ hclosed hsep

set_option backward.isDefEq.respectTransparency.types false in
instance semidirectProduct_isAffineHom [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] :
    IsAffineHom a.semidirectProduct.X.hom := by
  change IsAffineHom (pullback.fst G.X.hom H.X.hom ≫ G.X.hom)
  have hfst : IsAffineHom (pullback.fst G.X.hom H.X.hom) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  infer_instance

instance semidirectProduct_smooth [Smooth G.X.hom] [Smooth H.X.hom] :
    Smooth a.semidirectProduct.X.hom :=
  smooth_tensor G.X H.X inferInstance inferInstance

/-- For a commutative acting factor, projection is invariant under its conjugation action. -/
theorem semidirectProjection_conjugation [IsCommMonObj H.X] {T : Over B}
    (h : T ⟶ H.X) (x : T ⟶ a.semidirectProduct.X) :
    (conjugation a.semidirectInr).act h x ≫ a.semidirectProjection.hom.hom =
      x ≫ a.semidirectProjection.hom.hom := by
  rw [conjugation_act, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  have hh : (h ≫ a.semidirectInr.hom.hom) ≫ a.semidirectProjection.hom.hom = h := by
    change (h ≫ (a.semidirectInr ≫ a.semidirectProjection).hom.hom) = h
    rw [semidirectInr_comp_projection]
    exact Category.comp_id _
  rw [hh]
  simp only [mul_comm h, mul_assoc, inv_mul_cancel, mul_one]

end Langlands.GroupScheme.AutomorphicAction
