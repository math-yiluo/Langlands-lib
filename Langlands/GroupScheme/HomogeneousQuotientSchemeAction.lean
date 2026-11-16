import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
import Langlands.GroupScheme.DominantHomFlat
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # Actual homogeneous quotient actions have smooth relations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} (G : GroupScheme S)
  (H : SubgroupFunctor G) {Q : Over S} (q : G.X ⟶ Q)
  (hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ H.carrier T)
  [QuasiCompact q.left] [Smooth q.left] [Surjective q.left]

/-- After the smooth quotient cover, the actual action relation is a group shear
followed by the product of the two quotient projections. -/
theorem flagQuotientSchemeAction_relation_comp :
    (G.X ◁ q) ≫ lift (flagQuotientSchemeAction G H q hfib).hom (snd G.X Q) =
      (DominantHomFlat.shearRight (𝟙 G.X)).hom ≫ (q ⊗ₘ q) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, flagQuotientSchemeAction_hom,
      fac_flagQuotientActionHom, tensorHom_fst]
    simp only [DominantHomFlat.shearRight, lift_fst_assoc, Category.comp_id, Hom.mul_def,
      lift_fst_snd, Category.id_comp]
  · simp only [Category.assoc, lift_snd, whiskerLeft_snd, tensorHom_snd,
      DominantHomFlat.shearRight, lift_snd_assoc]

/-- Every supplied smooth fpqc coset projection has a smooth actual left action relation. -/
theorem smooth_flagQuotientSchemeAction_relation :
    Smooth (lift (flagQuotientSchemeAction G H q hfib).hom (snd G.X Q)).left := by
  have hs : Smooth (G.X ◁ q).left := by
    change Smooth (𝟙 G.X ⊗ₘ q).left
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @Smooth) inferInstance inferInstance
      (Over.w _).symm (Over.w _).symm
  have hu : Surjective (G.X ◁ q).left := by
    change Surjective (𝟙 G.X ⊗ₘ q).left
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @Surjective) inferInstance inferInstance
      (Over.w _).symm (Over.w _).symm
  have hp : Smooth (q ⊗ₘ q).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @Smooth) inferInstance inferInstance
      (Over.w _).symm (Over.w _).symm
  have : IsIso (DominantHomFlat.shearRight (𝟙 G.X)).hom.left :=
    (Over.forget S).map_isIso (DominantHomFlat.shearRight (𝟙 G.X)).hom
  have hc : Smooth ((G.X ◁ q).left ≫
      (lift (flagQuotientSchemeAction G H q hfib).hom (snd G.X Q)).left) := by
    rw [← Over.comp_left, flagQuotientSchemeAction_relation_comp, Over.comp_left]
    infer_instance
  exact Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
    (G.X ◁ q).left _

end Dynamic

namespace HomogeneousQuotientFromEmbedding.HomogeneousQuotient

variable {S : Scheme.{u}} {G H : GroupScheme S} {i : H ⟶ G}
  (Q : HomogeneousQuotient i)

/-- The actual left action on the supplied homogeneous quotient. -/
@[instance_reducible]
def action : SchemeAction G Q.scheme :=
  letI := Q.smooth_projection
  letI := Q.surjective_projection
  letI := Q.quasiCompact_projection
  Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range i) Q.projection Q.fibers

/-- The image of the identity section in the supplied homogeneous quotient. -/
def identityCoset : 𝟙_ (Over S) ⟶ Q.scheme := 1 ≫ Q.projection

/-- The quotient action on every lifted point is multiplication followed by the projection. -/
theorem action_act_lift {T : Over S} (g h : T ⟶ G.X) :
    Q.action.act g (h ≫ Q.projection) = (g * h) ≫ Q.projection := by
  let := Q.smooth_projection
  let := Q.surjective_projection
  let := Q.quasiCompact_projection
  exact Dynamic.flagQuotientSchemeAction_act_lift G (SubgroupFunctor.range i)
    Q.projection Q.fibers g h

/-- The actual action relation on the supplied quotient is smooth over any base. -/
theorem smooth_action_relation :
    Smooth (lift Q.action.hom (snd G.X Q.scheme)).left := by
  let := Q.smooth_projection
  let := Q.surjective_projection
  let := Q.quasiCompact_projection
  exact Dynamic.smooth_flagQuotientSchemeAction_relation G (SubgroupFunctor.range i)
    Q.projection Q.fibers

/-- The quotient itself is smooth if the original group scheme is smooth. -/
theorem smooth_structure [Smooth G.X.hom] : Smooth Q.scheme.hom := by
  let := Q.smooth_projection
  let := Q.surjective_projection
  have : Smooth (Q.projection.left ≫ Q.scheme.hom) := by rw [Over.w]; infer_instance
  exact Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
    Q.projection.left Q.scheme.hom

/-- The embedded subgroup fixes the identity coset on every relative test. -/
theorem identityCoset_isFixed : (Q.action.restrict i).IsFixed Q.identityCoset := by
  intro T b h
  simp only [SchemeAction.restrict_act, identityCoset, ← Category.assoc, MonObj.comp_one]
  rw [Q.action_act_lift, mul_one]
  apply (Q.fibers T _ _).mpr
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨h⁻¹, ?_⟩
  simp only [GrpObj.inv_comp, mul_one]

end HomogeneousQuotientFromEmbedding.HomogeneousQuotient

end Langlands.GroupScheme
