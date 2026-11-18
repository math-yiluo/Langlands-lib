import Langlands.GroupScheme.SimplyConnected.FactorTorusProjection

/-! # Original-field torus projections for actual normal almost-simple subgroups -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Actual compatible torus and original-field group/torus retractions onto a
normal factor. The all-test commutation criterion retains its product meaning. -/
structure NormalFactorTorusProjection (j : H ⟶ G) (t : T.toGrp ⟶ G)
    extends CompatibleNormalMaximalTorus j t where
  retraction : G ⟶ H
  inclusion_retraction : j ≫ retraction = 𝟙 H
  projection : T.toGrp ⟶ torus.toGrp
  projection_comp : projection ≫ subgroupHom = t ≫ retraction
  projection_section : CommGroupScheme.groupHom torusHom ≫ projection = 𝟙 torus.toGrp
  dominant : IsSchemeTheoreticallyDominant projection.hom.hom.left
  commute_iff : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ H.X) (y : U ⟶ G.X),
    Commute (x ≫ j.hom.hom) y ↔ Commute x (y ≫ retraction.hom.hom)

namespace SimplyConnectedAlmostSimpleProduct

variable [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (D : SimplyConnectedAlmostSimpleProduct G)
  (hH : IsAlmostSimple H) (j : H ⟶ G) (hj : IsClosedSubgroup j)
  (hn : (SubgroupFunctor.range j).IsNormal)

/-- The intrinsic normal-factor index identifies the supplied subgroup with
an actual factor of any product presentation, with the actual inclusion square. -/
def normalFactorIso : H ≅ D.factor (D.indexOfNormalAlmostSimple hH j hj hn) := by
  let i := D.indexOfNormalAlmostSimple hH j hj hn
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsClosedImmersion (D.inclusion i).hom.hom.left := D.isClosedSubgroup_inclusion i
  let h₁ : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, rfl⟩
  let h₂ : (SubgroupFunctor.range j).IsRepresentedBy (D.inclusion i) :=
    ⟨Over.mono_of_mono_left _, (D.range_eq_indexOfNormalAlmostSimple hH j hj hn).symm⟩
  exact h₁.isoOfIsRepresentedBy h₂

theorem normalFactorIso_hom_comp :
    (D.normalFactorIso hH j hj hn).hom ≫ D.inclusion (D.indexOfNormalAlmostSimple hH j hj hn) = j := by
  unfold normalFactorIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

theorem normalFactorIso_inv_comp :
    (D.normalFactorIso hH j hj hn).inv ≫ j = D.inclusion (D.indexOfNormalAlmostSimple hH j hj hn) := by
  let e := D.normalFactorIso hH j hj hn
  calc
    e.inv ≫ j = e.inv ≫ (e.hom ≫ D.inclusion (D.indexOfNormalAlmostSimple hH j hj hn)) :=
      congrArg (fun f => e.inv ≫ f) (D.normalFactorIso_hom_comp hH j hj hn).symm
    _ = _ := e.inv_hom_id_assoc _

/-- A chosen ambient maximal torus projects to an actual maximal torus of any
supplied almost-simple normal subgroup, with all maps over the original field. -/
def normalFactorTorusProjection (hG : IsConnectedReductive G)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t) : NormalFactorTorusProjection j t := by
  let i := D.indexOfNormalAlmostSimple hH j hj hn
  let e := D.normalFactorIso hH j hj hn
  let F := D.factorTorusProjection hG t ht i
  have he : e.inv ≫ j = D.inclusion i := D.normalFactorIso_inv_comp hH j hj hn
  have he' : e.hom ≫ D.inclusion i = j := D.normalFactorIso_hom_comp hH j hj hn
  refine {
    torus := F.torus
    subgroupHom := F.subgroupHom ≫ e.inv
    torusHom := F.torusHom
    isMaximalTorus := F.isMaximalTorus.comp_iso e.symm
    isClosedSubgroup := F.isClosedSubgroup
    comp_eq := ?_
    retraction := D.projection i ≫ e.inv
    inclusion_retraction := ?_
    projection := F.projection
    projection_comp := ?_
    projection_section := F.projection_section
    dominant := F.dominant
    commute_iff := ?_ }
  · rw [Category.assoc, he]
    exact F.comp_eq
  · calc
      j ≫ D.projection i ≫ e.inv = (e.hom ≫ D.inclusion i) ≫ D.projection i ≫ e.inv :=
        congrArg (fun f => f ≫ D.projection i ≫ e.inv) he'.symm
      _ = 𝟙 H := by
        rw [Category.assoc, ← Category.assoc (D.inclusion i),
          D.inclusion_projection, Category.id_comp, Iso.hom_inv_id]
  · rw [← Category.assoc, F.projection_comp, Category.assoc]
  · intro U x y
    have hde := D.commute_inclusion_iff i (x ≫ e.hom.hom.hom) y
    have hleft : (x ≫ e.hom.hom.hom) ≫ (D.inclusion i).hom.hom = x ≫ j.hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using congrArg (fun f => x ≫ f.hom.hom) he'
    rw [hleft] at hde
    rw [hde]
    constructor
    · intro h
      have h' := h.map ((yonedaGrp.map e.inv).app (Opposite.op U)).hom
      change Commute ((x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom)
        ((y ≫ (D.projection i).hom.hom) ≫ e.inv.hom.hom) at h'
      have hee : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 H.X :=
        congrArg (fun f => f.hom.hom) e.hom_inv_id
      simpa only [Category.assoc, hee, Category.comp_id, Grp.comp_hom_hom] using h'
    · intro h
      have h' := h.map ((yonedaGrp.map e.hom).app (Opposite.op U)).hom
      change Commute (x ≫ e.hom.hom.hom)
        ((y ≫ (D.projection i ≫ e.inv).hom.hom) ≫ e.hom.hom.hom) at h'
      simpa only [Grp.comp_hom_hom, Category.assoc, ← Grp.comp_hom_hom,
        Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id] using h'

end SimplyConnectedAlmostSimpleProduct

namespace NormalFactorTorusProjection

variable {j : H ⟶ G} {t : T.toGrp ⟶ G} (F : NormalFactorTorusProjection j t)

/-- The actual factor torus is split over every extension splitting the
prescribed ambient torus, by base change of its schematically dominant projection. -/
theorem isSplitTorus_baseChange (K : Type u) [Field K] [Algebra k K]
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp) :
    IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj F.torus).toGrp := by
  let b := algebraBaseMap k K
  have : IsAffine F.torus.X.left := SplittingAssembly.isAffine_of_isTorus _ F.isMaximalTorus.1
  let : IsAffineHom F.torus.toGrp.X.hom := inferInstance
  let : IsAffineHom ((CommGroupScheme.baseChange b).obj F.torus).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd F.torus.toGrp.X.hom b)
    infer_instance
  have hambient : IsTorus T.toGrp := ⟨K, inferInstance, inferInstance, hT⟩
  let : QuasiCompact T.toGrp.X.hom := hambient.quasiCompact
  have : QuasiCompact (F.projection.hom.hom.left ≫ F.torus.toGrp.X.hom) := by
    simpa only [Over.w] using (inferInstance : QuasiCompact T.toGrp.X.hom)
  let : QuasiCompact F.projection.hom.hom.left :=
    QuasiCompact.of_comp F.projection.hom.hom.left F.torus.toGrp.X.hom
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : IsSchemeTheoreticallyDominant F.projection.hom.hom.left := F.dominant
  exact hT.of_schematicallyDominant_hom ((GroupScheme.baseChange b).map F.projection)
    (isSchemeTheoreticallyDominant_baseChange b F.projection)

end NormalFactorTorusProjection
end Langlands.GroupScheme
