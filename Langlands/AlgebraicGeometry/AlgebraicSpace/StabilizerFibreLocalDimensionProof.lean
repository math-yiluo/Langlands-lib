import Langlands.AlgebraicGeometry.AlgebraicSpace.StabilizerFibreLocalDimensionStatement
import Langlands.AlgebraicGeometry.SchemeLocalDimensionBaseChangeProof

/-!
# Stabilizer fibres are equidimensional: proof

Two points of one fibre of the stabilizer scheme come from a single point of the fibre
product of the stabilizer with itself over `V`. Over the residue field `Ω` of that point
both become sections of the base change of the stabilizer to `Spec Ω`, and left
translation by the quotient of their group components is an automorphism of this base
change carrying one section to the other. Base change preserves relative local dimension,
so the two points have the same local dimension in their fibre.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction)
open Langlands.AlgebraicGeometry.SchemeFiberGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace StabilizerFibre

/-- Over a one-point base the relative local dimension is the local dimension of the
source. -/
theorem relativeTopologicalKrullDimAt_of_subsingleton {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Subsingleton Y] (x : X) :
    relativeTopologicalKrullDimAt f x = topologicalKrullDimAt x := by
  rw [relativeTopologicalKrullDimAt_eq_preimage_singleton]
  have hU : f ⁻¹' {f x} = Set.univ := Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
  exact topologicalKrullDimAt_homeomorph
    ((Homeomorph.setCongr hU).trans (Homeomorph.Set.univ X)) _

variable {S : Scheme.{u}} {G : GroupScheme S} {V : Over S} (a : SchemeAction G V)

/-- The stabilizer scheme of `a`, the base change of the action graph along the
diagonal of `V`. -/
abbrev Stab : Over S :=
  Limits.pullback (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))

/-- The projection of the stabilizer scheme to `V`. -/
abbrev proj : Stab a ⟶ V :=
  pullback.snd (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))

/-- The group component of a point of the stabilizer scheme. -/
def group {T : Over S} (q : T ⟶ Stab a) : T ⟶ G.X :=
  q ≫ pullback.fst (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V)) ≫ fst G.X V

theorem group_comp {T T' : Over S} (b : T' ⟶ T) (q : T ⟶ Stab a) :
    group a (b ≫ q) = b ≫ group a q := by
  simp only [group, Category.assoc]

/-- The point of `G × V` underlying a point of the stabilizer is its group component
together with its image in `V`. -/
theorem comp_pullback_fst {T : Over S} (q : T ⟶ Stab a) :
    q ≫ pullback.fst (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V)) =
      lift (group a q) (q ≫ proj a) := by
  have h := congrArg (fun φ => q ≫ φ ≫ snd V V)
    (pullback.condition (f := lift a.hom (snd G.X V)) (g := lift (𝟙 V) (𝟙 V)))
  simp only [Category.assoc, lift_snd, Category.comp_id] at h
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, group]
  · simpa only [Category.assoc, lift_snd] using h

/-- The group component of a point of the stabilizer fixes its image in `V`. -/
theorem act_group {T : Over S} (q : T ⟶ Stab a) :
    a.act (group a q) (q ≫ proj a) = q ≫ proj a := by
  have h := congrArg (fun φ => q ≫ φ ≫ fst V V)
    (pullback.condition (f := lift a.hom (snd G.X V)) (g := lift (𝟙 V) (𝟙 V)))
  simp only [Category.assoc, lift_fst, Category.comp_id] at h
  rw [SchemeAction.act, ← comp_pullback_fst, Category.assoc]
  exact h

/-- The point of the stabilizer given by a group point fixing a point of `V`. -/
def mk {T : Over S} (g : T ⟶ G.X) (n : T ⟶ V) (h : a.act g n = n) : T ⟶ Stab a :=
  pullback.lift (lift g n) n (by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, lift_fst, Category.comp_id, SchemeAction.act] using h
    · simp only [Category.assoc, lift_snd, Category.comp_id])

@[simp] theorem mk_proj {T : Over S} (g : T ⟶ G.X) (n : T ⟶ V) (h : a.act g n = n) :
    mk a g n h ≫ proj a = n :=
  pullback.lift_snd _ _ _

@[simp] theorem group_mk {T : Over S} (g : T ⟶ G.X) (n : T ⟶ V) (h : a.act g n = n) :
    group a (mk a g n h) = g := by
  simp only [group, mk, pullback.lift_fst_assoc, lift_fst]

/-- Points of the stabilizer are determined by their group components and their images
in `V`. -/
theorem hom_ext {T : Over S} {q q' : T ⟶ Stab a} (hg : group a q = group a q')
    (hn : q ≫ proj a = q' ≫ proj a) : q = q' := by
  apply pullback.hom_ext
  · rw [comp_pullback_fst, comp_pullback_fst, hg, hn]
  · exact hn

/-- A group point fixing `t` also has inverse fixing `t`. -/
theorem act_inv_of_act {T : Over S} {h : T ⟶ G.X} {t : T ⟶ V} (hh : a.act h t = t) :
    a.act h⁻¹ t = t := by
  calc
    a.act h⁻¹ t = a.act h⁻¹ (a.act h t) := by rw [hh]
    _ = t := by rw [← SchemeAction.act_mul, inv_mul_cancel, SchemeAction.act_one]

variable {W : Over S} (t : W ⟶ V)

/-- Left translation by a point `h` of `G` over `W` fixing `t`, on the base change of the
stabilizer scheme along `t`: `(g, w) ↦ (h(w) g, w)`. -/
def translate (h : W ⟶ G.X) (hh : a.act h t = t) :
    Limits.pullback (proj a) t ⟶ Limits.pullback (proj a) t :=
  pullback.lift
    (mk a ((pullback.snd (proj a) t ≫ h) * group a (pullback.fst (proj a) t))
      (pullback.fst (proj a) t ≫ proj a) (by
        rw [SchemeAction.act_mul, act_group, pullback.condition (f := proj a) (g := t),
          ← SchemeAction.naturality, hh]))
    (pullback.snd (proj a) t) (by
      rw [mk_proj, pullback.condition])

@[reassoc (attr := simp)] theorem translate_fst (h : W ⟶ G.X) (hh : a.act h t = t) :
    translate a t h hh ≫ pullback.fst (proj a) t =
      mk a ((pullback.snd (proj a) t ≫ h) * group a (pullback.fst (proj a) t))
        (pullback.fst (proj a) t ≫ proj a) (by
          rw [SchemeAction.act_mul, act_group, pullback.condition (f := proj a) (g := t),
            ← SchemeAction.naturality, hh]) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem translate_snd (h : W ⟶ G.X) (hh : a.act h t = t) :
    translate a t h hh ≫ pullback.snd (proj a) t = pullback.snd (proj a) t :=
  pullback.lift_snd _ _ _

theorem translate_comp (h h' : W ⟶ G.X) (hh : a.act h t = t) (hh' : a.act h' t = t) :
    translate a t h hh ≫ translate a t h' hh' =
      translate a t (h' * h) (by rw [SchemeAction.act_mul, hh, hh']) := by
  apply pullback.hom_ext
  · apply hom_ext a
    · rw [Category.assoc, translate_fst, translate_fst, group_comp, group_mk, group_mk,
        MonObj.comp_mul, MonObj.comp_mul, translate_snd_assoc, ← group_comp, translate_fst,
        group_mk, mul_assoc]
    · simp only [Category.assoc, translate_fst_assoc, mk_proj]
  · simp only [Category.assoc, translate_snd]

theorem translate_eq_id (h : W ⟶ G.X) (hh : a.act h t = t) (h1 : h = 1) :
    translate a t h hh = 𝟙 _ := by
  subst h1
  apply pullback.hom_ext
  · apply hom_ext a
    · simp only [translate_fst, group_mk, MonObj.comp_one, one_mul, Category.id_comp]
    · simp only [translate_fst, mk_proj, Category.id_comp]
  · simp only [translate_snd, Category.id_comp]

/-- Translation is an automorphism, with inverse the translation by the inverse. -/
def translateIso (h : W ⟶ G.X) (hh : a.act h t = t) :
    Limits.pullback (proj a) t ≅ Limits.pullback (proj a) t where
  hom := translate a t h hh
  inv := translate a t h⁻¹ (act_inv_of_act a hh)
  hom_inv_id := by
    rw [translate_comp]
    exact translate_eq_id a t _ _ (inv_mul_cancel h)
  inv_hom_id := by
    rw [translate_comp]
    exact translate_eq_id a t _ _ (mul_inv_cancel h)

/-- Two points of one fibre of the stabilizer projection have the same local dimension
in that fibre. -/
theorem relativeTopologicalKrullDimAt_eq_of_proj_eq [LocallyOfFiniteType (proj a).left]
    (x y : (Stab a).left) (hxy : (proj a).left x = (proj a).left y) :
    relativeTopologicalKrullDimAt (proj a).left x =
      relativeTopologicalKrullDimAt (proj a).left y := by
  obtain ⟨z, hzx, hzy⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  let p0 := (Limits.pullback (proj a).left (proj a).left).fromSpecResidueField z
  let px := p0 ≫ pullback.fst (proj a).left (proj a).left
  let py := p0 ≫ pullback.snd (proj a).left (proj a).left
  have hpσ : px ≫ (proj a).left = py ≫ (proj a).left := by
    simp only [px, py, Category.assoc, pullback.condition]
  let W : Over S := Over.mk (px ≫ (Stab a).hom)
  let qx : W ⟶ Stab a := Over.homMk px rfl
  let qy : W ⟶ Stab a := Over.homMk py (by
    change py ≫ (Stab a).hom = px ≫ (Stab a).hom
    rw [← Over.w (proj a), ← Category.assoc, ← Category.assoc, hpσ])
  have hq : qx ≫ proj a = qy ≫ proj a := by
    apply Over.OverMorphism.ext
    simpa only [Over.comp_left, qx, qy, Over.homMk_left] using hpσ
  let t := qx ≫ proj a
  have hfy : a.act (group a qy) t = t := by
    rw [show t = qy ≫ proj a from hq]
    exact act_group a qy
  let h := group a qx * (group a qy)⁻¹
  have hh : a.act h t = t := by
    rw [SchemeAction.act_mul, act_inv_of_act a hfy]
    exact act_group a qx
  let sx : W ⟶ Limits.pullback (proj a) t := pullback.lift qx (𝟙 W) (by
    simp only [Category.id_comp, t])
  let sy : W ⟶ Limits.pullback (proj a) t := pullback.lift qy (𝟙 W) (by
    simp only [Category.id_comp, t, hq])
  have hsx_fst : sx ≫ pullback.fst (proj a) t = qx := pullback.lift_fst _ _ _
  have hsx_snd : sx ≫ pullback.snd (proj a) t = 𝟙 W := pullback.lift_snd _ _ _
  have hsy_fst : sy ≫ pullback.fst (proj a) t = qy := pullback.lift_fst _ _ _
  have hsy_snd : sy ≫ pullback.snd (proj a) t = 𝟙 W := pullback.lift_snd _ _ _
  have hs : sy ≫ translate a t h hh = sx := by
    apply pullback.hom_ext
    · apply hom_ext a
      · rw [hsx_fst, Category.assoc, translate_fst, group_comp, group_mk, MonObj.comp_mul,
          ← Category.assoc sy, hsy_snd, Category.id_comp, ← group_comp, hsy_fst]
        exact inv_mul_cancel_right _ _
      · simp only [Category.assoc, translate_fst_assoc, mk_proj, reassoc_of% hsy_fst,
          reassoc_of% hsx_fst]
        exact hq.symm
    · simp only [Category.assoc, translate_snd, hsy_snd, hsx_snd]
  have sq : IsPullback (pullback.fst (proj a) t).left (pullback.snd (proj a) t).left
      (proj a).left t.left :=
    (IsPullback.of_hasPullback (proj a) t).map (Over.forget S)
  have : Subsingleton W.left :=
    inferInstanceAs (Subsingleton (Spec ((Limits.pullback (proj a).left
      (proj a).left).residueField z)))
  have key (s : W ⟶ Limits.pullback (proj a) t) (w : W.left) :
      relativeTopologicalKrullDimAt (proj a).left ((pullback.fst (proj a) t).left (s.left w)) =
        topologicalKrullDimAt (s.left w) := by
    rw [← relativeTopologicalKrullDimAt_baseChange sq]
    exact relativeTopologicalKrullDimAt_of_subsingleton _ _
  let w0 : W.left := IsLocalRing.closedPoint _
  have hx : (pullback.fst (proj a) t).left (sx.left w0) = x := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, pullback.lift_fst]
    change (p0 ≫ pullback.fst (proj a).left (proj a).left) w0 = x
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hzx]
  have hy : (pullback.fst (proj a) t).left (sy.left w0) = y := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, pullback.lift_fst]
    change (p0 ≫ pullback.snd (proj a).left (proj a).left) w0 = y
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hzy]
  have hτ : (translate a t h hh).left (sy.left w0) = sx.left w0 := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hs]
  rw [← hx, ← hy, key, key, ← hτ]
  exact (topologicalKrullDimAt_homeomorph
    (Scheme.homeoOfIso ((Over.forget S).mapIso (translateIso a t h hh))) _).symm

/-- The stabilizer projection is locally of finite type when `G` is: it is the base
change of the diagonal of `V`, an immersion, followed by the projection `G × V → V`, a
base change of `G → S`. The proof is Worker 79's `locallyOfFiniteType_stabilizer` from
their draft for Task 5217. -/
theorem locallyOfFiniteType_proj (hG : LocallyOfFiniteType G.X.hom) :
    LocallyOfFiniteType (proj a).left := by
  have hsnd : LocallyOfFiniteType (snd G.X V).left := by
    rw [Over.snd_left]
    infer_instance
  have hgraph : LocallyOfFiniteType (lift a.hom (snd G.X V)).left := by
    have h : (lift a.hom (snd G.X V)).left ≫ (snd V V).left = (snd G.X V).left := by
      rw [← Over.comp_left, lift_snd]
    rw [← h] at hsnd
    exact locallyOfFiniteType_of_comp _ (snd V V).left
  have e := PreservesPullback.iso_hom_snd (Over.forget S)
    (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))
  change (PreservesPullback.iso (Over.forget S) _ _).hom ≫ pullback.snd _ _ =
    (pullback.snd (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))).left at e
  rw [← e]
  have h1 : LocallyOfFiniteType ((Over.forget S).map (lift a.hom (snd G.X V))) := hgraph
  have h2 : LocallyOfFiniteType (pullback.snd ((Over.forget S).map (lift a.hom (snd G.X V)))
      ((Over.forget S).map (lift (𝟙 V) (𝟙 V)))) := inferInstance
  infer_instance

end StabilizerFibre

open StabilizerFibre in
/-- Stacks Lemma 39.8.1 for the fibres of the stabilizer scheme of a group action. -/
theorem stabilizerFibreLocalDimension : StabilizerFibreLocalDimensionStatement.{u} := by
  intro S G V a hG σ x
  have : LocallyOfFiniteType σ.left := locallyOfFiniteType_proj a hG
  apply le_antisymm (topologicalKrullDimAt_le _)
  rw [topologicalKrullDim_eq_iSup_at]
  refine iSup_le fun p => ?_
  rw [← relativeTopologicalKrullDimAt_fiberι σ.left (σ.left x) p]
  exact (relativeTopologicalKrullDimAt_eq_of_proj_eq a _ x
    (σ.left.fiberHomeo (σ.left x) p).2).le

end Langlands.AlgebraicGeometry.AlgebraicSpace
