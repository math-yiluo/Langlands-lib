/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport

/-! # Diagonal sections for the étale-to-pro-étale comparison

## References

* Stacks Project, Tag 0GLZ, the identification of F with its comparison restriction
* Sites, Tags 03CB and 03CC
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

-- Local notation expands the diagonal formula; the public declaration introduces
-- no second copy of the downstream `proEtaleComparisonEtaleSection` definition.
set_option quotPrecheck false in
local notation:max "δ[" X "," F "," U "]" s:max =>
  (by
    let _ : (MorphismProperty.Over.pullback @Etale ⊤ (U).hom).IsContinuous
        ((X).smallGrothendieckTopology @Etale)
        ((U).left.smallGrothendieckTopology @Etale) :=
      Scheme.isContinuous_overPullback @Etale @Etale le_rfl (U).hom
    exact ((Scheme.etaleSetPullback (U).hom).obj F).obj.map
      (MorphismProperty.Over.homMk
        (pullback.lift (𝟙 (U).left) (𝟙 (U).left) (by simp)) (by simp) :
        Scheme.Etale.mk (𝟙 (U).left) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ (U).hom).obj U).op
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ (U).hom) (Type _)
        ((X).smallGrothendieckTopology @Etale)
        ((U).left.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op U) s)
  : ((Scheme.etaleSetPullback (U).hom).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 (U).left))))

private noncomputable abbrev b {S T : Scheme.{u}} (f : T ⟶ S) :=
  MorphismProperty.Over.pullback @Etale ⊤ f

private noncomputable def adj {S T : Scheme.{u}} (f : T ⟶ S) := by
  let _ : (b f).IsContinuous (S.smallGrothendieckTopology @Etale)
      (T.smallGrothendieckTopology @Etale) :=
    Scheme.isContinuous_overPullback @Etale @Etale le_rfl f
  exact Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (b f)
    (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Diagonal sections commute with a morphism of étale objects, using the same
terminal transport as the comparison sheaf's restriction law. -/
theorem proEtaleComparisonDiagonalSection_naturality {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (U V : X.Etale) (g : V ⟶ U) (s : F.obj.obj (op U)) :
    δ[X, F, V] (F.obj.map g.op s) =
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ g.left) (Type (u + 1))
        (U.left.smallGrothendieckTopology @Etale)
        (V.left.smallGrothendieckTopology @Etale)).unit.app
          ((Scheme.etaleSetPullback U.hom).obj F)).hom.app
            (op (Scheme.Etale.mk (𝟙 U.left))) ≫
        (etaleSetTerminalTransport U.hom g.left V.hom g.w F).inv)
          (δ[X, F, U] s) := by
  rcases U with ⟨⟨S, ⟨⟨⟩⟩, f⟩, hf⟩
  rcases V with ⟨⟨T, ⟨⟨⟩⟩, k⟩, hk⟩
  rcases g with ⟨⟨t, r, ht⟩, _, _⟩
  change S ⟶ X at f
  change T ⟶ X at k
  change T ⟶ S at t
  have ht' : t ≫ f = k := by simpa using ht
  subst k
  have hr : r = 𝟙 (Discrete.mk PUnit.unit) := Subsingleton.elim _ _
  subst r
  let _ : Etale f := hf
  let _ : Etale (t ≫ f) := hk
  let U := Scheme.Etale.mk f
  let V := Scheme.Etale.mk (t ≫ f)
  let q : V ⟶ U := MorphismProperty.Over.homMk t (by simp [U, V])
  let idS := Scheme.Etale.mk (𝟙 S)
  let idT := Scheme.Etale.mk (𝟙 T)
  let d : idS ⟶ (b f).obj U := MorphismProperty.Over.homMk
    (pullback.lift (𝟙 S) (𝟙 S) (by simp [U])) (by simp [idS])
  let d' : idT ⟶ (b (t ≫ f)).obj V := MorphismProperty.Over.homMk
    (pullback.lift (𝟙 T) (𝟙 T) (by simp [V])) (by simp [idT])
  let i : (b t).obj idS ≅ idT :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 S) t)) (Category.comp_id _)
  let m := i.inv ≫ (b t).map d
  let p := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) t f).inv.app U
  let LF := (Scheme.etaleSetPullback f).obj F
  let LTF := (Scheme.etaleSetPullback t).obj LF
  let LKF := (Scheme.etaleSetPullback (t ≫ f)).obj F
  let c := (Classical.choose etaleSetInverseImageCompositionUnits.2.2 X S T f t).hom.app F
  let ηf := ((adj f).unit.app F).hom
  let ηt := ((adj t).unit.app LF).hom
  let ηk := ((adj (t ≫ f)).unit.app F).hom
  have hn : LF.obj.map d.op ≫ ηt.app (op idS) =
      ηt.app (op ((b f).obj U)) ≫ LTF.obj.map ((b t).map d).op :=
    ηt.naturality d.op
  have hc : LTF.obj.map m.op ≫ c.hom.app (op idT) =
      c.hom.app (op ((b t).obj ((b f).obj U))) ≫ LKF.obj.map m.op :=
    c.hom.naturality m.op
  have hu : ηf.app (op U) ≫ ηt.app (op ((b f).obj U)) ≫
      c.hom.app (op ((b t).obj ((b f).obj U))) =
        ηk.app (op U) ≫ LKF.obj.map p.op := by
    apply ConcreteCategory.hom_ext
    intro z
    exact (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1 X S T f t F U z
  have hp : m ≫ p = d' ≫ (b (t ≫ f)).map q := by
    apply MorphismProperty.Over.Hom.ext
    change m.left ≫ p.left = d'.left ≫ ((b (t ≫ f)).map q).left
    rw [MorphismProperty.Over.pullback_map_left]
    dsimp [m, p, d, d', i, q, U, V, idS, idT,
      Scheme.Etale.mk, MorphismProperty.Over.mk]
    apply pullback.hom_ext
    · simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.isoMk_inv_left,
        asIso_inv, MorphismProperty.Over.pullback_map_left, MorphismProperty.Over.homMk_hom,
        Over.homMk_left, MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id,
        Category.comp_id, Category.assoc, pullbackLeftPullbackSndIso_hom_fst, limit.lift_π,
        PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left, IsIso.inv_comp_eq]
      erw [pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst]
      change pullback.fst (𝟙 S) t ≫ 𝟙 S = pullback.snd (𝟙 S) t ≫ 𝟙 T ≫ t
      rw [Category.id_comp]
      exact pullback.condition
    · simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.isoMk_inv_left,
        asIso_inv, MorphismProperty.Over.pullback_map_left, MorphismProperty.Over.homMk_hom,
        Over.homMk_left, MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id,
        Category.comp_id, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, limit.lift_π,
        PullbackCone.mk_π_app, IsIso.inv_comp_eq]
      erw [pullback.lift_snd]
  have key : ηf.app (op U) ≫ LF.obj.map d.op ≫ ηt.app (op idS) ≫
      LTF.obj.map i.inv.op ≫ c.hom.app (op idT) =
      F.obj.map q.op ≫ ηk.app (op V) ≫ LKF.obj.map d'.op := by
    calc
      _ = ηf.app (op U) ≫ ηt.app (op ((b f).obj U)) ≫
          LTF.obj.map m.op ≫ c.hom.app (op idT) := by
        rw [reassoc_of% hn]
        simp only [m, op_comp, Functor.map_comp, Category.assoc]
      _ = ηf.app (op U) ≫ ηt.app (op ((b f).obj U)) ≫
          c.hom.app (op ((b t).obj ((b f).obj U))) ≫ LKF.obj.map m.op := by
        rw [hc]
      _ = ηk.app (op U) ≫ LKF.obj.map (m ≫ p).op := by
        rw [reassoc_of% hu]
        simp only [op_comp, Functor.map_comp]
      _ = _ := by
        rw [reassoc_of% (ηk.naturality q.op)]
        rw [hp]
        simp only [op_comp, Functor.map_comp]
        rfl
  change LKF.obj.map d'.op (ηk.app (op V) (F.obj.map q.op s)) =
    c.hom.app (op idT) (LTF.obj.map i.inv.op
      (ηt.app (op idS) (LF.obj.map d.op (ηf.app (op U) s))))
  exact (ConcreteCategory.congr_hom key s).symm

end AlgebraicGeometry
