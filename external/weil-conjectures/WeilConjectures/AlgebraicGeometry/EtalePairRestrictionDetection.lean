/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Sites.Sheaf

/-! # A single qcqs overlap detects matching after any base change
Source: Stacks Project, Tags 03Q4 and 09YQ, overlap reduction. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Stacks Project, Tags 03Q4 and 09YQ, fibre-product overlap reduction.
(blueprint: lem-weil-pbc-etale-pair-restriction-detection).
Proof: take Z to be U ×_W V in the small étale category, with its projections p,q.
The maps to W are qcqs by cancellation against the qcqs structure map of W.
Base change and composition show that Z has qcqs structure map. Its projections
have equal composites to W. Base change along h preserves this fibre product.
For any a,a' with equal composites to the base change of W, the pullback universal
property supplies a map from Y to the base change of Z with composites a,a'.
Restrict the assumed equation along this map. Functoriality of the presheaf F
identifies its two sides with the restrictions along a,a'. This uses no covering,
limit cone, directed system, or sheaf gluing; functorial restriction suffices.
Empty overlaps and equal objects are included by the same universal property. -/
theorem etale_pair_restriction_detection
    {S : Scheme.{u}} (W U V : S.Etale)
    [QuasiCompact W.hom] [QuasiSeparated W.hom]
    [QuasiCompact U.hom] [QuasiSeparated U.hom]
    [QuasiCompact V.hom] [QuasiSeparated V.hom]
    (f : U ⟶ W) (g : V ⟶ W) :
    ∃ (Z : S.Etale) (p : Z ⟶ U) (q : Z ⟶ V),
      QuasiCompact Z.hom ∧ QuasiSeparated Z.hom ∧ p ≫ f = q ≫ g ∧
      ∀ (T : Scheme.{u}) (h : T ⟶ S)
        (F : Sheaf T.smallEtaleTopology (Type (u + 1)))
        (s : F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)))
        (t : F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj V))),
        F.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ h).map p).op s =
          F.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ h).map q).op t →
        ∀ (Y : T.Etale)
          (a : Y ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).obj U)
          (a' : Y ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).obj V),
          a ≫ (MorphismProperty.Over.pullback @Etale ⊤ h).map f =
            a' ≫ (MorphismProperty.Over.pullback @Etale ⊤ h).map g →
          F.obj.map a.op s = F.obj.map a'.op t := by
  classical
  have : QuasiCompact (g.left ≫ W.hom) := by
    rw [MorphismProperty.Over.w g]
    infer_instance
  let : QuasiCompact g.left := QuasiCompact.of_comp g.left W.hom
  have : QuasiSeparated (g.left ≫ W.hom) := by
    rw [MorphismProperty.Over.w g]
    infer_instance
  let : QuasiSeparated g.left := QuasiSeparated.of_comp g.left W.hom
  let Z : S.Etale := Scheme.Etale.mk (pullback.fst f.left g.left ≫ U.hom)
  let p : Z ⟶ U := MorphismProperty.Over.homMk (pullback.fst f.left g.left) rfl
  let q : Z ⟶ V := MorphismProperty.Over.homMk (pullback.snd f.left g.left) (by
    change pullback.snd f.left g.left ≫ V.hom =
      pullback.fst f.left g.left ≫ U.hom
    rw [← MorphismProperty.Over.w g, ← MorphismProperty.Over.w f,
      ← Category.assoc, ← pullback.condition, Category.assoc])
  have hpq : p ≫ f = q ≫ g := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.fst f.left g.left ≫ f.left = pullback.snd f.left g.left ≫ g.left
    exact pullback.condition
  have hqc : QuasiCompact Z.hom := by
    change QuasiCompact (pullback.fst f.left g.left ≫ U.hom)
    infer_instance
  have hqs : QuasiSeparated Z.hom := by
    change QuasiSeparated (pullback.fst f.left g.left ≫ U.hom)
    infer_instance
  refine ⟨Z, p, q, hqc, hqs, hpq, ?_⟩
  intro T h F s t heq Y a a' ha
  let A := a.left ≫ pullback.fst U.hom h
  let B := a'.left ≫ pullback.fst V.hom h
  have hAB : A ≫ f.left = B ≫ g.left := by
    have hh := congrArg (fun z ↦ z.left ≫ pullback.fst W.hom h) ha
    change (a.left ≫ ((MorphismProperty.Over.pullback @Etale ⊤ h).map f).left) ≫
        pullback.fst W.hom h =
      (a'.left ≫ ((MorphismProperty.Over.pullback @Etale ⊤ h).map g).left) ≫
        pullback.fst W.hom h at hh
    simpa [MorphismProperty.Over.pullback_map_left, Category.assoc, A, B] using hh
  let z := pullback.lift A B hAB
  have hz : z ≫ Z.hom = Y.hom ≫ h := by
    change z ≫ (pullback.fst f.left g.left ≫ U.hom) = _
    rw [← Category.assoc, pullback.lift_fst]
    dsimp [A]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun v ↦ v ≫ h) (MorphismProperty.Over.w a)
  let v : Y ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).obj Z :=
    MorphismProperty.Over.homMk (pullback.lift z Y.hom hz) (by simp)
  have hvp : v ≫ (MorphismProperty.Over.pullback @Etale ⊤ h).map p = a := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift z Y.hom hz ≫
      ((MorphismProperty.Over.pullback @Etale ⊤ h).map p).left = a.left
    apply pullback.hom_ext
    · simp only [Category.assoc, MorphismProperty.Over.pullback_map_left,
        pullback.lift_fst]
      change pullback.lift z Y.hom hz ≫
        (pullback.fst Z.hom h ≫ pullback.fst f.left g.left) = A
      rw [← Category.assoc, pullback.lift_fst]
      exact pullback.lift_fst A B hAB
    · simp only [Category.assoc, MorphismProperty.Over.pullback_map_left,
        pullback.lift_snd]
      exact (MorphismProperty.Over.w a).symm
  have hvq : v ≫ (MorphismProperty.Over.pullback @Etale ⊤ h).map q = a' := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift z Y.hom hz ≫
      ((MorphismProperty.Over.pullback @Etale ⊤ h).map q).left = a'.left
    apply pullback.hom_ext
    · simp only [Category.assoc, MorphismProperty.Over.pullback_map_left,
        pullback.lift_fst]
      change pullback.lift z Y.hom hz ≫
        (pullback.fst Z.hom h ≫ pullback.snd f.left g.left) = B
      rw [← Category.assoc, pullback.lift_fst]
      exact pullback.lift_snd A B hAB
    · simp only [Category.assoc, MorphismProperty.Over.pullback_map_left,
        pullback.lift_snd]
      exact (MorphismProperty.Over.w a').symm
  have hh := congrArg (F.obj.map v.op) heq
  simpa only [← comp_apply, ← Functor.map_comp, ← op_comp, hvp, hvq] using hh

end AlgebraicGeometry
