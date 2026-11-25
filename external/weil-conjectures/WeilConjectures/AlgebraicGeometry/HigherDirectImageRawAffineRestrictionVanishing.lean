/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawAffineColimitComparisonInjective
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-! # Affine restrictions of raw classes eventually vanish

Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-higher-direct-image-raw-affine-restriction-vanishing).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
/-- An injective cocone comparison detects zero at a later stage.
Source: Mathlib `IsColimit.eq_iff'`, applied to x and zero. -/
private theorem exists_addCommGrp_stage_eq_zero {I : Type v} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] (K : I ⥤ AddCommGrpCat.{v + 1})
    (B : Cocone K) (hinj : Function.Injective (colimit.desc K B))
    (i : I) (x : K.obj i) (h : B.ι.app i x = 0) :
    ∃ (j : I) (f : i ⟶ j), K.map f x = 0 := by
  have : PreservesFilteredColimitsOfSize.{v, v} (forget AddCommGrpCat.{v + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{v, v + 1, v, v + 1} _
  change (B.ι.app i : K.obj i ⟶ B.pt).hom x = 0 at h
  have hx : colimit.ι K i x = colimit.ι K i 0 := by
    apply hinj
    change (colimit.ι K i ≫ colimit.desc K B) x =
      (colimit.ι K i ≫ colimit.desc K B) 0
    rw [colimit.ι_desc]
    change (B.ι.app i : K.obj i ⟶ B.pt).hom x =
      (B.ι.app i : K.obj i ⟶ B.pt).hom 0
    exact h.trans (map_zero _).symm
  obtain ⟨j, f, hf⟩ := ((colimit.isColimit K).eq_iff' x 0).mp hx
  exact ⟨j, f, by simpa only [map_zero] using hf⟩


set_option backward.isDefEq.respectTransparency true in
/-- On an affine etale test object a zero raw limit class dies at a later stage.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-higher-direct-image-raw-affine-restriction-vanishing).

Proof: Commute raw pullback with restriction to W by the naturality of inverse-image
composition and the comparison with the single functor. Base change the cone to W.
Since W is affine, its base changes with the qcqs stage schemes are qcqs; affine
transition maps and the limit property are preserved by base change. Restrict the
coefficient system; inverse image preserves its colimit and its coherence maps.
Place every coefficient sheaf in degree zero. Derived adjunction for etale
restriction identifies the raw Hom groups with cohomology on these base changes:
the free abelian sheaf on W represents sections, and the exact left adjoint of
restriction makes this identification compatible with pullback and coefficients.
Apply complex cohomology continuity (Tag 0EZM) with lower bound zero. Its canonical
colimit comparison is injective. The filtered abelian-group colimit equality
criterion therefore gives j and i → j with zero image of the restricted class.
The single and shift comparisons identify that image with the stated raw map.
Naturality of raw pullback with restriction then preserves this same zero class
on every V → W: the restrictions are precomposition, and the inverse-image
composition and single-functor comparisons are natural transformations. Their
naturality squares, mapped into the derived category, commute with this
precomposition. Thus the stage j and arrow obtained above work on all further
restrictions. Degree zero is section continuity; the empty affine object has zero group. -/
theorem exists_higherDirectImage_raw_affine_restriction_eq_zero {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ) (U : S.Etale) (i : I)
    (z : (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op U))
    (W : S.Etale) (q : W ⟶ U) [IsAffine W.left]
    (hz : (abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)).map q.op
      (abelianHigherDirectImageRawPullback (c.π.app (op i)).left
        (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p (F i)
        (colimit H) ((eH i).inv ≫ colimit.ι H i) U z) = 0) :
    ∃ (j : I) (f : i ⟶ j), ∀ (V : S.Etale) (a : V ⟶ W),
      abelianHigherDirectImageRawPullback (D.map f.op).left (D.obj (op i)).hom
        (D.obj (op j)).hom (Over.w (D.map f.op)) p (F i) (F j) (φ f) V
          ((abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).map
            (a ≫ q).op z) = 0 := by
  classical
  let P := abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)
  let Q := abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)
  let t := P.map q.op z
  obtain ⟨d⟩ :=
    exists_raw_affine_colimit_comparison_injective D c hc F φ hφid hφcomp H eH hH p W
  have ht : (d.β i).app (op W) t = 0 := by
    have hn := congrArg (fun g => g z) ((d.β i).naturality q.op)
    change (d.β i).app (op W) (P.map q.op z) = Q.map q.op ((d.β i).app (op U) z) at hn
    rw [d.hβ i U z] at hn
    exact hn.trans hz
  have hx : d.B.ι.app i ((d.eStage i).hom t) = 0 := by
    rw [d.hleg i t, ht, map_zero]
  obtain ⟨j, f, hf⟩ := exists_addCommGrp_stage_eq_zero d.K d.B d.hinj i
    ((d.eStage i).hom t) hx
  have hzero : (d.eStage j).hom ((d.τ f).app (op W) t) = 0 := by
    rw [← d.htrans f t]
    exact hf
  have hraw := congrArg (d.eStage j).inv hzero
  simp only [Iso.hom_inv_id_apply, map_zero] at hraw
  refine ⟨j, f, ?_⟩
  intro V a
  rw [← d.hτ f V]
  have hn := congrArg (fun g => g t) ((d.τ f).naturality a.op)
  change (d.τ f).app (op V) (P.map a.op t) =
    (abelianHigherDirectImageRawPresheaf (D.obj (op j)).hom p (F j)).map a.op
      ((d.τ f).app (op W) t) at hn
  simp only [op_comp, Functor.map_comp, AddCommGrpCat.comp_apply]
  change (d.τ f).app (op V) (P.map a.op t) = 0
  rw [hn, hraw, map_zero]

end AlgebraicGeometry.Etale
