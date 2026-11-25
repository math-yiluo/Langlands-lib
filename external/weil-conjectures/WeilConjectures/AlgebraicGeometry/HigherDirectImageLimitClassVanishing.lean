/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.HigherDirectImageAffineSectionVanishing
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! # Classes in fibers of higher direct images under scheme limits

Source: Stacks Project, Tag 09Z1.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- A stage class vanishing in the limit fiber vanishes at a later stage.
Source: Stacks Project, Lemma 59.51.7, Tag 09Z1, proof
(blueprint: sbc-lem-higher-direct-image-limit-class-vanishing).

Proof:
1. Represent the given stage fiber class on an affine etale neighborhood of the
   chosen point using the higher direct image presheaf theorem and `eK`.
   Its image is zero as a germ. Shrink the neighborhood so that the induced
   cohomology class on the pullback of the limit scheme is zero.
2. Pull back the scheme and sheaf systems to this affine neighborhood. All schemes
   are qcqs, the transitions remain affine, and the cone remains a limit. Exact
   inverse image preserves the sheaf colimit and degree-zero complexes.
3. Apply injectivity of the complex cohomology continuity comparison. A class of
   a filtered colimit represented at a stage is zero exactly when it becomes zero
   at some later stage. Thus there exist `j` and `f : i ⟶ j` killing the restricted
   class. Naturality of the higher direct image presheaf identification and `hK`
   identify this map with the fiber of `K.map f`. Passing back to germs proves
   the desired vanishing. The compatibility equation `hη` is used in step 1. -/
theorem exists_higherDirectImage_limit_fiber_eq_zero {S : Scheme.{v}}
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
    [HasColimit H] (p : ℕ)
    (K : I ⥤ Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eK : ∀ i : I, K.obj i ≅
      (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+(((D.obj (op i)).hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (F i))))
    (hK : ∀ {i j : I} (f : i ⟶ j), K.map f =
      (eK i).hom ≫ abelianHigherDirectImageMap (D.map f.op).left
        (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
        (F i) (F j) (φ f) ≫ (eK j).inv)
    [HasColimit K]
    (η : K ⟶ (Functor.const I).obj
      ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))))
    (hη : ∀ i : I, η.app i = (eK i).hom ≫
      abelianHigherDirectImageMap (c.π.app (op i)).left (D.obj (op i)).hom c.pt.hom
        (Over.w (c.π.app (op i))) p (F i) (colimit H)
        ((eH i).inv ≫ colimit.ι H i)) (s : S) :
    ∀ (i : I)
      (y : ((S.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{v + 1})).obj (K.obj i)),
      (((S.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).map (η.app i)) y = 0 →
      ∃ (j : I) (f : i ⟶ j),
        (((S.uliftPointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{v + 1})).map (K.map f)) y = 0 := by
  classical
  have : PreservesFilteredColimitsOfSize.{v + 1, v + 1}
      (forget AddCommGrpCat.{v + 1}) := inferInstance
  have : LocallySmall.{v + 1} S.Etale := locallySmall_max.{v + 1}
  let Φ := S.uliftPointSmallEtale s
  intro i y hy
  obtain ⟨U, x, z, hz⟩ := Φ.toPresheafFiber_jointly_surjective (P := (K.obj i).obj) y
  let Q : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{v + 1} := ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
    (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))).obj
  have hzero : Φ.toPresheafFiber U x Q ((η.app i).hom.app (op U) z) =
      Φ.toPresheafFiber U x Q 0 := by
    rw [map_zero]
    dsimp only [Q]
    have hn := Φ.toPresheafFiber_naturality_apply (η.app i).hom U x z
    dsimp only [Functor.const_obj_obj] at hn
    exact hn.symm.trans (by rw [hz]; exact hy)
  obtain ⟨W, g, w, hw, hW⟩ := (Φ.toPresheafFiber_eq_iff' U x _ _).mp hzero
  have hWzero : (η.app i).hom.app (op W) ((K.obj i).obj.map g.op z) = 0 := by
    rw [NatTrans.naturality_apply]
    simpa only [Q, Functor.const_obj_obj, map_zero] using hW
  let A := Scheme.AffineEtale.Spec S
  obtain ⟨T, t, ⟨a⟩, u, hu⟩ := Φ.jointly_surjective _
    (A.is_cover_of_isCoverDense S.smallEtaleTopology W) w
  let V := A.obj a.obj
  have : IsAffine V.left := by
    dsimp only [V, A]
    rw [Scheme.AffineEtale.Spec_obj_left]
    infer_instance
  let v := Φ.fiber.map a.lift u
  let zV := (K.obj i).obj.map a.map.op ((K.obj i).obj.map g.op z)
  have hzV : Φ.toPresheafFiber V v (K.obj i).obj zV = y := by
    rw [Φ.toPresheafFiber_w_apply, Φ.toPresheafFiber_w_apply]
    have hv : Φ.fiber.map a.map v = w := by
      dsimp only [v]
      simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
        (congrArg (fun f ↦ Φ.fiber.map f u) a.fac).trans hu
    rw [hv, hw, hz]
  have hVzero : (η.app i).hom.app (op V) zV = 0 := by
    dsimp only [zV]
    rw [NatTrans.naturality_apply, hWzero, map_zero]
  obtain ⟨j, f, hf⟩ := exists_higherDirectImage_affine_section_eq_zero
    D c hc F φ hφid hφcomp H eH hH p K eK hK η hη V i zV hVzero
  refine ⟨j, f, ?_⟩
  rw [← hzV]
  change Φ.presheafFiber.map (K.map f).hom
    (Φ.toPresheafFiber V v (K.obj i).obj zV) = 0
  rw [Φ.toPresheafFiber_naturality_apply, hf, map_zero]

end AlgebraicGeometry.Etale
