/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Adjunctions

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.HigherDirectImageLimitPresheafClassDescent

/-! # Classes in fibers of higher direct images under scheme limits

Source: Stacks Project, Tag 09Z1.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Every class in the limit higher direct image fiber comes from a stage.
Source: Stacks Project, Lemma 59.51.7, Tag 09Z1, proof
(blueprint: sbc-lem-higher-direct-image-limit-class-descent).

Proof:
1. Represent the fiber class on an affine etale neighborhood of the chosen point.
   The higher direct image presheaf theorem identifies its germ with a degree-p
   cohomology class on the pullback of the limit scheme to that neighborhood.
2. The pullbacks of the stages are qcqs since the neighborhood is affine and the
   structure maps are qcqs. Their transitions are affine and their limit is the
   pullback of the given limit. Pull back the sheaf system as well. Inverse image
   preserves colimits, so its colimit is the restriction of `colimit H`.
3. Place these sheaves in degree zero and apply complex cohomology continuity.
   Surjectivity of the cohomology colimit comparison represents the class at a
   stage. The higher direct image presheaf theorem turns this representative into
   a germ in the stage higher direct image, hence, using `eK`, a fiber element of
   `K.obj i`. Naturality of the presheaf identification and `hη` identify its image
   with the initial germ. This gives the required equality. -/
theorem exists_higherDirectImage_limit_fiber_rep {S : Scheme.{v}}
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
    [HasColimit K]
    (η : K ⟶ (Functor.const I).obj
      ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))))
    (hη : ∀ i : I, η.app i = (eK i).hom ≫
      abelianHigherDirectImageMap (c.π.app (op i)).left (D.obj (op i)).hom c.pt.hom
        (Over.w (c.π.app (op i))) p (F i) (colimit H)
        ((eH i).inv ≫ colimit.ι H i)) (s : S) :
    ∀ x : ((S.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).obj
      ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))),
      ∃ (i : I)
        (y : ((S.uliftPointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{v + 1})).obj (K.obj i)),
        (((S.uliftPointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{v + 1})).map (η.app i)) y = x := by
  classical
  let T := (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
    (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))
  let P := (uliftYoneda.{v + 1} ⋙
    (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1} ⋙
    upperStar AddCommGrpCat.{v + 1} c.pt.hom ⋙
    DerivedCategory.Plus.singleFunctor _ 0).op ⋙
      preadditiveYoneda.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H))⟦(p : ℤ)⟧)
  let Φ := S.uliftPointSmallEtale s
  have : LocallySmall.{v + 1} S.Etale := locallySmall_max.{v + 1, v, v + 1}
  obtain ⟨e, hlift⟩ := exists_higherDirectImage_limit_presheaf_class_cover
    D c hc F φ hφid hφcomp H eH hH p K eK η hη
  let τ : P ⟶ T.obj := toSheafify S.smallEtaleTopology P ≫ e.hom.hom
  have : Presheaf.IsLocallySurjective S.smallEtaleTopology τ := by
    dsimp [τ]
    infer_instance
  intro x
  obtain ⟨x', hx'⟩ := Φ.toPresheafFiber_map_surjective τ x
  obtain ⟨U, u, z, hz⟩ := Φ.toPresheafFiber_jointly_surjective (P := P) x'
  obtain ⟨R, hR, hRlift⟩ := hlift U z
  obtain ⟨V, f, hf, w, hw⟩ := Φ.jointly_surjective R hR u
  obtain ⟨i, y, hy⟩ := hRlift f hf
  refine ⟨i, Φ.toPresheafFiber V w (K.obj i).obj y, ?_⟩
  change Φ.presheafFiber.map (η.app i).hom
    (Φ.toPresheafFiber V w (K.obj i).obj y) = x
  rw [Φ.toPresheafFiber_naturality_apply, hy]
  change Φ.toPresheafFiber V w T.obj (T.obj.map f.op (τ.app (op U) z)) = x
  rw [Φ.toPresheafFiber_w_apply f w T.obj, hw,
    ← Φ.toPresheafFiber_naturality_apply τ U u, hz, hx']

end AlgebraicGeometry.Etale
