/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Adjunctions

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.HigherDirectImageLimitAffineClassRep

/-! # Descent of higher direct image cohomology-presheaf classes

Source: Stacks Project, Tag 09Z1
(blueprint: lem-sbc-higher-direct-image-limit-presheaf-class-cover).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Raw cohomology-presheaf classes locally descend to stage higher direct images.
Source: Stacks Project, Lemma 59.51.7, Tag 09Z1, cohomology comparison in its proof,
and Lemma 59.51.6, Tag 03Q8
(blueprint: lem-sbc-higher-direct-image-limit-presheaf-class-cover).

Proof:
1. Take the natural sheafification isomorphism e of Tag 03Q8. The presheaf P is
   the derived-Hom presentation of U ↦ H^p(U ×_S X, F); free abelian sheaves on
   representables corepresent sections, and derived adjunction identifies these
   Hom groups with the cohomology of the restriction to the pullback. Use this
   natural comparison, rather than an arbitrary abstract isomorphism.
2. Cover U by affine etale objects V. The schemes V ×_S X_i are qcqs because the
   maps X_i → S are qcqs and V is affine. Their transitions are affine by base
   change; their limit is V ×_S X. Restrict F_i and its transition maps to these
   pullbacks. Inverse image preserves colimits, so the restricted limit sheaf is
   the colimit of the restricted stage sheaves.
3. Regard the restricted sheaves as complexes concentrated in degree zero.
   Cohomology continuity on V makes each restriction of z the image of a class
   at some stage i. Send that class through the stage cohomology-presheaf map
   to a section of R^p g_i,* F_i, then through (eK i).inv to a section y of K_i.
4. The cohomology-presheaf comparison is natural for the derived adjunction unit
   and maps of coefficients: the stage-to-limit map takes the representing
   derived morphism to its pulled-back morphism followed by F_i → F. After
   applying degree-p homology this is abelianHigherDirectImageMap. Thus hη says
   that η_i(y) is exactly the image of z under toSheafify followed by e.hom,
   restricted to V. Generate a sieve from the affine cover. Restriction of y
   along further arrows preserves this equality by naturality of η, so every
   arrow of this covering sieve has the required lift.
-/
theorem exists_higherDirectImage_limit_presheaf_class_cover {S : Scheme.{v}}
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
    (η : K ⟶ (Functor.const I).obj
      ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))))
    (hη : ∀ i : I, η.app i = (eK i).hom ≫
      abelianHigherDirectImageMap (c.π.app (op i)).left (D.obj (op i)).hom c.pt.hom
        (Over.w (c.π.app (op i))) p (F i) (colimit H)
        ((eH i).inv ≫ colimit.ι H i)) :
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
    ∃ (e : (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj P ≅ T),
      ∀ (U : S.Etale) (z : P.obj (op U)),
        ∃ (R : Sieve U), R ∈ S.smallEtaleTopology U ∧
          ∀ {V : S.Etale} (f : V ⟶ U), R f →
            ∃ (i : I) (y : (K.obj i).obj.obj (op V)),
              (η.app i).hom.app (op V) y =
                T.obj.map f.op
                  ((toSheafify S.smallEtaleTopology P ≫ e.hom.hom).app (op U) z) := by
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
  obtain ⟨e, haffine⟩ := exists_higherDirectImage_limit_affine_class_rep
    D c hc F φ hφid hφcomp H eH hH p
  refine ⟨e, ?_⟩
  intro U z
  let 𝒰 := U.left.affineCover
  let V (j : 𝒰.I₀) : S.Etale :=
    Scheme.Etale.mk (𝒰.f j ≫ U.hom)
  let f (j : 𝒰.I₀) : V j ⟶ U :=
    MorphismProperty.Over.homMk (𝒰.f j)
  refine ⟨Sieve.ofArrows V f, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact 𝒰.iUnion_range
  · intro W g hg
    obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff V f g).mp hg
    have : IsAffine (V j).left := by
      change IsAffine (Spec _)
      infer_instance
    obtain ⟨i, y, hy⟩ := haffine (V j) (P.map (f j).op z)
    let y' := (eK i).inv.hom.app (op (V j)) y
    have hstage : (η.app i).hom.app (op (V j)) y' =
        (toSheafify S.smallEtaleTopology P ≫ e.hom.hom).app (op (V j))
          (P.map (f j).op z) := by
      rw [hη]
      dsimp only [y']
      have he := congrArg (fun t ↦ t.hom.app (op (V j))) (eK i).inv_hom_id
      have hey := ConcreteCategory.congr_hom he y
      change (eK i).hom.hom.app (op (V j))
        ((eK i).inv.hom.app (op (V j)) y) = y at hey
      change (abelianHigherDirectImageMap (c.π.app (op i)).left
        (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p (F i)
        (colimit H) ((eH i).inv ≫ colimit.ι H i)).hom.app (op (V j))
          ((eK i).hom.hom.app (op (V j)) ((eK i).inv.hom.app (op (V j)) y)) = _
      rw [hey]
      exact hy
    refine ⟨i, (K.obj i).obj.map a.op y', ?_⟩
    have hnat := (η.app i).hom.naturality_apply a.op y'
    rw [hnat, hstage]
    have hτ := (toSheafify S.smallEtaleTopology P ≫ e.hom.hom).naturality_apply
      (f j).op z
    rw [hτ]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl

end AlgebraicGeometry.Etale
