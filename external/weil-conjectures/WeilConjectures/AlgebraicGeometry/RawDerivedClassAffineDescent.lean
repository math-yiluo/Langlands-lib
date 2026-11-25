/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import WeilConjectures.AlgebraicGeometry.CofilteredAffineEtaleModel
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import WeilConjectures.AlgebraicGeometry.FixedDerivedCohomologyDiagram
import WeilConjectures.AlgebraicGeometry.RawFixedDerivedComparisonIsIso
import WeilConjectures.AlgebraicGeometry.RawFixedDerivedComparisonNaturality
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Descent of raw classes with bounded-below coefficients

Source: Stacks Project, Tags 0EYL, 0EYM and 0GIT.
(blueprint: lem-sc-raw-derived-class-affine-descent).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

noncomputable local instance rawDerivedClassAffineDescentHasShift (T : Scheme.{u}) :
    HasShift (DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) ℤ :=
  inferInstance

attribute [local irreducible] restrictedOverCohomologyMap
  cartesianDerivedImageMap cartesianChartCohomologyLift cartesianChartCohomologyIso
  upperStar upperStarCompDerivedPlus rawFixedDerivedComparison
  rawRestrictedDerivedPullback

set_option backward.isDefEq.respectTransparency false

private theorem cancel_transport {C : Type*} [Category C] {A A' B B' : C}
    (e : A' ≅ A) (d : B ≅ B') (f : A ⟶ B) (z : A' ⟶ B')
    (h : f ≫ d.hom = e.inv ≫ z) : z ≫ d.inv = e.hom ≫ f := by
  have hh := congrArg (fun t ↦ e.hom ≫ t ≫ d.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    using hh.symm

set_option maxRecDepth 2048 in
private theorem raw_chart_transport {B Y Y' : Scheme.{u}}
    (a : Y ⟶ B) (b : Y' ⟶ Y) (a' : Y' ⟶ B) (w : a' = b ≫ a)
    (U : B.Etale) (V : Y'.Etale) (r : V.left ⟶ U.left)
    (hr : IsPullback r V.hom U.hom a')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (e : (D+((b)^*[AddCommGrpCat.{u + 1}])).obj K ≅ K') (q : ℤ)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree Y').obj V) ⟶ K'⟦q⟧)
    (y : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj U)) ⟶ K⟦q⟧)
    (hy : rawRestrictedDerivedPullback b a a' w.symm K K' e.hom q U y =
      (DerivedCategory.Plus.singleFunctor _ 0).map
        (abelianFreeRepresentablePullbackSquareIso a' U V r hr).inv ≫ z) :
    z ≫ (shiftFunctor _ q).map e.inv =
      cartesianChartClassPullback a b a' w U V r hr K q y := by
  let eF := (DerivedCategory.Plus.singleFunctor _ 0).mapIso
    (abelianFreeRepresentablePullbackSquareIso a' U V r hr)
  let t := (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} b a a' w).hom.app
        ((abelianComparisonFree B).obj U)) ≫
    (((b)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    (D+((b)^*[AddCommGrpCat.{u + 1}])).map y ≫
    ((D+((b)^*[AddCommGrpCat.{u + 1}])).commShiftIso q).hom.app K
  have ht : t ≫ (shiftFunctor _ q).map e.hom = eF.inv ≫ z := by
    unfold rawRestrictedDerivedPullback at hy
    simpa only [t, eF, Functor.mapIso_inv, Category.assoc] using hy
  change z ≫ (shiftFunctor _ q).map e.inv = eF.hom ≫ t
  exact cancel_transport eF ((shiftFunctor _ q).mapIso e) t z ht

-- Constructing the chart diagram and its limiting cone needs a larger elaboration budget.
/-- A raw derived class descends with its coefficient complex fixed at the original stage.

Source: Stacks Project, Tags 0EYL and 0GIT.
(blueprint: lem-sc-raw-derived-class-affine-descent).

Proof: Restrict the diagram to arrows into i. Descend V to an affine etale object
at a stage j using finite presentation. The base changes of this object form a
limiting diagram of qcqs schemes with affine transitions. Pull back the fixed
bounded-below complex K to this diagram and apply derived etale cohomology
continuity in degree q. A raw Hom from the degree-zero free representable computes
this hypercohomology: use a bounded-below injective representative of K and the
free-representable sections adjunction. Surjectivity of the filtered colimit map
gives a stage l and a class y. Inverse-image composition, the single comparison
and the shift comparison identify its image with the displayed chart pullback.
The equations defining the cone give the displayed coefficient isomorphism.
No direct image, exchange map, cartesian source, or restricted sheaf cohomology
is involved. Empty V and q=0 are included by the same adjunction and continuity.
-/
theorem exists_rawDerivedClass_affine_descent
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (q : ℕ) (i : I) (V : c.pt.left.Etale) [IsAffine V.left]
    (K : DerivedCategory.Plus (Sheaf (D.obj i).left.smallEtaleTopology
      AddCommGrpCat.{u + 1}))
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj V) ⟶
        ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj K)⟦(q : ℤ)⟧) :
    ∃ (j : I) (W : (D.obj j).left.Etale) (_ : IsAffine W.left)
      (r : V.left ⟶ W.left)
      (hr : IsPullback r V.hom W.hom (c.π.app j).left)
      (l : Over j) (b : l.left ⟶ i)
      (y : (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((((D.map l.hom).left)^*[AddCommGrpCat.{u + 1}]).obj
          ((abelianComparisonFree (D.obj j).left).obj W)) ⟶
        ((D+(((D.map b).left)^*[AddCommGrpCat.{u + 1}])).obj K)⟦(q : ℤ)⟧),
      z ≫ (shiftFunctor _ (q : ℤ)).map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
            (c.π.app l.left).left (D.map b).left (c.π.app i).left
            (congrArg (fun t ↦ t.left) (c.w b)).symm).hom.app K) =
        cartesianChartClassPullback (D.map l.hom).left (c.π.app l.left).left
          (c.π.app j).left (congrArg (fun t ↦ t.left) (c.w l.hom)).symm
          W V r hr _ (q : ℤ) y := by
  classical
  let E := D ⋙ Over.forget (Spec (.of k))
  let cE : Cone E := (Over.forget _).mapCone c
  have hcomp (x : I) : CompactSpace (E.obj x) := by
    dsimp [E]
    exact QuasiCompact.compactSpace_of_compactSpace (D.obj x).hom
  have hqs (x : I) : QuasiSeparatedSpace (E.obj x) := by
    dsimp [E]
    exact quasiSeparatedSpace_of_quasiSeparated (D.obj x).hom
  have (x y : I) (a : x ⟶ y) : IsAffineHom (E.map a) :=
    inferInstanceAs (IsAffineHom (D.map a).left)
  let E' := Over.forget i ⋙ E
  let c' := cE.whisker (Over.forget i)
  have hc' : IsLimit c' :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) cE).symm hc
  have (x : Over i) : CompactSpace (E'.obj x) := hcomp x.left
  have (x : Over i) : QuasiSeparatedSpace (E'.obj x) := hqs x.left
  have (x y : Over i) (a : x ⟶ y) : IsAffineHom (E'.map a) :=
    inferInstanceAs (IsAffineHom (D.map a.left).left)
  obtain ⟨j, W, hW, r, hr⟩ :=
    Scheme.exists_affineEtale_model_of_cofiltered E' c' hc' V
  change (D.obj j.left).left.Etale at W
  let := hW
  have hr' : IsPullback r V.hom W.hom (c.π.app j.left).left := hr
  let A := Over.post (X := j.left) E
  let cA := cE.overPost j.left
  let M : Over j.left ⥤ Scheme.{u} :=
    { obj := fun l ↦ pullback W.hom (E.map l.hom)
      map := fun {l m} f ↦ rawAffineRestrictedMap (E.map f.left)
        (E.map m.hom) (E.map l.hom) (by rw [← E.map_comp, Over.w f]) W
      map_id := by
        intro l
        apply pullback.hom_ext <;> simp [rawAffineRestrictedMap]
      map_comp := by
        intro l m n f g
        apply pullback.hom_ext <;> simp [rawAffineRestrictedMap, Category.assoc] }
  let cM : Cone M :=
    { pt := pullback W.hom (cE.π.app j.left)
      π :=
        { app := fun l ↦ rawAffineRestrictedMap (cE.π.app l.left)
            (E.map l.hom) (cE.π.app j.left) (cE.w l.hom) W
          naturality := by
            intro l m f
            apply pullback.hom_ext <;>
              simp [M, rawAffineRestrictedMap, Category.assoc, cE.w f.left] } }
  have hcA : IsLimit ((Over.forget _).mapCone cA) := by
    exact (Functor.Initial.isLimitWhiskerEquiv (Over.forget j.left) cE).symm hc
  have hcM : IsLimit cM := by
    let P := Over.pullback W.hom ⋙ Over.forget W.left
    let eM : A ⋙ P ≅ M := NatIso.ofComponents
      (fun l ↦ pullbackSymmetry (E.map l.hom) W.hom) (by
      intro l m f
      apply pullback.hom_ext <;>
        simp [A, P, M, Over.post, rawAffineRestrictedMap, pullback.map,
          pullbackSymmetry_hom_comp_snd_assoc, Category.assoc])
    have : IsConnected (Over j.left) := IsCofiltered.isConnected _
    have : PreservesLimitsOfShape (Over j.left) P := by dsimp only [P]; infer_instance
    have hh := isLimitOfPreserves P (isLimitOfReflects (Over.forget _) hcA)
    apply ((IsLimit.postcomposeHomEquiv eM (P.mapCone cA)).symm hh).ofIsoLimit
    refine Cone.ext (pullbackSymmetry (cE.π.app j.left) W.hom) ?_
    intro l
    simp only [eM, P, cA]
    apply pullback.hom_ext <;>
      simp only [cM, Cone.overPost, rawAffineRestrictedMap, pullback.map,
        Functor.const_obj_obj, Functor.id_obj, Cone.postcompose_obj_pt,
        Functor.mapCone_pt, Functor.comp_obj, Over.forget_obj, Over.pullback_obj_left,
        Cone.postcompose_obj_π, NatTrans.comp_app, Functor.mapCone_π_app,
        Functor.comp_map, Over.forget_map, Over.pullback_map_left,
        Over.homMk_left, NatIso.ofComponents_hom_app, Category.assoc,
        pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
        Category.comp_id]
    all_goals
      erw [pullback.lift_fst, pullback.lift_snd]
      first
      | exact (pullbackSymmetry_hom_comp_fst _ _).symm
      | exact (pullbackSymmetry_hom_comp_snd_assoc _ _ _).symm
  have (l : Over j.left) : CompactSpace (M.obj l) := by
    have : IsAffine (M.obj l) := by
      dsimp [M]
      infer_instance
    infer_instance
  have (l : Over j.left) : QuasiSeparatedSpace (M.obj l) := by
    have : IsAffine (M.obj l) := by
      dsimp [M]
      infer_instance
    infer_instance
  have (l m : Over j.left) (f : l ⟶ m) : IsAffineHom (M.map f) := by
    dsimp [M, rawAffineRestrictedMap]
    exact MorphismProperty.pullbackMap (P := @IsAffineHom)
      (by infer_instance) (by infer_instance) (by simp)
      (by rw [← E.map_comp, Over.w f])
  let t : M ⟶ (Functor.const (Over j.left)).obj (E.obj i) :=
    { app := fun l ↦ pullback.snd W.hom (E.map l.hom) ≫
        E.map (l.hom ≫ j.hom)
      naturality := by
        intro l m f
        change M.map f ≫ (pullback.snd W.hom (E.map m.hom) ≫
          E.map (m.hom ≫ j.hom)) = _ ≫ 𝟙 _
        simp only [Category.comp_id, M, rawAffineRestrictedMap,
          pullback.map, pullback.lift_snd_assoc, Category.assoc]
        rw [← E.map_comp]
        congr 2
        rw [← Category.assoc, Over.w f] }
  let p := pullback.snd W.hom (cE.π.app j.left) ≫ (c.π.app i).left
  have hp : ∀ l, cM.π.app l ≫ t.app l = p := by
    intro l
    change rawAffineRestrictedMap (cE.π.app l.left)
      (E.map l.hom) (cE.π.app j.left) (cE.w l.hom) W ≫
      (pullback.snd W.hom (E.map l.hom) ≫ E.map (l.hom ≫ j.hom)) = _
    simp only [rawAffineRestrictedMap, pullback.map, pullback.lift_snd_assoc,
      Category.assoc]
    exact congrArg (fun f ↦ pullback.snd W.hom (cE.π.app j.left) ≫ f)
      (cE.w (l.hom ≫ j.hom))
  obtain ⟨v⟩ := exists_fixedDerivedCohomologyDiagram (E.obj i) M cM t p hp K (q : ℤ)
  obtain ⟨hv⟩ := derivedEtaleCohomology_limit (E.obj i) M cM hcM t p hp K
    (q : ℤ) v.H v.e v.hm v.B v.eY v.hs
  let eFree := (DerivedCategory.Plus.singleFunctor _ 0).mapIso
    (abelianFreeRepresentablePullbackSquareIso (c.π.app j.left).left W V r hr')
  let z₀ := eFree.inv ≫ z
  let x := rawFixedDerivedComparison (c.π.app j.left).left (c.π.app i).left
    K (q : ℤ) W z₀
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (forget AddCommGrpCat.{u + 1})
  obtain ⟨l, xl, hxl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget AddCommGrpCat.{u + 1}) hv) (v.eY.inv x)
  change v.B.ι.app l xl = v.eY.inv x at hxl
  let el := rawFixedDerivedComparison (D.map l.unop.hom).left
    (D.map (l.unop.hom ≫ j.hom)).left K (q : ℤ) W
  let := isIso_rawFixedDerivedComparison (D.map l.unop.hom).left
    (D.map (l.unop.hom ≫ j.hom)).left K (q : ℤ) W
  let y := (asIso el).inv ((v.e l.unop).hom xl)
  have hy : el y = (v.e l.unop).hom xl := by
    exact ConcreteCategory.congr_hom (Iso.inv_hom_id (asIso el)) _
  have hclass : presentationDerivedMap (cM.π.app l.unop)
      (t.app l.unop) p (hp l.unop).symm K.obj (q : ℤ) (el y) = x := by
    rw [hy]
    have hs := ConcreteCategory.congr_hom (v.hs l.unop) xl
    rw [hxl] at hs
    apply (ConcreteCategory.bijective_of_isIso v.eY.inv).injective
    simpa only [ConcreteCategory.comp_apply, Functor.const_obj_obj] using hs.symm
  have hn := rawFixedDerivedComparison_naturality
    (c.π.app l.unop.left).left (D.map l.unop.hom).left (c.π.app j.left).left
    (congrArg (fun t ↦ t.left) (c.w l.unop.hom)) (D.map (l.unop.hom ≫ j.hom)).left (c.π.app i).left
    (congrArg (fun t ↦ t.left) (c.w (l.unop.hom ≫ j.hom))).symm K (q : ℤ) W y
  have hraw : rawRestrictedDerivedPullback (c.π.app l.unop.left).left
      (D.map l.unop.hom).left (c.π.app j.left).left (congrArg (fun t ↦ t.left) (c.w l.unop.hom)) _ _
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
        (c.π.app l.unop.left).left (D.map (l.unop.hom ≫ j.hom)).left
        (c.π.app i).left (congrArg (fun t ↦ t.left) (c.w (l.unop.hom ≫ j.hom))).symm).inv.app K)
      (q : ℤ) W y = z₀ := by
    have := isIso_rawFixedDerivedComparison (c.π.app j.left).left
      (c.π.app i).left K (q : ℤ) W
    apply (ConcreteCategory.bijective_of_isIso
      (rawFixedDerivedComparison (c.π.app j.left).left (c.π.app i).left K (q : ℤ) W)).injective
    exact hn.symm.trans hclass
  refine ⟨j.left, W, hW, r, hr', l.unop, l.unop.hom ≫ j.hom, y, ?_⟩
  exact raw_chart_transport (D.map l.unop.hom).left (c.π.app l.unop.left).left
    (c.π.app j.left).left (congrArg (fun t ↦ t.left) (c.w l.unop.hom)).symm
    W V r hr' _ _
    ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} (c.π.app l.unop.left).left
      (D.map (l.unop.hom ≫ j.hom)).left (c.π.app i).left
      (congrArg (fun t ↦ t.left) (c.w (l.unop.hom ≫ j.hom))).symm).symm.app K)
    (q : ℤ) z y hraw

end AlgebraicGeometry.Etale
