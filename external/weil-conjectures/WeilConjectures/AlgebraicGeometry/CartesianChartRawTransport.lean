/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianFreeRepresentablePullback
public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonIsIso

/-! # Geometric transport of chart classes

Source: Stacks Project, Tag 0EYM, the pullback identifications in the second proof.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency true

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Pasting identifies the chart fibre product with the cartesian source over T.
Both arrows are explicitly constructed by the pullback universal property.
Source: Stacks Project, Tag 0EYM.
(blueprint: def-sc-cartesian-chart-source-iso). -/
noncomputable def cartesianChartSourceIso {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) :
    pullback a (pullback.snd f g) ≅ pullback f g' where
  hom := pullback.lift
    (pullback.snd a (pullback.snd f g) ≫ pullback.fst f g)
    (pullback.fst a (pullback.snd f g)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        ← pullback.condition, Category.assoc, ← w])
  inv := pullback.lift (pullback.snd f g')
    (pullback.lift (pullback.fst f g') (pullback.snd f g' ≫ a) (by
      rw [Category.assoc, ← w, pullback.condition])) (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp
    · apply pullback.hom_ext <;> simp [pullback.condition]
  inv_hom_id := by
    apply pullback.hom_ext <;> simp

@[reassoc (attr := simp)]
theorem cartesianChartSourceIso_hom_fst {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) :
    (cartesianChartSourceIso f g a g' w).hom ≫ pullback.fst f g' =
      pullback.snd a (pullback.snd f g) ≫ pullback.fst f g := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cartesianChartSourceIso_hom_snd {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) :
    (cartesianChartSourceIso f g a g' w).hom ≫ pullback.snd f g' =
      pullback.fst a (pullback.snd f g) := by
  exact pullback.lift_snd _ _ _

/-- The inverse chart identification preserves its projection to T.
(blueprint: def-sc-cartesian-chart-source-iso). -/
@[reassoc (attr := simp)]
theorem cartesianChartSourceIso_inv_fst {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) :
    (cartesianChartSourceIso f g a g' w).inv ≫
      pullback.fst a (pullback.snd f g) = pullback.snd f g' := by
  exact pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The inverse chart identification preserves its projection to X.
(blueprint: def-sc-cartesian-chart-source-iso). -/
@[reassoc (attr := simp)]
theorem cartesianChartSourceIso_inv_snd_fst {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) :
    (cartesianChartSourceIso f g a g' w).inv ≫
      pullback.snd a (pullback.snd f g) ≫ pullback.fst f g = pullback.fst f g' := by
  simp [cartesianChartSourceIso]

/-- Pullback along an isomorphism is an equivalence also on bounded-below
complexes; the unit and counit are the composition and identity comparisons.
Source: Stacks Project, Tag 03CB.
(blueprint: def-sc-cartesian-chart-source-iso). -/
noncomputable def abelianDerivedPullbackEquivalence {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ≌
      DerivedCategory.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Equivalence.mk D+((e.inv)^*[AddCommGrpCat.{u + 1}])
    D+((e.hom)^*[AddCommGrpCat.{u + 1}])
    ((upperStarIdDerivedPlus AddCommGrpCat.{u + 1} Y).symm ≪≫
      upperStarCompDerivedPlus AddCommGrpCat.{u + 1} e.hom e.inv (𝟙 Y) (by simp))
    ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} e.inv e.hom (𝟙 Z) (by simp)).symm ≪≫
      upperStarIdDerivedPlus AddCommGrpCat.{u + 1} Z)

/-- The explicit coefficient comparison on the chart identification.
Source: Stacks Project, Tags 03CB and 0EYM.
(blueprint: def-sc-cartesian-chart-source-iso). -/
noncomputable def cartesianChartCoefficientIso {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (((cartesianChartSourceIso f g a g' w).inv)^*[AddCommGrpCat.{u + 1}]).obj
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F)) ≅
      ((pullback.fst f g')^*[AddCommGrpCat.{u + 1}]).obj F :=
  ((upperStarComp AddCommGrpCat.{u + 1} (cartesianChartSourceIso f g a g' w).inv
    (pullback.snd a (pullback.snd f g))).app _).symm ≪≫
  ((upperStarComp AddCommGrpCat.{u + 1}
    ((cartesianChartSourceIso f g a g' w).inv ≫ pullback.snd a (pullback.snd f g))
    (pullback.fst f g) (pullback.fst f g')
    (cartesianChartSourceIso_inv_snd_fst f g a g' w).symm).app F).symm

/-- Pullback of raw classes along a specified scheme isomorphism and coefficient
isomorphism. Its underlying map is exactly the canonical raw pullback.
Source: Stacks Project, Tags 03CB and 03Q8.
(blueprint: def-sc-abelian-raw-iso-pullback). -/
noncomputable def abelianRawIsoPullback {B Y Z : Scheme.{u}} (e : Y ≅ Z)
    (h : Y ⟶ B) (h' : Z ⟶ B) (w : e.inv ≫ h = h') (q : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((e.inv)^*[AddCommGrpCat.{u + 1}]).obj F ≅ F') (V : B.Etale) :
    (abelianHigherDirectImageRawPresheaf h q F).obj (op V) ≅
      (abelianHigherDirectImageRawPresheaf h' q F').obj (op V) := by
  let L := D+((e.inv)^*[AddCommGrpCat.{u + 1}])
  letI : L.IsEquivalence := (abelianDerivedPullbackEquivalence e).isEquivalence_functor
  let A := ((h)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj V)
  let A' := ((h')^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj V)
  let ea : (DerivedCategory.Plus.singleFunctor _ 0).obj A' ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        (((e.inv)^*[AddCommGrpCat.{u + 1}]).obj A) :=
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((upperStarComp AddCommGrpCat.{u + 1} e.inv h h' w.symm).app _)
  let eb : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((e.inv)^*[AddCommGrpCat.{u + 1}]).obj A) ≅
      L.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A) :=
    ((((e.inv)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).app A).symm
  let eg : L.obj (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) ≅
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F')⟦(q : ℤ)⟧ :=
    (L.commShiftIso (q : ℤ)).app _ ≪≫ (shiftFunctor _ (q : ℤ)).mapIso
      ((((e.inv)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).app F ≪≫
        (DerivedCategory.Plus.singleFunctor _ 0).mapIso φ)
  let em : AddCommGrpCat.of
      ((DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) ≅
      AddCommGrpCat.of (L.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A) ⟶
        L.obj (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧)) :=
    (AddEquiv.ofBijective L.mapAddHom
      ⟨L.map_injective, L.map_surjective⟩).toAddCommGrpIso
  exact em ≪≫ (preadditiveCoyoneda.obj (op _)).mapIso eg ≪≫
    (preadditiveYoneda.obj _).mapIso eb.op ≪≫
    (preadditiveYoneda.obj _).mapIso ea.op

/-- The constructed isomorphism acts by the prescribed raw pullback.
Source: Stacks Project, Tag 03CB.
(blueprint: def-sc-abelian-raw-iso-pullback). -/
theorem abelianRawIsoPullback_hom {B Y Z : Scheme.{u}} (e : Y ≅ Z)
    (h : Y ⟶ B) (h' : Z ⟶ B) (w : e.inv ≫ h = h') (q : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((e.inv)^*[AddCommGrpCat.{u + 1}]).obj F ≅ F') (V : B.Etale)
    (z : (abelianHigherDirectImageRawPresheaf h q F).obj (op V)) :
    (abelianRawIsoPullback e h h' w q F F' φ V).hom z =
      abelianHigherDirectImageRawPullback e.inv h h' w q F F' φ.hom V z := by
  rfl

/-- The additive shifted derived adjunction, with the shift comparison of
right derived direct image. Source: Stacks Project, Tag 03Q8.
(blueprint: def-sc-abelian-raw-adjunction-iso). -/
noncomputable def abelianShiftedDerivedAdjunctionIso {T Y : Scheme.{u}}
    (p : Y ⟶ T)
    (A : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ) :
    AddCommGrpCat.of ((D+((p)^*[AddCommGrpCat.{u + 1}])).obj A ⟶ K⟦q⟧) ≅
      AddCommGrpCat.of (A ⟶ ((R+((p)_*[AddCommGrpCat.{u + 1}])).obj K)⟦q⟧) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).derivedPlus.homAddEquiv
      A (K⟦q⟧)).toAddCommGrpIso ≪≫
    (preadditiveCoyoneda.obj (op A)).mapIso
      ((R+((p)_*[AddCommGrpCat.{u + 1}]).commShiftIso q).app K)

/-- Transport raw chart classes into the Hom group on the actual fibre product.
All factors are isomorphisms of exact inverse images, single complexes or raw
classes under a scheme isomorphism. Source: Stacks Project, Tags 03CB and 0EYM.
(blueprint: def-sc-cartesian-chart-adjunct). -/
noncomputable def cartesianChartAdjunctIso {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (V : B.Etale) :
    (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) q
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V) ≅
      AddCommGrpCat.of
        ((D+((pullback.snd f g')^*[AddCommGrpCat.{u + 1}])).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj V))) ⟶
          ((D+((pullback.fst f g')^*[AddCommGrpCat.{u + 1}])).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(q : ℤ)⟧) := by
  let e := cartesianChartSourceIso f g a g' w
  let p := pullback.snd f g'
  let G := ((pullback.fst f g')^*[AddCommGrpCat.{u + 1}]).obj F
  have hd : e.inv ≫ (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) = p ≫ a := by
    rw [← pullback.condition, ← Category.assoc, cartesianChartSourceIso_inv_fst]
  let A := ((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj V)
  let ea : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p ≫ a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj V)) ≅
      (D+((p)^*[AddCommGrpCat.{u + 1}])).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj A) :=
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso
        ((upperStarComp AddCommGrpCat.{u + 1} p a).app _) ≪≫
      ((((p)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).app A).symm
  exact abelianRawIsoPullback e _ _ hd q _ G (cartesianChartCoefficientIso f g a g' w F) V ≪≫
    (preadditiveYoneda.obj _).mapIso ea.symm.op ≪≫
    (preadditiveCoyoneda.obj (op _)).mapIso ((shiftFunctor _ (q : ℤ)).mapIso
      ((((pullback.fst f g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor
        0).app F).symm)

/-- Take the shifted derived adjoint of the explicitly transported chart class.
Source: Stacks Project, Tags 03Q8 and 0EYM.
(blueprint: def-sc-cartesian-chart-raw-adjunction-iso). -/
noncomputable def cartesianChartRawAdjunctionIso {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (V : B.Etale) :
    (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) q
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V) ≅
      AddCommGrpCat.of
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj V)) ⟶
          (cartesianDerivedImage f g'
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(q : ℤ)⟧) :=
  cartesianChartAdjunctIso f g a g' w F q V ≪≫
    abelianShiftedDerivedAdjunctionIso (pullback.snd f g') _ _ (q : ℤ)

/-- The chart cohomology comparison for a specified pullback test object. Its
three factors are the inverse of the raw cohomology evaluation comparison,
the chart derived adjunction, and the free-representable pullback isomorphism.
Source: Stacks Project, Tags 03Q8 and 0EYM.
(blueprint: def-sc-cartesian-chart-cohomology-iso). -/
noncomputable def cartesianChartCohomologyIso {S X T B : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S)
    (w : g' = a ≫ g) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (V : B.Etale) (U : T.Etale) (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom a) :
    rawAffineRestrictedCohomology
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) q
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F)) V ≅
      AddCommGrpCat.of
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((abelianComparisonFree T).obj U) ⟶
          (cartesianDerivedImage f g'
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(q : ℤ)⟧) := by
  let h := pullback.snd a (pullback.snd f g) ≫ pullback.snd f g
  let G := ((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F)
  letI := isIso_rawRestrictedCohomologyComparison h q G V
  exact (asIso (rawRestrictedCohomologyComparison h q G V)).symm ≪≫
    cartesianChartRawAdjunctionIso f g a g' w F q V ≪≫
    (preadditiveYoneda.obj _).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
        (abelianFreeRepresentablePullbackSquareIso a V U r hr)).op

end AlgebraicGeometry.Etale
