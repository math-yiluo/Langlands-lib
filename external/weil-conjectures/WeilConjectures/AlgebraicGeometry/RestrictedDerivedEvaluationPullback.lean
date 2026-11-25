/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
import WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionShiftComparison

/-! # The derived evaluation square before choosing a generator

Source: Stacks Project, Tags 0D6F, 07A6 and 03Q8.
(blueprint: lem-sbc-restricted-derived-evaluation-pullback).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- Restricted derived sections followed by zeroth homology.
Source: Stacks Project, Tag 0BKV.
(blueprint: lem-sbc-restricted-derived-evaluation-pullback). -/
noncomputable abbrev Hzero {S Y : Scheme.{v}} (h : Y ⟶ S) (U : S.Etale) :=
  sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0

/-- Transport zeroth derived sections of a single sheaf by ordinary section pullback.
All maps are constructed: the zero comparison, the adjunction unit on sections,
the restricted coefficient map, and the inverse zero comparison.
Source: Stacks Project, Tags 0D6F and 07A6.
(blueprint: lem-sbc-restricted-derived-evaluation-pullback). -/
noncomputable def transportZero {S Y Y' : Scheme.{v}} (a : Y' ⟶ Y)
    (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (G' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (ψ : (upperStar AddCommGrpCat.{v + 1} a).obj G ⟶ G') (U : S.Etale) :
    (Hzero h U).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ⟶
      (Hzero h' U).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G') :=
  (zeroIso ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U) G).hom ≫
    globalSectionsUpperStarMap AddCommGrpCat.{v + 1} (rawAffineRestrictedMap a h h' w U)
      ((upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)).obj G) ≫
    (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1}).map
      (rawAffineRestrictedCoefficient a h h' w G G' ψ U) ≫
    (zeroIso ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U) G').inv

/-- Pullback of a derived morphism with an arbitrary source sheaf identification.
Source: Stacks Project, Tag 07A6.
(blueprint: lem-sbc-restricted-derived-evaluation-pullback). -/
noncomputable def pullbackHom {Y Y' : Scheme.{v}} (a : Y' ⟶ Y) (p : ℕ)
    {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}}
    {G' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1}}
    (e : (upperStar AddCommGrpCat.{v + 1} a).obj G ≅ G')
    {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}}
    {F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1}}
    (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F')
    (t : (DerivedCategory.Plus.singleFunctor _ 0).obj G ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj G' ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F')⟦(p : ℤ)⟧ :=
  (DerivedCategory.Plus.singleFunctor _ 0).map e.inv ≫
    ((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryPlusSingleFunctor 0).inv.app G ≫
    D+(upperStar AddCommGrpCat.{v + 1} a).map t ≫
    (D+(upperStar AddCommGrpCat.{v + 1} a).commShiftIso (p : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (shiftFunctor _ (p : ℤ)).map
      (((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map φ)

/-- The derived section square for an arbitrary morphism between single complexes.
No represented sheaf, identity generator, or evaluation at a chosen element occurs.
Source: Stacks Project, Cohomology on Sites, Tags 0D6F and 07A6; the natural
restriction calculation in Tag 03Q8.
(blueprint: lem-sbc-restricted-derived-evaluation-pullback).

Proof: Put r = pr_Y, r' = pr_Y' and q = U times_S a. The pullback identities
imply r' followed by a equals q followed by r. Use inverse-image composition
along this equality to identify r'^* a^* with q^* r^*. The unit for q gives a
natural map RΓ(V, r^* K) to RΓ(V', r'^* a^* K): apply RΓ to its derived unit,
then use the derived composition comparison for q_* and global sections.
Its naturality square at t commutes by functoriality and naturality of the unit.
On a single G in degree zero this map is the ordinary section pullback, since
the degree-zero right-derived comparison identifies the derived unit with the
underived adjunction unit. Postcompose by e to obtain transportZero.
On the shifted single F the shift comparison and single-complex comparison
identify the same map with rawAffineComplexPullback, followed by the restricted
single coefficient morphism for φ. Naturality of these comparisons gives
rawAffineRestrictedCohomologyMap. Precompose the naturality square with the
single comparison for G and the inverse of e, and postcompose with the shift
comparison for F'. Cancel each comparison with its inverse. The resulting
square is the stated equality of homomorphisms. All constructions apply for
p = 0 and on an empty restricted scheme; no inverse of a section map is used. -/
theorem restrictedDerivedEvaluation_pullback {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (G' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (e : (upperStar AddCommGrpCat.{v + 1} a).obj G ≅ G')
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F') (U : S.Etale)
    (t : (DerivedCategory.Plus.singleFunctor _ 0).obj G ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧) :
    (Hzero h U).map t ≫ (shiftIso h p F U).hom ≫
        rawAffineRestrictedCohomologyMap a h h' w p F F' φ U =
      transportZero a h h' w G G' e.hom U ≫
        (Hzero h' U).map (pullbackHom a p e φ t) ≫ (shiftIso h' p F' U).hom := by
  let L := upperStar AddCommGrpCat.{v + 1} a
  let A := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  let B := ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧
  let α := (L.mapDerivedCategoryPlusSingleFunctor 0).hom.app G ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map e.hom
  let αinv := (DerivedCategory.Plus.singleFunctor _ 0).map e.inv ≫
    (L.mapDerivedCategoryPlusSingleFunctor 0).inv.app G
  let β := (D+(L).commShiftIso (p : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (shiftFunctor _ (p : ℤ)).map
      ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map φ)
  have hα : α ≫ αinv = 𝟙 _ := by
    simp [α, αinv, Category.assoc]
  have hzero : (restrictedSectionPullback a h h' w U).app A ≫
      (Hzero h' U).map α = transportZero a h h' w G G' e.hom U :=
    restrictedSectionPullback_zero a h h' w G G' e.hom U
  have hshift : (restrictedSectionPullback a h h' w U).app B ≫
      (Hzero h' U).map β ≫ (shiftIso h' p F' U).hom =
      (shiftIso h p F U).hom ≫
        rawAffineRestrictedCohomologyMap a h h' w p F F' φ U :=
    restrictedSectionPullback_shift a h h' w p F F' φ U
  have hnat : (Hzero h U).map t ≫ (restrictedSectionPullback a h h' w U).app B =
      (restrictedSectionPullback a h h' w U).app A ≫ (Hzero h' U).map (D+(L).map t) :=
    (restrictedSectionPullback a h h' w U).naturality t
  have hpull : pullbackHom a p e φ t = αinv ≫ D+(L).map t ≫ β := by
    simp only [pullbackHom, αinv, β, L, Category.assoc]
  have hcancel : (Hzero h' U).map α ≫ (Hzero h' U).map αinv = 𝟙 _ := by
    rw [← Functor.map_comp, hα]
    exact (Hzero h' U).map_id _
  calc
    _ = (Hzero h U).map t ≫ (restrictedSectionPullback a h h' w U).app B ≫
        (Hzero h' U).map β ≫ (shiftIso h' p F' U).hom := by rw [hshift]
    _ = (restrictedSectionPullback a h h' w U).app A ≫
        (Hzero h' U).map (D+(L).map t) ≫ (Hzero h' U).map β ≫
          (shiftIso h' p F' U).hom := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ (Hzero h' U).map β ≫ (shiftIso h' p F' U).hom) hnat
    _ = _ := by
      rw [hpull, ← hzero]
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc ((Hzero h' U).map α), hcancel]
      simp only [Category.id_comp]

end AlgebraicGeometry.Etale.RawRestrictedComparison
