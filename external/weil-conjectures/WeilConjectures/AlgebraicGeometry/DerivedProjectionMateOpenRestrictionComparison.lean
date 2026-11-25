/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.OpenRestrictionAdjunctionHomDescent
import WeilConjectures.AlgebraicGeometry.OpenRestrictionTensorCounitDescent
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh

/-! # Open restriction comparison for derived projection mates

Source: Stacks Project, Tag 08EU, first sentence of the proof, and Tag 08FE.
(blueprint: lem-pc-derived-projection-mate-open-restriction-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AlgebraicGeometry

attribute [local irreducible] schemeDerivedTensorMonoidal HasDerivedCategory.ofIsGrothendieckAbelian
  Functor.mapDerivedCategory DerivedCategory.homologyFunctor

private theorem mate_square
    {C D CO DO : Type*} [Category* C] [Category* D] [Category* CO] [Category* DO]
    {F : C ⥤ D} {G : D ⥤ C} {FO : CO ⥤ DO} {GO : DO ⥤ CO}
    {rX : D ⥤ DO} {rY : C ⥤ CO}
    (p : F ⊣ G) (q : FO ⊣ GO)
    (alpha : F ⋙ rX ≅ rY ⋙ FO) (beta : G ⋙ rY ≅ rX ⋙ GO)
    {A : C} {B : D} {N : CO} {E : DO}
    (v : F.obj A ⟶ B) (vo : FO.obj N ⟶ E)
    (a : rY.obj A ≅ N) (c : rX.obj B ≅ E)
    (hHom : rY.map (p.homEquiv A B v) ≫ beta.hom.app B =
      q.homEquiv (rY.obj A) (rX.obj B) (alpha.inv.app A ≫ rX.map v))
    (hTensor : alpha.inv.app A ≫ rX.map v ≫ c.hom = FO.map a.hom ≫ vo) :
    a.hom ≫ q.homEquiv N E vo =
      rY.map (p.homEquiv A B v) ≫ (beta.app B ≪≫ GO.mapIso c).hom := by
  symm
  dsimp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hHom, ← q.homEquiv_naturality_right,
    Category.assoc, hTensor, q.homEquiv_naturality_left]

-- Keep the fixed localizations opaque during comparison of functor types.
/-- Restriction of a projection mate to a target open is isomorphic, as an
arrow, to a projection mate for the inverse-image source over that open, using the
shared small localizations.
This is a comparison statement; it does not assert that either mate is invertible.

Source: Stacks Project, Tag 08EU, first sentence of the proof, and Tag 08FE.
(blueprint: lem-pc-derived-projection-mate-open-restriction-comparison).

Proof: use hZ and hg to identify Z with the inverse image of U and g with the
restricted morphism. No compactness or quasi-separatedness is needed for this comparison.
Restriction of quasi-coherent cohomology remains quasi-coherent. Use the exact open
restriction functors and the direct-image/open-restriction comparison of Tag 08FE.
Tensor and pullback commute with these restrictions. Open restriction on derived
categories is a localization with fully faithful right adjoint. Evaluate the supplied
tensor comparison on these right adjoints and use the localization counits to descend
it to Z and U. Descend the adjunction in the same way. Naturality of the supplied
tensor comparison and the formula for the adjunction Hom equivalence identify the
restricted mate with the descended mate, conjugated by the object comparison maps.
Change both local derived categories to their shared small localizations by uniqueness
of localization; the K-flat tensor and derived-functor universal properties transport
all the comparisons. Write rX and rY for the restrictions, N = rY(M), E = rX(L).
The source comparison a identifies rY(M tensor Rf(L)) with N tensor Rg(E).
The target comparison b identifies rY(Rf(F(M) tensor L)) with Rg(Fg(N) tensor E).
Expand p.homEquiv(v) as p.unit followed by Rf(v); the restriction comparisons
carry the unit and counit to those of q. Naturality of t at the localization
units then gives rY(pi) followed by b = a followed by the local mate.
Thus a and b define the required arrow isomorphism. The two object comparisons give
an isomorphism in the arrow category. No invertibility of a projection mate is used.
If U is empty, Z is empty and the same localization and restriction comparisons apply. -/
theorem exists_derivedProjectionMate_openRestriction_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (M : schemeDerivedQCohCategory Y) (L : schemeDerivedQCohCategory X)
    (U : Y.Opens)
    (Z : Scheme.{u}) (g : Z ⟶ U.toScheme)
    (hZ : Z = (f ⁻¹ᵁ U).toScheme) (hg : HEq g (f ∣_ U)) :
    letI : HasDerivedCategory.{u}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
        inferInstance
    letI : HasDerivedCategory.{u}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) := inferInstance
    ∃ (q : derivedPullback g ⊣ schemeDerivedDirectImage g)
        (s : tensor (schemeDerivedCategory U.toScheme) ⋙ derivedPullback g ≅
          (derivedPullback g).prod (derivedPullback g) ⋙ tensor (schemeDerivedCategory Z))
        (N : schemeDerivedQCohCategory U.toScheme) (E : schemeDerivedQCohCategory Z),
        Nonempty (Arrow.mk ((schemeOpenRestriction Y U).mapDerivedCategory.map
          (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
            ((derivedPullback f).obj M.obj ⊗ L.obj)
              (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
                (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj)))) ≅
          Arrow.mk (q.homEquiv (N.obj ⊗ (schemeDerivedDirectImage g).obj E.obj)
            ((derivedPullback g).obj N.obj ⊗ E.obj)
              (s.hom.app (N.obj, (schemeDerivedDirectImage g).obj E.obj) ≫
                (𝟙 ((derivedPullback g).obj N.obj) ⊗ₘ q.counit.app E.obj)))) := by
  rename_i hX hY
  subst Z
  have hg' : g = f ∣_ U := eq_of_heq hg
  subst g
  let hXO : HasDerivedCategory.{u}
      (SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ U).toScheme.toRingedSpace)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let hYO : HasDerivedCategory.{u}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let rX : schemeDerivedCategory X ⥤ schemeDerivedCategory (f ⁻¹ᵁ U).toScheme :=
    (schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory
  let rY : schemeDerivedCategory Y ⥤ schemeDerivedCategory U.toScheme :=
    (schemeOpenRestriction Y U).mapDerivedCategory
  have hdesc := @exists_openRestriction_adjunction_hom_descent.{u, w}
    X Y f U hX hY hXO hYO p
  rcases hdesc with ⟨q, alpha, beta, hHom⟩
  have ht := @exists_openRestriction_tensor_counit_descent.{u, w}
    X Y f U hX hY hXO hYO p t
  have ht' := ht q alpha beta hHom
  rcases ht' with ⟨s, rhoY, rhoX, hTensor⟩
  let N : schemeDerivedQCohCategory U.toScheme := ⟨rY.obj M.obj, by
    apply (@schemeDerivedQCoh_openRestriction_iff.{u, w, u} Y U hY hYO M.obj).2
    intro n
    have := M.property n
    exact SheafOfModules.isQuasicoherent_over
      (C := Y.Opens) (J := Opens.grothendieckTopology Y)
      (R := moduleRings Y.toRingedSpace) _ U⟩
  let E : schemeDerivedQCohCategory (f ⁻¹ᵁ U).toScheme := ⟨rX.obj L.obj, by
    apply (@schemeDerivedQCoh_openRestriction_iff.{u, w, u} X (f ⁻¹ᵁ U) hX hXO L.obj).2
    intro n
    have := L.property n
    exact SheafOfModules.isQuasicoherent_over
      (C := X.Opens) (J := Opens.grothendieckTopology X)
      (R := moduleRings X.toRingedSpace) _ (f ⁻¹ᵁ U)⟩
  let a : rY.obj (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj) ≅
      N.obj ⊗ (schemeDerivedDirectImage (f ∣_ U)).obj E.obj :=
    rhoY.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≪≫
      tensorIso (Iso.refl _) (beta.app L.obj)
  let c : rX.obj ((derivedPullback f).obj M.obj ⊗ L.obj) ≅
      (derivedPullback (f ∣_ U)).obj N.obj ⊗ E.obj :=
    rhoX.app ((derivedPullback f).obj M.obj, L.obj) ≪≫
      tensorIso (alpha.app M.obj) (Iso.refl _)
  let b := beta.app ((derivedPullback f).obj M.obj ⊗ L.obj) ≪≫
    (schemeDerivedDirectImage (f ∣_ U)).mapIso c
  refine ⟨q, s, N, E, ⟨Arrow.isoMk a b ?_⟩⟩
  exact mate_square p q alpha beta _ _ a c (hHom _ _ _) (hTensor M.obj L.obj)

end AlgebraicGeometry
