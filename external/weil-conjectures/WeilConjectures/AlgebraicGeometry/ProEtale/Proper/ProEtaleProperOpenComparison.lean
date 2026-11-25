/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparisonIso
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparisonComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel

/-!
# The canonical proper-open comparison on the pro-etale site

The map is the transport of the specified etale map through the canonical
extension-by-zero mate and direct-image comparison. No unspecified isomorphism is chosen.

## References

* Stacks Tag 09AF
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Extend the canonical sheaf extension-by-zero mate termwise to bounded below complexes. -/
def properOpenSiteExtensionIso (Λ : Type (u + 1)) [CommRing Λ]
    {X T : Scheme.{u}} (j : X ⟶ T) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The specified proper-open isomorphism: inverse extension comparison, comparison
pullback of the etale proper-open map, canonical direct-image mate, extension comparison. -/
def properOpenProEtaleIsoPlus (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (r : T₁ ⟶ T₂) [IsProper r]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ r = j₂)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj L) ≅
      (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj L)) :=
  letI := Etale.isIso_properOpenComparison Λ r j₁ j₂ h L
  letI := isIso_comparisonDirectImagePlus Λ r
  (properOpenSiteExtensionIso Λ j₂).symm.app L ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T₂).mapDerivedCategoryPlus.mapIso
      (asIso (Etale.properOpenComparison Λ r j₁ j₂ h L)) ≪≫
    (asIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange r (ModuleCat.{u + 1} Λ)))).app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj L) ≪≫
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.mapIso
      ((properOpenSiteExtensionIso Λ j₁).app L)

/-- The same canonical comparison in the ambient unbounded derived category, using only
canonical compatibility isomorphisms for the bounded below inclusions. -/
def properOpenProEtaleIso (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (r : T₁ ⟶ T₂) [IsProper r]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ r = j₂)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategory.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L.obj) ≅
      (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctor.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategory.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L.obj)) :=
  let N := comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  let J₁ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁
  let J₂ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂
  let R := (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctor
  J₂.mapDerivedCategory.mapIso (N.mapDerivedCategoryPlusCompatibility.app L).symm ≪≫
    (J₂.mapDerivedCategoryPlusCompatibility.app (N.mapDerivedCategoryPlus.obj L)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso (properOpenProEtaleIsoPlus Λ r j₁ j₂ h L) ≪≫
    ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusCompatibility.app
      (J₁.mapDerivedCategoryPlus.obj (N.mapDerivedCategoryPlus.obj L))) ≪≫
    R.mapIso (J₁.mapDerivedCategoryPlusCompatibility.app (N.mapDerivedCategoryPlus.obj L)) ≪≫
    R.mapIso (J₁.mapDerivedCategory.mapIso (N.mapDerivedCategoryPlusCompatibility.app L))

/-- The transported maps respect composition. No assertion about arbitrary pro-etale
complexes is made: the same bounded below etale `L` is used in all three terms. -/
theorem properOpenProEtaleIsoPlus_comp (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ T₃ X : Scheme.{u}} [IsNoetherian T₁] [IsNoetherian T₂] [IsNoetherian T₃]
    (r : T₁ ⟶ T₂) (s : T₂ ⟶ T₃) [IsProper r] [IsProper s]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (j₃ : X ⟶ T₃)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₃]
    (hr : j₁ ≫ r = j₂) (hs : j₂ ≫ s = j₃)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (properOpenProEtaleIsoPlus Λ (r ≫ s) j₁ j₃
      ((Category.assoc j₁ r s).symm.trans ((congrArg (· ≫ s) hr).trans hs)) L).hom =
      (properOpenProEtaleIsoPlus Λ s j₂ j₃ hs L).hom ≫
        (lowerStar (ModuleCat.{u + 1} Λ) s).rightDerivedFunctorPlus.map
          (properOpenProEtaleIsoPlus Λ r j₁ j₂ hr L).hom ≫
        (proEtaleComparisonDirectImageCompIso Λ r s).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj L)) := by
  let A := ModuleCat.{u + 1} Λ
  let N₁ := (comparisonUpperStar A T₁).mapDerivedCategoryPlus
  let N₂ := (comparisonUpperStar A T₂).mapDerivedCategoryPlus
  let N₃ := (comparisonUpperStar A T₃).mapDerivedCategoryPlus
  let R := (Etale.lowerStar A r).rightDerivedFunctorPlus
  let S := (Etale.lowerStar A s).rightDerivedFunctorPlus
  let R' := (lowerStar A r).rightDerivedFunctorPlus
  let S' := (lowerStar A s).rightDerivedFunctorPlus
  let H' := (lowerStar A (r ≫ s)).rightDerivedFunctorPlus
  let M := (Etale.openImmersionLowerShriek A j₁).mapDerivedCategoryPlus.obj L
  let P := (Etale.openImmersionLowerShriek A j₂).mapDerivedCategoryPlus.obj L
  let Q := (Etale.openImmersionLowerShriek A j₃).mapDerivedCategoryPlus.obj L
  let B₁ := (openImmersionLowerShriek A j₁).mapDerivedCategoryPlus.obj
    ((comparisonUpperStar A X).mapDerivedCategoryPlus.obj L)
  let B₂ := (openImmersionLowerShriek A j₂).mapDerivedCategoryPlus.obj
    ((comparisonUpperStar A X).mapDerivedCategoryPlus.obj L)
  let B₃ := (openImmersionLowerShriek A j₃).mapDerivedCategoryPlus.obj
    ((comparisonUpperStar A X).mapDerivedCategoryPlus.obj L)
  let d₁ : N₁.obj M ≅ B₁ := (properOpenSiteExtensionIso Λ j₁).app L
  let d₂ : N₂.obj P ≅ B₂ := (properOpenSiteExtensionIso Λ j₂).app L
  let d₃ : N₃.obj Q ≅ B₃ := (properOpenSiteExtensionIso Λ j₃).app L
  let a : P ⟶ R.obj M := Etale.properOpenComparison Λ r j₁ j₂ hr L
  let b : Q ⟶ S.obj P := Etale.properOpenComparison Λ s j₂ j₃ hs L
  let hc := (Category.assoc j₁ r s).symm.trans ((congrArg (· ≫ s) hr).trans hs)
  let c : Q ⟶ (Etale.lowerStar A (r ≫ s)).rightDerivedFunctorPlus.obj M :=
    Etale.properOpenComparison Λ (r ≫ s) j₁ j₃ hc L
  let Dᵣ := Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange r A)
  let Dₛ := Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange s A)
  let Dᵣₛ := Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange (r ≫ s) A)
  let ce := etaleComparisonDirectImageCompIso Λ r s
  let cp := proEtaleComparisonDirectImageCompIso Λ r s
  have ha : c = b ≫ S.map a ≫ ce.hom.app M :=
    Etale.properOpenComparison_comp Λ r s j₁ j₂ j₃ hr hs L
  have hD : N₃.map (ce.hom.app M) ≫ Dᵣₛ.app M =
      Dₛ.app (R.obj M) ≫ S'.map (Dᵣ.app M) ≫ cp.hom.app (N₁.obj M) :=
    comparisonDirectImagePlus_comp Λ r s M
  have hn : N₃.map (S.map a) ≫ Dₛ.app (R.obj M) =
      Dₛ.app P ≫ S'.map (N₂.map a) := Dₛ.naturality a
  have hp : cp.hom.app (N₁.obj M) ≫ H'.map d₁.hom =
      S'.map (R'.map d₁.hom) ≫ cp.hom.app B₁ :=
    (cp.hom.naturality d₁.hom).symm
  have hd : S'.map d₂.hom ≫ S'.map d₂.inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  change (d₃.inv ≫ N₃.map c ≫ Dᵣₛ.app M ≫ H'.map d₁.hom) =
    (d₃.inv ≫ N₃.map b ≫ Dₛ.app P ≫ S'.map d₂.hom) ≫
      S'.map (d₂.inv ≫ N₂.map a ≫ Dᵣ.app M ≫ R'.map d₁.hom) ≫
        cp.hom.app B₁
  rw [ha]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hd]
  rw [reassoc_of% hD, hp, reassoc_of% hn]

end AlgebraicGeometry.ProEtale
