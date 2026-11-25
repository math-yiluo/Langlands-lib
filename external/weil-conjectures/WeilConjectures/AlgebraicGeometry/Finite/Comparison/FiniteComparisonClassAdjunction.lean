/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules

import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import Mathlib.CategoryTheory.EssentialImage
/-!
# Exceptional adjunction on the comparison class

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-existence,
thm-sf-ambient-adjoint-class.md (blueprint: thm-sf-ambient-adjoint-class).

The interface retains the natural Hom equivalences and the compactification comparisons.
The right functor is written as the specified comparison composite, without an ambient
pro-etale adjunction hypothesis. A single etale right adjoint normalizes the right functors
for all compactifications; compatibility of the Hom equivalences characterizes the left
comparisons, and the right comparisons are identities in this normalization. The left
comparisons are required to equal the existing canonical comparison on every
bounded-below étale representative, rather than being chosen as a free coherent family.
-/

@[expose] public noncomputable section

set_option autoImplicit false

section HomDescent

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {B : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} B]
  (U : C ⥤ D) [U.IsEquivalence] (F : D ⥤ E) (I : D ⥤ B) (R : E ⥤ B)
  (Q : ObjectProperty E)
  (e : ∀ (X : C) (Y : E), Q Y → ((F.obj (U.obj X) ⟶ Y) ≃ (I.obj (U.obj X) ⟶ R.obj Y)))

variable
  (el : ∀ (X X' : C) (Y : E) (hY : Q Y) (a : X ⟶ X')
    (b : F.obj (U.obj X') ⟶ Y),
    e X Y hY (F.map (U.map a) ≫ b) = I.map (U.map a) ≫ e X' Y hY b)
  (er : ∀ (X : C) (Y Y' : E) (hY : Q Y) (hY' : Q Y')
    (a : F.obj (U.obj X) ⟶ Y) (b : Y ⟶ Y'),
    e X Y' hY' (a ≫ b) = e X Y hY a ≫ R.map b)

/-- Transport the given Hom bijections using the canonical representative of each object. -/
private def comparisonHomDescent (X : D) (Y : E) (hY : Q Y) :
    (F.obj X ⟶ Y) ≃ (I.obj X ⟶ R.obj Y) :=
  (F.mapIso (U.objObjPreimageIso X)).symm.homFromEquiv.trans
    ((e (U.objPreimage X) Y hY).trans (I.mapIso (U.objObjPreimageIso X)).homFromEquiv)

include el in
/-- Naturality in the source follows by lifting its conjugate to the full functor. -/
private theorem comparisonHomDescent_left (X X' : D) (Y : E) (hY : Q Y)
    (a : X ⟶ X') (b : F.obj X' ⟶ Y) :
    comparisonHomDescent U F I R Q e X Y hY (F.map a ≫ b) =
      I.map a ≫ comparisonHomDescent U F I R Q e X' Y hY b := by
  let a₀ := U.inv.map a
  have ha : U.map a₀ =
      (U.objObjPreimageIso X).hom ≫ a ≫ (U.objObjPreimageIso X').inv :=
    U.fun_inv_map X X' a
  have h := el (U.objPreimage X) (U.objPreimage X') Y hY a₀
    (F.map (U.objObjPreimageIso X').hom ≫ b)
  simp only [ha, Functor.map_comp, Category.assoc] at h
  simpa [comparisonHomDescent, Category.assoc] using
    congrArg (fun t ↦ I.map (U.objObjPreimageIso X).inv ≫ t) h

include er in
/-- Naturality in the target is preserved by the transport. -/
private theorem comparisonHomDescent_right (X : D) (Y Y' : E) (hY : Q Y) (hY' : Q Y')
    (a : F.obj X ⟶ Y) (b : Y ⟶ Y') :
    comparisonHomDescent U F I R Q e X Y' hY' (a ≫ b) =
      comparisonHomDescent U F I R Q e X Y hY a ≫ R.map b := by
  simpa [comparisonHomDescent, Category.assoc] using
    congrArg (fun t ↦ I.map (U.objObjPreimageIso X).inv ≫ t)
      (er (U.objPreimage X) Y Y' hY hY' (F.map (U.objObjPreimageIso X).hom ≫ a) b)

include el in
/-- On an object in the image the descended bijection is exactly the original one. -/
private theorem comparisonHomDescent_obj (X : C) (Y : E) (hY : Q Y)
    (a : F.obj (U.obj X) ⟶ Y) :
    comparisonHomDescent U F I R Q e (U.obj X) Y hY a = e X Y hY a := by
  let a₀ := U.preimage (U.objObjPreimageIso (U.obj X)).hom
  have h := el (U.objPreimage (U.obj X)) X Y hY a₀ a
  simp only [a₀, Functor.map_preimage] at h
  simp [comparisonHomDescent, h]

end CategoryTheory

end HomDescent

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The named direct-image comparison on D+, placed in the ordinary derived
categories using their specified inclusion comparisons. It is the actual counit mate.
Source: blueprint comparison-class adjunction, proper direct-image comparison
(blueprint: thm-sf-ambient-adjoint-class). -/
def fixedDirectImageComparisonIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V : Scheme.{u}} (c : S ⟶ V) [QuasiCompact c] [QuasiSeparated c] :
    DerivedCategory.Plus.ι ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory ≅
      DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor :=
  Functor.isoWhiskerRight
      (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlusCompatibility.symm _ ≪≫
    Functor.isoWhiskerLeft
      (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlus
      (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategoryPlusCompatibility.symm ≪≫
    Functor.isoWhiskerRight
      (@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A c)
        (isIso_fixedComparisonDirectImageMatePlus A c)) DerivedCategory.Plus.ι ≪≫
    Functor.isoWhiskerLeft
      (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategoryPlus
      (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlusCompatibility ≪≫
    Functor.isoWhiskerRight
      (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategoryPlusCompatibility _

/-- Compact support comparison with the specified direct-image counit mate.
Source: blueprint comparison-class adjunction, chosen compactification
(blueprint: thm-sf-ambient-adjoint-class). -/
noncomputable def fixedCompactSupportComparisonIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (A : Type (u + 1)) [CommRing A] [Finite A] (c : Compactification f) :
    DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} A]) ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      DerivedCategory.Plus.ι ⋙ Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1}
        A) c ⋙
        D(ν^*(Y)[ModuleCat.{u + 1} A]) :=
  have := c.isProper
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryCompIso _ _ ≪≫
            Functor.mapDerivedCategoryNatIso
              (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) c.i).symm ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm)
          R(ProEtale.lowerStar (ModuleCat.{u + 1} A) c.g)
              ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
        c.i).mapDerivedCategoryPlusCompatibility.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D+(Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
      (fixedDirectImageComparisonIso A c.g).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
        c.i).mapDerivedCategoryPlusCompatibility _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι (Functor.associator _ _ _).symm

/-- Canonical compactification comparison on etale representatives, obtained by
transporting the canonical etale comparison through the specified compact-support maps.
Source: blueprint comparison-class adjunction, clause (3)
(blueprint: thm-sf-ambient-adjoint-class). -/
def fixedCompactSupportOriginIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) :=
  fixedCompactSupportComparisonIso A c ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c d)
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ≪≫
    (fixedCompactSupportComparisonIso A d).symm

/-- The relative adjunction and its coherent compactification comparisons, with the right
functor normalized to `nu_X^* G Rnu_Y,*`. `P` and `Q` specify precisely the allowed inputs
and targets. For the finite coefficient ring `Λ`, the comparison components must equal
`fixedCompactSupportOriginIso`, the existing transport of the
canonical étale comparisons. The Hom bijection at `c₀` must be the transport of `adj` by
the fixed compact-support comparison and derived comparison adjunction. The datum also
includes preservation of bounded-below complexes by the transported right functor.
Source: Weil blueprint, thm-sf-ambient-adjoint-class.md, clauses (2)--(3)
(blueprint: thm-sf-ambient-adjoint-class). -/
structure FixedComparisonClassAdjunction
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (c₀ : Compactification f)
    (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀ ⊣ G)
    (P : ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))))
    (Q : ObjectProperty (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))) where
  /-- The transported ordinary right adjoint preserves bounded-below complexes. -/
  boundedBelow (L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
      (hL : _root_.DerivedCategory.TStructure.t.plus L) :
    _root_.DerivedCategory.TStructure.t.plus
      ((R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ G ⋙
        D(ν^*(X)[ModuleCat.{u + 1} Λ])).obj L)
  /-- The adjunction bijections for each compactification and each allowed pair. -/
  homEquiv (c : Compactification f) (K) (hK : P K) (L) (hL : Q L) :
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K ⟶ L) ≃
      (K ⟶ (R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ G ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ])).obj L)
  /-- At the chosen compactification, the Hom bijection is the transported chosen
  étale adjunction, through the fixed compact-support and site comparisons. -/
  homEquiv_normalized
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (hK : P (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj)) (L) (hL : Q L)
      (a : (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} Λ) c₀).obj K.obj ⟶
        R(ν_*(Y)[ModuleCat.{u + 1} Λ]).obj L) :
    homEquiv c₀ (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj) hK L hL
        ((fixedCompactSupportComparisonIso
            Λ c₀).hom.app K ≫
          ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ L).symm a) =
      D(ν^*(X)[ModuleCat.{u + 1} Λ]).map ((adj.homEquiv K.obj _) a)
  /-- Naturality with respect to every morphism between allowed inputs. -/
  naturality_left (c : Compactification f) (K K') (hK : P K) (hK' : P K')
      (L) (hL : Q L) (a : K ⟶ K')
      (b : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K' ⟶ L) :
    homEquiv c K hK L hL
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map a ≫ b) =
      a ≫ homEquiv c K' hK' L hL b
  /-- Naturality with respect to every morphism between allowed targets. -/
  naturality_right (c : Compactification f) (K) (hK : P K)
      (L L') (hL : Q L) (hL' : Q L')
      (a : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K ⟶ L)
      (b : L ⟶ L') :
    homEquiv c K hK L' hL' (a ≫ b) =
      homEquiv c K hK L hL a ≫
        (R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ G ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ])).map b
  /-- Compactification comparisons on exactly the permitted input class. -/
  comparison (c d : Compactification f) :
    P.ι ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ≅
      P.ι ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d
  /-- On every étale-origin input, the comparison is the canonical étale comparison
  transported through `ν^*`; this fixes the comparison rather than allowing scalar twists. -/
  comparison_normalized (c d : Compactification f)
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (hK : P (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj)) :
    (comparison c d).hom.app ⟨D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj, hK⟩ =
      (fixedCompactSupportOriginIso Λ c d).hom.app K
  /-- Comparing a compactification with itself gives the identity. -/
  comparison_refl (c : Compactification f) : comparison c c = Iso.refl _
  /-- The comparison isomorphisms satisfy the cocycle condition. -/
  comparison_trans (c d e : Compactification f) :
    comparison c e = comparison c d ≪≫ comparison d e
  /-- The comparisons identify the Hom bijections; this determines their components. -/
  comparison_homEquiv (c d : Compactification f) (K) (hK : P K) (L) (hL : Q L)
      (a : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d).obj K ⟶ L) :
    homEquiv c K hK L hL ((comparison c d).hom.app ⟨K, hK⟩ ≫ a) =
      homEquiv d K hK L hL a

private abbrev comparisonOriginLift (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).FullSubcategory :=
  (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).lift
    (DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]))
    (fun K ↦ DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj K.property)

private local instance comparisonOriginLift_full (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) : (comparisonOriginLift Λ X).Full where
  map_surjective {K L} a := by
    obtain ⟨b, hb⟩ :=
      (bijective_comparisonUpperStar_mapDerivedCategory_map K.obj L.obj L.property).2 a.hom
    exact ⟨ObjectProperty.homMk b, by ext; exact hb⟩

private local instance comparisonOriginLift_faithful (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) : (comparisonOriginLift Λ X).Faithful where
  map_injective {K L} a b h := by
    ext
    exact (bijective_comparisonUpperStar_mapDerivedCategory_map K.obj L.obj L.property).1
      (congrArg (fun t ↦ t.hom) h)

private local instance comparisonOriginLift_essSurj (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) : (comparisonOriginLift Λ X).EssSurj where
  mem_essImage K := by
    obtain ⟨K₀, hK₀, ⟨e⟩⟩ := K.property
    exact ⟨⟨K₀, hK₀⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

private local instance comparisonOriginLift_isEquivalence
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) :
    (comparisonOriginLift Λ X).IsEquivalence where

private def originComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d :=
  ((Functor.whiskeringLeft _ _ _).obj (comparisonOriginLift Λ X)).preimageIso
    (fixedCompactSupportOriginIso Λ c d)

private theorem originComparison_normalized (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (originComparison Λ c d).hom.app ((comparisonOriginLift Λ X).obj K) =
      (fixedCompactSupportOriginIso Λ c d).hom.app K := by
  exact congrArg (fun t ↦ t.app K)
    (((Functor.whiskeringLeft _ _ _).obj (comparisonOriginLift Λ X)).map_preimage
      (X := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c)
      (Y := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) d)
      (fixedCompactSupportOriginIso Λ c d).hom)

private theorem fixedCompactSupportOriginIso_trans
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d e : Compactification f) :
    fixedCompactSupportOriginIso Λ c d ≪≫ fixedCompactSupportOriginIso Λ d e =
      fixedCompactSupportOriginIso Λ c e := by
  ext K
  simp only [fixedCompactSupportOriginIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc]
  rw [← Etale.rightDerivedLowerShriekOfCompactificationPlusιIso_trans Λ c d e]
  simp

private theorem originComparison_trans (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d e : Compactification f) :
    originComparison Λ c d ≪≫ originComparison Λ d e = originComparison Λ c e := by
  apply ((Functor.whiskeringLeft _ _ _).obj (comparisonOriginLift Λ X)).mapIso_injective
  ext K
  simp only [Functor.mapIso_trans, Iso.trans_hom, NatTrans.comp_app,
    Functor.mapIso_hom, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app]
  rw [originComparison_normalized, originComparison_normalized, originComparison_normalized]
  exact congrArg (fun t ↦ t.hom.app K) (fixedCompactSupportOriginIso_trans Λ c d e)

private def representativeHomEquiv
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c₀ : Compactification f)
    (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀ ⊣ G)
    (hG : ∀ L, _root_.DerivedCategory.TStructure.t.plus L →
      _root_.DerivedCategory.TStructure.t.plus
        (G.obj (R(ν_*(Y)[ModuleCat.{u + 1} Λ]).obj L)))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (hL : _root_.DerivedCategory.TStructure.t.plus L) :
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀).obj
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj) ⟶ L) ≃
      ((D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj) ⟶
        (R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ G ⋙
          D(ν^*(X)[ModuleCat.{u + 1} Λ])).obj L) :=
  ((fixedCompactSupportComparisonIso Λ c₀).app K).homFromEquiv.trans
    (((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ L).trans
      ((adj.homEquiv K.obj _).trans
        (Equiv.ofBijective (fun a ↦ D(ν^*(X)[ModuleCat.{u + 1} Λ]).map a)
          (bijective_comparisonUpperStar_mapDerivedCategory_map _ _ (hG L hL)))))

private theorem representativeHomEquiv_left
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c₀ : Compactification f)
    (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀ ⊣ G)
    (hG : ∀ L, _root_.DerivedCategory.TStructure.t.plus L →
      _root_.DerivedCategory.TStructure.t.plus
        (G.obj (R(ν_*(Y)[ModuleCat.{u + 1} Λ]).obj L)))
    (K K' : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (hL : _root_.DerivedCategory.TStructure.t.plus L) (a : K ⟶ K')
    (b : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀).obj
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K'.obj) ⟶ L) :
    representativeHomEquiv Λ c₀ G adj hG K L hL
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀).map
          (D(ν^*(X)[ModuleCat.{u + 1} Λ]).map a.hom) ≫ b) =
      D(ν^*(X)[ModuleCat.{u + 1} Λ]).map a.hom ≫
        representativeHomEquiv Λ c₀ G adj hG K' L hL b := by
  have h := (fixedCompactSupportComparisonIso Λ c₀).inv.naturality_assoc a b
  change D(ν^*(Y)[ModuleCat.{u + 1} Λ]).map
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀).map
        a.hom) ≫ (fixedCompactSupportComparisonIso Λ c₀).inv.app K' ≫ b =
    (fixedCompactSupportComparisonIso Λ c₀).inv.app K ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀).map
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).map a.hom) ≫ b at h
  simp only [representativeHomEquiv, Equiv.trans_apply, Equiv.ofBijective_apply]
  dsimp only [Iso.homFromEquiv, Equiv.coe_fn_mk]
  erw [← h]
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Functor.map_comp]
  rfl

private theorem representativeHomEquiv_right
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c₀ : Compactification f)
    (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀ ⊣ G)
    (hG : ∀ L, _root_.DerivedCategory.TStructure.t.plus L →
      _root_.DerivedCategory.TStructure.t.plus
        (G.obj (R(ν_*(Y)[ModuleCat.{u + 1} Λ]).obj L)))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L L' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (hL' : _root_.DerivedCategory.TStructure.t.plus L')
    (a : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀).obj
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K.obj) ⟶ L) (b : L ⟶ L') :
    representativeHomEquiv Λ c₀ G adj hG K L' hL' (a ≫ b) =
      representativeHomEquiv Λ c₀ G adj hG K L hL a ≫
        (R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ G ⋙
          D(ν^*(X)[ModuleCat.{u + 1} Λ])).map b := by
  simp only [representativeHomEquiv, Equiv.trans_apply, Equiv.ofBijective_apply]
  dsimp only [Iso.homFromEquiv, Equiv.coe_fn_mk]
  erw [← Category.assoc]
  erw [(derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv_naturality_right
    (((fixedCompactSupportComparisonIso Λ c₀).app K).inv ≫ a) b]
  erw [adj.homEquiv_naturality_right, Functor.map_comp]
  rfl

private theorem originComparison_refl (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f) :
    originComparison Λ c c = Iso.refl _ := by
  have h := originComparison_trans Λ c c c
  ext K
  apply (cancel_epi ((originComparison Λ c c).hom.app K)).1
  simpa using congrArg (fun t ↦ t.hom.app K) h

private def buildFixedComparisonClassAdjunction
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c₀ : Compactification f)
    (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀ ⊣ G)
    (hG : ∀ L, _root_.DerivedCategory.TStructure.t.plus L →
      _root_.DerivedCategory.TStructure.t.plus
        (G.obj (R(ν_*(Y)[ModuleCat.{u + 1} Λ]).obj L))) :
    FixedComparisonClassAdjunction Λ f c₀ G adj
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X)
      _root_.DerivedCategory.TStructure.t.plus := by
  let P := DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X
  let U := comparisonOriginLift Λ X
  let F := P.ι ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀
  let R := R(ν_*(Y)[ModuleCat.{u + 1} Λ]) ⋙ G ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ])
  let e := representativeHomEquiv Λ c₀ G adj hG
  let Φ := comparisonHomDescent U F P.ι R _root_.DerivedCategory.TStructure.t.plus e
  have el := representativeHomEquiv_left Λ c₀ G adj hG
  have er := representativeHomEquiv_right Λ c₀ G adj hG
  refine
    { boundedBelow := ?_
      homEquiv := fun c K hK L hL ↦
        ((originComparison Λ c c₀).app ⟨K, hK⟩).homFromEquiv.trans (Φ ⟨K, hK⟩ L hL)
      homEquiv_normalized := ?_
      naturality_left := ?_
      naturality_right := ?_
      comparison := originComparison Λ
      comparison_normalized := fun c d K hK ↦ originComparison_normalized Λ c d K
      comparison_refl := originComparison_refl Λ
      comparison_trans := fun c d e ↦ (originComparison_trans Λ c d e).symm
      comparison_homEquiv := ?_ }
  · intro L hL
    obtain ⟨n, hn⟩ := hG L hL
    exact ⟨n, (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).isGE_mapDerivedCategory_obj
      _ n⟩
  · intro K hK L hL a
    change Φ (U.obj K) L hL
      ((originComparison Λ c₀ c₀).inv.app (U.obj K) ≫
        (fixedCompactSupportComparisonIso Λ c₀).hom.app K ≫
          ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ L).symm a) = _
    rw [originComparison_refl]
    simp only [Iso.refl_inv, NatTrans.id_app]
    change comparisonHomDescent U F P.ι R _ e (U.obj K) L hL _ = _
    rw [comparisonHomDescent_obj U F P.ι R _ e el K L hL]
    change representativeHomEquiv Λ c₀ G adj hG K L hL
      (𝟙 _ ≫ (fixedCompactSupportComparisonIso Λ c₀).hom.app K ≫
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ L).symm a) = _
    rw [Category.id_comp]
    change D(ν^*(X)[ModuleCat.{u + 1} Λ]).map
      ((adj.homEquiv _ _) ((derivedComparisonAdjunction
        (ModuleCat.{u + 1} Λ) Y).homEquiv _ L
          ((fixedCompactSupportComparisonIso Λ c₀).inv.app K ≫
            (fixedCompactSupportComparisonIso Λ c₀).hom.app K ≫
              ((derivedComparisonAdjunction
                (ModuleCat.{u + 1} Λ) Y).homEquiv _ L).symm a))) = _
    simp only [Iso.inv_hom_id_app_assoc, Equiv.apply_symm_apply]
    rfl
  · intro c K K' hK hK' L hL a b
    let a' : (⟨K, hK⟩ : P.FullSubcategory) ⟶ ⟨K', hK'⟩ := ObjectProperty.homMk a
    have h := (originComparison Λ c c₀).inv.naturality_assoc a' b
    change F.map a' ≫ (originComparison Λ c c₀).inv.app ⟨K', hK'⟩ ≫ b =
      (originComparison Λ c c₀).inv.app ⟨K, hK⟩ ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map a ≫ b at h
    change Φ ⟨K, hK⟩ L hL
      ((originComparison Λ c c₀).inv.app ⟨K, hK⟩ ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map a ≫ b) =
      a ≫ Φ ⟨K', hK'⟩ L hL ((originComparison Λ c c₀).inv.app ⟨K', hK'⟩ ≫ b)
    rw [← h]
    exact comparisonHomDescent_left U F P.ι R _ e el _ _ L hL a' _
  · intro c K hK L L' hL hL' a b
    change Φ ⟨K, hK⟩ L' hL'
      ((originComparison Λ c c₀).inv.app ⟨K, hK⟩ ≫ a ≫ b) =
      Φ ⟨K, hK⟩ L hL ((originComparison Λ c c₀).inv.app ⟨K, hK⟩ ≫ a) ≫ R.map b
    rw [← Category.assoc]
    exact comparisonHomDescent_right U F P.ι R _ e er _ L L' hL hL' _ b
  · intro c d K hK L hL a
    have h := congrArg (fun t ↦ t.inv.app ⟨K, hK⟩)
      (originComparison_trans Λ c d c₀)
    simp only [Iso.trans_inv, NatTrans.comp_app] at h
    change Φ ⟨K, hK⟩ L hL ((originComparison Λ c c₀).inv.app ⟨K, hK⟩ ≫
      (originComparison Λ c d).hom.app ⟨K, hK⟩ ≫ a) =
      Φ ⟨K, hK⟩ L hL ((originComparison Λ d c₀).inv.app ⟨K, hK⟩ ≫ a)
    rw [← h]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The normalized comparison-class datum for any specified ordinary etale adjunction
whose right functor preserves a lower bound after derived comparison direct image.
Source: blueprint thm-sf-ambient-adjoint-class, proof of clauses (2)--(3)
(blueprint: lem-sf-specified-comparison-class-construction).

Proof: on each bounded-below etale representative, compose the fixed compact-support
comparison, the comparison adjunction, the supplied etale adjunction, and full faithfulness
of comparison pullback on bounded-below targets. Descend these natural bijections along
the equivalence onto the etale-origin full subcategory. Transport the canonical etale
compactification comparisons through that same equivalence. Their identity and cocycle
laws, and compatibility with the Hom bijections, descend because the equivalence is fully
faithful. This is the existing construction `buildFixedComparisonClassAdjunction`, with
its specified-adjoint and coefficient parameters retained. -/
theorem nonempty_fixedComparisonClassAdjunction_of_boundedBelow
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c₀ : Compactification f)
    (G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c₀ ⊣ G)
    (hG : ∀ L, _root_.DerivedCategory.TStructure.t.plus L →
      _root_.DerivedCategory.TStructure.t.plus
        (G.obj (R(ν_*(Y)[ModuleCat.{u + 1} Λ]).obj L))) :
    Nonempty (FixedComparisonClassAdjunction Λ f c₀ G adj
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X)
      _root_.DerivedCategory.TStructure.t.plus) := by
  exact ⟨buildFixedComparisonClassAdjunction Λ c₀ G adj hG⟩

end AlgebraicGeometry.ProEtale
