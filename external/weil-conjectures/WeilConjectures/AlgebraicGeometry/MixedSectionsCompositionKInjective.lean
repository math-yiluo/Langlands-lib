/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomPullbackComparison
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate
import WeilConjectures.AlgebraicGeometry.DirectImageGlobalSectionsKInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.MixedSectionsLeftUnitNormalization
import WeilConjectures.AlgebraicGeometry.MixedSectionsRightUnitNormalization

/-! # Mixed Leray composition on K-injective complexes
Source: Stacks Project, cohomology.tex, Tags 08HY, 0D5T and 0D5W.
(blueprint: lem-sc-mixed-sections-composition-kinjective).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

-- Checking the canonical comparisons expands sheaf and derived-functor instances.
/-- Composition coherence computed on a K-injective complex.
Source: Stacks Project, Cohomology, Tags 0D5T and 0D5W.
(blueprint: lem-sc-mixed-sections-composition-kinjective).

Proof: Put K = quotient(I), Df = f_* and Dg = g_* on module sheaves, and write
ΓX, ΓY, ΓZ for underived global sections. Precompose the asserted equality with
unit_ΓZ(Dg(Df K)), ΓZ(unit_Dg(Df K)), and ΓZ(RDg(unit_Df(K))). The first is
invertible by global-sections acyclicity for the composite direct image; the
composition of the last two is invertible because the normalized composition
unit equation identifies it with ΓZ(unit_D(fg)(K)) followed by the inverse
composition comparison. The unit of D(fg) at I is invertible by K-injectivity.
On the left, naturality of the mixed comparison for g moves RDg(unit_Df) across
c_g. Apply the normalized mixed Leray unit equations for g at Df(K) and f at K.
Functoriality reduces this path to factor_g;Sg(factor_f);Sg(Sf(unit_ΓX(K))).
On the right, the normalized direct-image composition equation removes the
composition comparison. Apply the mixed Leray unit equation for fg, and use
naturality of the scalar-composition comparison to move unit_ΓX to the end.
The remaining equality is factor_g;Sg(factor_f)=factor_fg;s(f,g) at ΓX(K).
It follows by composing mapDerivedCategoryCompIso_fach with
mapDerivedCategoryNatIso_fach for restrictScalarsComp'. Its underived components
are identity on elements; their homotopy maps are identities and localization
preserves these. Cancel the precomposed isomorphism. This calculation uses no
resolution transport, and works for identity morphisms, the zero complex and
empty schemes, with the two localization universes kept independent. -/
theorem mixedSections_composition_coherence_on_kInjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] :
    let F := DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)
    let e : schemeDerivedDirectImage f ⋙ schemeDerivedDirectImage g ≅
        schemeDerivedDirectImage (f ≫ g) :=
      schemeNormalizedDirectImageCompIso f g
    (mixedGlobalSectionsDirectImageIso g).hom.app ((schemeDerivedDirectImage f).obj F) ≫
        (schemeGlobalScalarRestriction g).map
          ((mixedGlobalSectionsDirectImageIso f).hom.app F) =
      (schemeDerivedGlobalSections Z).map (e.hom.app F) ≫
        (mixedGlobalSectionsDirectImageIso (f ≫ g)).hom.app F ≫
        (schemeGlobalScalarRestrictionCompIso f g).hom.app
          ((schemeDerivedGlobalSections X).obj F) := by
  let K := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  let Dfg := RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom
  let HZ := RingedSpace.globalSectionsFunctor Z.toRingedSpace
  let e := schemeNormalizedDirectImageCompIso f g
  let a := HZ.rightDerivedFunctorUnit.app ((Dfg.mapHomotopyCategory (.up ℤ)).obj K)
  let t := Dfg.rightDerivedFunctorUnit.app K
  have : IsIso a := isIso_directImage_globalSections_unit_on_kInjective (f ≫ g) I
  have : IsIso t := inferInstance
  let p := a ≫ (schemeDerivedGlobalSections Z).map t ≫
    (schemeDerivedGlobalSections Z).map (e.inv.app (DerivedCategory.Qh.obj K))
  have : IsIso p := by dsimp [p]; infer_instance
  apply (cancel_epi p).1
  exact (mixedSections_left_unit_normalization f g I).trans
    (mixedSections_right_unit_normalization f g I).symm

end AlgebraicGeometry
