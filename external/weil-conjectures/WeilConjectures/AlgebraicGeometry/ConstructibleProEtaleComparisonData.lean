/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! # Canonical inverse image for constructible comparison

Source: Stacks Tags 099R, 00WX, 03D2 and 09AL.
The three constructions are retained verbatim from ConstructibleProEtaleComparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace AlgebraicGeometry.ProEtale

/-- The constant-section map on the recorded equivalent sites. This is sheafification of
`a ↦` the constant section `a`, along the transported inclusion of etale objects.
Source: Stacks Tags 099R and 00WX; blueprint constructible comparison, proof step 1
(blueprint: theorem-comparison-constructible-sheaves). -/
def constructibleComparisonRingMap (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    siteModuleRings (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⟶
    ((Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
      RingCat.{max v (u + 1)} (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).obj
        (siteModuleRings (ConstantCompletion.constant
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)) :=
  (sheafCompose (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)})).map
    (((sheafificationAdjunction (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      CommRingCat.{max v (u + 1)}).homEquiv
        ((Functor.const (Scheme.smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ).obj
          (CommRingCat.of A))
        ((Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
          CommRingCat.{max v (u + 1)} (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) |>.obj
            (ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, v} X)
              A))).symm
        (Functor.whiskerLeft (Scheme.smallModelComparisonInclusion.{u, v} X).op
          (toSheafify (Scheme.coefficientProEtaleModelTopology.{u, v} X)
            ((Functor.const _).obj (CommRingCat.of A)))))

/-- Module comparison inverse image, constructed by module Kan extension and sheafification.
The ring map is the canonical constant-section map, so this is inverse image with the
canonical identification of the constant coefficient rings. No arbitrary map is chosen.
Source: Stacks Tags 00WX and 03D2; blueprint constructible comparison, proof steps 1 and 3
(blueprint: theorem-comparison-constructible-sheaves). -/
abbrev constructibleComparisonPullback (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
    ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A) :=
  SheafOfModules.pullback.{max v (u + 1)}
    (F := Scheme.smallModelComparisonInclusion.{u, v} X) (constructibleComparisonRingMap X A)

/-- Termwise comparison pullback on cochain complexes. Zero-morphism preservation is
supplied by Mathlib's theorem for the existing module pullback adjunction, explicitly
rather than by an expensive instance search. No mathematical assertion is postponed here.
Source: Stacks Tag 09AL; blueprint constructible comparison, proof step 4
(blueprint: theorem-comparison-constructible-sheaves). -/
def constructibleComparisonComplexPullback (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    ConstantCompletion.Cx (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
    ConstantCompletion.Cx (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A) :=
  @Functor.mapHomologicalComplex ℤ _ _ _ _ _ _ (constructibleComparisonPullback X A)
    (@Functor.preservesZeroMorphisms_of_isLeftAdjoint _ _ _ _ _ _ _
      (SheafOfModules.pullbackPushforwardAdjunction
        (F := Scheme.smallModelComparisonInclusion.{u, v} X)
        (constructibleComparisonRingMap X A)).isLeftAdjoint) (.up ℤ)

end AlgebraicGeometry.ProEtale
