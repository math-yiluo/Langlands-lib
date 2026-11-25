/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageKanRepresentative
public import WeilConjectures.AlgebraicGeometry.EtaleSectionsFpqcDescent
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonComposition
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonIdentity
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalRestriction
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.RightDerivedExactComposite
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
public import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-! # Geometric comparison on the existing small site models

Source: Stacks Project, Tags 099R, 00WX and 00X6
(blueprint: proposition-comparison-morphism-inverse-image).

These are the original inclusion and geometric adjunction transported by AsSmall.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The etale site model in a universe containing the coefficient ring.
Source: Stacks Tags 00VC and 099R
(blueprint: proposition-comparison-morphism-inverse-image). -/
abbrev smallModelComparisonEtaleSite (X : Scheme.{u}) := AsSmall.{max v (u + 1)} X.Etale

/-- The original etale topology transported by the model equivalence.
Source: Stacks Tags 00VC and 099R
(blueprint: proposition-comparison-morphism-inverse-image). -/
abbrev smallModelComparisonEtaleTopology (X : Scheme.{u}) :=
  (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).inducedTopology
    X.smallEtaleTopology

/-- The original inclusion transported to the two coefficient-sized models.
Source: Stacks Tag 099R (blueprint: proposition-comparison-morphism-inverse-image). -/
abbrev smallModelComparisonInclusion (X : Scheme.{u}) :
    smallModelComparisonEtaleSite.{u, v} X ⥤ coefficientProEtaleSiteModel.{u, v} X :=
  AsSmall.down ⋙ toProEt X ⋙ AsSmall.up

/-- The transported inclusion is continuous, retaining the original covers.
Source: Stacks Tag 099R (blueprint: proposition-comparison-morphism-inverse-image).
Proof: AsSmall.down is continuous for the induced etale topology, toProEt is the
existing continuous inclusion, and AsSmall.up is the existing continuous equivalence
for the coefficient-sized pro-etale topology. Compose these three continuous functors. -/
@[instance]
theorem smallModelComparisonInclusion_isContinuous (X : Scheme.{u}) :
    (smallModelComparisonInclusion.{u, v} X).IsContinuous
      (smallModelComparisonEtaleTopology.{u, v} X)
      (coefficientProEtaleModelTopology.{u, v} X) := by
  have := Functor.isContinuous_comp (toProEt X) AsSmall.up
    X.smallEtaleTopology (ProEt.topology X) (coefficientProEtaleModelTopology.{u, v} X)
  exact Functor.isContinuous_comp AsSmall.down (toProEt X ⋙ AsSmall.up)
    (smallModelComparisonEtaleTopology.{u, v} X) X.smallEtaleTopology
    (coefficientProEtaleModelTopology.{u, v} X)

/-- The comparison inverse image on the existing small models.
Source: Stacks Tag 099R (blueprint: proposition-comparison-morphism-inverse-image). -/
abbrev smallModelComparisonPullback (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallModelComparisonInclusion.{u, v} X) (Type (max v (u + 1)))
    (smallModelComparisonEtaleTopology.{u, v} X) (coefficientProEtaleModelTopology.{u, v} X)

/-- The comparison direct image on the same models.
Source: Stacks Tag 099R (blueprint: proposition-comparison-morphism-inverse-image). -/
abbrev smallModelComparisonPushforward (X : Scheme.{u}) :=
  (smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous (Type (max v (u + 1)))
    (smallModelComparisonEtaleTopology.{u, v} X) (coefficientProEtaleModelTopology.{u, v} X)

/-- The geometric comparison on the existing small models.
Source: Stacks Tag 099R (blueprint: proposition-comparison-morphism-inverse-image). -/
abbrev smallModelProEtaleComparison (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallModelComparisonInclusion.{u, v} X) (Type (max v (u + 1)))
    (smallModelComparisonEtaleTopology.{u, v} X) (coefficientProEtaleModelTopology.{u, v} X)

/-- Comparison remains left exact after transporting along the model equivalences.
Source: Stacks Tags 099R and 00X6
(blueprint: proposition-comparison-morphism-inverse-image).
Proof: the AsSmall equivalences induce equivalences on sheaves. Their conjugate of
proEtaleSiteComparison is the displayed Kan-extension adjunction, by uniqueness of left
adjoints to the same sectionwise direct image. Transport finite-limit preservation from
preservesFiniteLimits_proEtaleSiteComparison through this natural isomorphism and the two
equivalences. The transported inclusion retains all etale and pro-etale objects. -/
@[instance]
theorem smallModelComparisonPullback_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (smallModelComparisonPullback.{u, v} X) := by
  have : (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsRightAdjoint :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isRightAdjoint_inverse
  have : (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).IsRightAdjoint :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).symm.isRightAdjoint_inverse
  have : RepresentablyFlat (smallModelComparisonInclusion.{u, v} X) :=
    inferInstanceAs (RepresentablyFlat
      ((AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale) ⋙
        toProEt X ⋙ AsSmall.up))
  exact Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback
    (smallModelComparisonInclusion.{u, v} X) (Type (max v (u + 1)))
    (smallModelComparisonEtaleTopology.{u, v} X) (coefficientProEtaleModelTopology.{u, v} X)

end AlgebraicGeometry.Scheme
