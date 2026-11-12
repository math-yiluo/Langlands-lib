import Langlands.Geometry.Building.ParahoricDoubleCosetComponents
import Langlands.Geometry.Building.AffineIwahoriTitsStatement
import Langlands.Geometry.Building.FacetParabolicComparisonStatement

/-!
# The corrected KP Theorem 7.8.1(2),(3) from their structural inputs

For the actual data `P : ParahoricBuildingData G`, the chamber splitting of KP 7.8.2 together
with the actual affine Iwahori–Tits system of KP Theorem 7.5.3 gives the fixed-data
conclusion `P.IwahoriDoubleCosetBijection C`, and the chamber splitting together with the
common-chamber facet comparisons of KP Proposition 7.5.5 gives
`P.ParahoricDoubleCosetBijection F₁ F₂`. The global forms reduce
`IwahoriDoubleCosetStatement` and `ParahoricDoubleCosetStatement` to the three published
statements `IwahoriWeylChamberSplittingStatement`, `AffineIwahoriTitsStatement` and
`FacetParabolicComparisonStatement`, which are explicit hypotheses here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- KP Theorem 7.8.1(2) for a chamber `C` of fixed data, from the chamber splitting of
KP 7.8.2 and the actual affine Iwahori–Tits system of KP Theorem 7.5.3 for `C`. -/
theorem iwahoriDoubleCosetBijection_of_splitting_of_affineIwahoriTits
    [P.normalizerZero.Normal] [P.zeroSubgroup.Normal] {C : Set P.Apartment}
    (hsplit : P.IwahoriWeylChamberSplitting C) (htits : P.AffineIwahoriTits C) :
    P.IwahoriDoubleCosetBijection C := by
  obtain ⟨_, hT⟩ := htits
  exact P.iwahoriDoubleCosetBijection_of_zeroTits C hT.parahoric_le_zero
    P.affineTitsProjection_coe hT.tits
    (P.chamberStabilizer_toComponents_surjective_of_splitting hsplit)

/-- KP Theorem 7.8.1(3) for faces `F₁`, `F₂` of a chamber `C` of fixed data, from the chamber
splitting of KP 7.8.2 and the common-chamber facet comparisons of KP Proposition 7.5.5, which
share one actual affine Iwahori–Tits system for `C`. -/
theorem parahoricDoubleCosetBijection_of_splitting_of_commonChamberFacetParabolics
    [P.normalizerZero.Normal] [P.zeroSubgroup.Normal] {C F₁ F₂ : Set P.Apartment}
    (hsplit : P.IwahoriWeylChamberSplitting C)
    (hfacet : P.CommonChamberFacetParabolics C F₁ F₂) :
    P.ParahoricDoubleCosetBijection F₁ F₂ := by
  obtain ⟨e, hT, h₁, h₂⟩ := hfacet
  exact P.parahoricDoubleCosetBijection_of_zeroTits_subgroupOf C hT.parahoric_le_zero
    P.affineTitsProjection_coe hT.tits
    (P.chamberStabilizer_toComponents_surjective_of_splitting hsplit)
    (P.facetSimpleInAffinePart_subset e C F₁) (P.facetSimpleInAffinePart_subset e C F₂)
    h₁.weyl_stabilizer.symm h₂.weyl_stabilizer.symm
    h₁.parahoric_le_zero h₂.parahoric_le_zero h₁.parabolic_eq h₂.parabolic_eq

end ParahoricBuildingData

/-- The reduction of the corrected KP Theorem 7.8.1(2),(3) to their structural inputs: the
chamber splitting (KP 7.8.2) and the actual affine Iwahori–Tits system (KP Theorem 7.5.3)
imply `IwahoriDoubleCosetStatement`, and the chamber splitting and the common-chamber facet
comparisons (KP Proposition 7.5.5) imply `ParahoricDoubleCosetStatement`. -/
def DoubleCosetStatementReductionStatement : Prop :=
  (IwahoriWeylChamberSplittingStatement.{u} → AffineIwahoriTitsStatement.{u} →
      IwahoriDoubleCosetStatement.{u}) ∧
    (IwahoriWeylChamberSplittingStatement.{u} → FacetParabolicComparisonStatement.{u} →
      ParahoricDoubleCosetStatement.{u})

/-- `IwahoriDoubleCosetStatement` from the chamber splitting and the actual affine
Iwahori–Tits system. -/
theorem iwahoriDoubleCosetStatement_of_statements
    (hsplit : IwahoriWeylChamberSplittingStatement.{u})
    (htits : AffineIwahoriTitsStatement.{u}) : IwahoriDoubleCosetStatement.{u} := by
  intro F _ _ _ _ G _ P hA C hC
  obtain ⟨_, _, hT⟩ := htits F G P hA C hC
  exact P.iwahoriDoubleCosetBijection_of_splitting_of_affineIwahoriTits
    (hsplit F G P hA C hC) hT

/-- `ParahoricDoubleCosetStatement` from the chamber splitting and the common-chamber facet
comparisons. -/
theorem parahoricDoubleCosetStatement_of_statements
    (hsplit : IwahoriWeylChamberSplittingStatement.{u})
    (hfacet : FacetParabolicComparisonStatement.{u}) : ParahoricDoubleCosetStatement.{u} := by
  intro F _ _ _ _ G _ P hA C F₁ F₂ hC h₁ h₂
  obtain ⟨_, _, hP⟩ := hfacet F G P hA C F₁ F₂ hC h₁ h₂
  exact P.parahoricDoubleCosetBijection_of_splitting_of_commonChamberFacetParabolics
    (hsplit F G P hA C hC) hP

/-- Proof of the reduction `DoubleCosetStatementReductionStatement`. -/
theorem doubleCosetStatementReduction : DoubleCosetStatementReductionStatement.{u} :=
  ⟨iwahoriDoubleCosetStatement_of_statements, parahoricDoubleCosetStatement_of_statements⟩

end Langlands.Geometry.Building
