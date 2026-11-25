/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstructibilityTest
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor
/-! # Classical-module comparison on coefficient-sized sites
Source: Stacks Tags 099T, 099Y and 09AK, comparison on all module sheaves and on local models.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
/-- The canonical inverse image is fully faithful, descends continuous modules,
and preserves and reflects constructibility.
Source: Stacks Tags 099T, 099Y, 09AK and 09AL
(auxiliary; not a blueprint node).

Proof: place modules in degree zero. The degree-zero embedding is fully faithful
and its objects are bounded. The bounded derived comparison therefore makes the
composite of this embedding with derived inverse image fully faithful. The exact
inverse image commutes with degree-zero embeddings, so canceling the fully faithful
target embedding proves full faithfulness on modules. For a continuous target
module, its degree-zero complex has continuous cohomology (zero outside degree zero).
Bounded classical descent supplies a derived antecedent. Taking degree-zero
cohomology and using exactness supplies a module antecedent. Finally apply the
separate finite-local-system constructibility test. -/
theorem coefficientComparison_moduleCriteria (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    (constructibleComparisonPullback X A).Full ∧
    (constructibleComparisonPullback X A).Faithful ∧
    (∀ F : ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
      (∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
        (P : AffinePresentation X I),
        IsIso (continuityMap P
          ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
            ((coefficientModelFixedScalars _ A).obj F).obj))) →
      (constructibleComparisonPullback X A).essImage F) ∧
    (∀ G : ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A),
      Scheme.IsCoefficientConstructibleEtaleModule X A G ↔
        Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A
          ((constructibleComparisonPullback X A).obj G)) := by
  obtain ⟨D, hD, hH, ⟨hS⟩⟩ := constructibleComparison_derivedFunctor X A
  obtain ⟨hff, hdesc⟩ := coefficientComparison_boundedClassical.{u, v} X A D hD
  let R := ConstantCompletion.constant (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A
  let S := ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
  obtain ⟨hfull, hfaithful⟩ := coefficientSingle_full_faithful R S
    (constructibleComparisonPullback X A) D hff hS
  refine ⟨hfull, hfaithful, ?_, coefficientComparison_constructibilityTest X A⟩
  intro F hF
  obtain ⟨M, ⟨e⟩⟩ := hdesc ((coefficientModelSingle _ 0).obj F) (coefficientSingle_bounded _ F)
    (coefficientSingle_classical.{u, v} X A F hF)
  obtain ⟨h0⟩ := hH 0
  exact ⟨(coefficientModelCohomology R 0).obj M,
    ⟨(h0.app M).symm ≪≫ (coefficientModelCohomology S 0).mapIso e ≪≫
      coefficientSingle_homologyIso S F⟩⟩
end AlgebraicGeometry.ProEtale
