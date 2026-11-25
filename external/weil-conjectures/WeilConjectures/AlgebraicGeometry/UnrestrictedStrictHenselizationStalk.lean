/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction
import WeilConjectures.AlgebraicGeometry.StrictLocalGermRestrictionIso
import WeilConjectures.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso

/-!
# Unrestricted strict-henselization stalk formula

Source: Stacks Project, Theorem 59.53.1, Tag 03Q9, first assertion
(blueprint: lem-weil-pbc-unrestricted-strict-henselization-stalk).
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- For every abelian étale sheaf, the canonical strict-local restriction is an isomorphism.
The germ map `r` is specified by its neighbourhood components; its existence and uniqueness
are supplied by `existsUnique_strictHenselizationStalkRestriction`. The canonical map is
`r ≫ strictHenselizationCohomologyComparison`, with target the cohomology of the inverse
image along the first projection of the strict-local base change.
Source: Stacks Project, Tag 03Q9, first assertion and proof
(blueprint: lem-weil-pbc-unrestricted-strict-henselization-stalk).

Proof:
1. Choose the unique germ restriction supplied by
`existsUnique_strictHenselizationStalkRestriction`.
2. The strict-local germ restriction is an isomorphism by
`isIso_strictHenselizationStalkRestriction`.
3. Apply `isIso_strictHenselization_baseChange_globalHomology` to `F` in degree zero.
The cohomology comparison is the composite of the exact inverse-image/homology
isomorphism, this base-change map on global homology, the strict-local Leray isomorphism,
and the inverse-image/single-complex isomorphism. Each factor is invertible, so its
composite with the germ restriction is invertible. -/
theorem unrestricted_strictHenselization_stalk
    {X S : Scheme.{w}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω]
    (xbar : Spec (.of Ω) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) (q : ℕ) :
    ∃ r : (Scheme.pointSmallEtale xbar).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{w + 1} f).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ⟶
        (Sheaf.Γ (Scheme.strictLocalization xbar).smallEtaleTopology
          AddCommGrpCat.{w + 1}).obj
          ((upperStar AddCommGrpCat.{w + 1} (Scheme.strictLocalizationToBase xbar)).obj
            ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
              ((rightDerivedLowerStarPlus AddCommGrpCat.{w + 1} f).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))),
      IsStrictHenselizationStalkRestriction xbar
          ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
            ((rightDerivedLowerStarPlus AddCommGrpCat.{w + 1} f).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) r ∧
        IsIso (r ≫ strictHenselizationCohomologyComparison xbar f F q) := by
  obtain ⟨r, hr, _⟩ := existsUnique_strictHenselizationStalkRestriction xbar _
  have hriso : IsIso r := isIso_strictHenselizationStalkRestriction xbar _ r hr
  exact ⟨r, hr, IsIso.comp_isIso' hriso
    (isIso_strictHenselizationCohomologyComparison f xbar F q)⟩

end AlgebraicGeometry.Etale
