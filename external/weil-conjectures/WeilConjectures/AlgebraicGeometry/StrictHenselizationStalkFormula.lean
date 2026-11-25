/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import WeilConjectures.AlgebraicGeometry.StrictLocalGermRestrictionIso
import WeilConjectures.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology

/-!
# Strict-henselization stalk formula

Source: the blueprint of the Weil conjectures, chapter
`chap-Cohomology-of-torsion-sheaves-on-curves`, node
`prop-weil-pbc-strict-henselization-stalk-formula` (Stacks Project, Tag 03Q9).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Stalks of higher direct images are étale cohomology over the strict henselization.

For a torsion sheaf `F` (torsion in the local-section sense, `Sheaf.IsTorsion`) the canonical
restriction `(R^q f_* F)_s ⟶ H^q(X ×_S S_(s), p⁻¹F)` is an isomorphism; it is
`r ≫ strictHenselizationCohomologyComparison s f F q` for the germ restriction `r`, pinned by
`IsStrictHenselizationStalkRestriction` (unique by
`existsUnique_strictHenselizationStalkRestriction`).

For `K ∈ D⁺(X_et)` with torsion cohomology sheaves, the canonical map
`(Rf_* K)_s ⟶ RΓ(X ×_S S_(s), p⁻¹K)` is an isomorphism in `D⁺(Ab)`; as the stalk is exact,
this is stated degreewise: in every degree `n` the canonical map
`H^n(Rf_* K)_s ⟶ H^n(X ×_S S_(s), p⁻¹K)` (the germ restriction `r`, then the inverse image
commuted with cohomology, the derived base-change mate `g⁻¹ Rf_* ⟶ Rf'_* p⁻¹`, and the exact
global sections and Leray isomorphism `strictHenselizationLerayHomologyIso`, i.e. the
construction of `strictHenselizationCohomologyComparison` applied to `K`) is an isomorphism.

Source: Stacks Project, Tag 03Q9, theorem-higher-direct-images
(blueprint: prop-weil-pbc-strict-henselization-stalk-formula).
The proof uses the sheafified higher-direct-image formula, geometric stalks and their
sheafification invariance, cofinal affine pointed neighborhoods, the strict-henselization
limit and fibre-product limit, and étale cohomology continuity. For the derived clause it
uses the bounded-below injective representative and the general continuity comparison;
the restriction maps induce the canonical comparison on cohomology in every degree.
-/
theorem strictHenselizationStalkFormula
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})
    (hF : F.IsTorsion) (q : ℕ) :
    (∃ r : (Scheme.pointSmallEtale s).sheafFiber.obj
          ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
            ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ⟶
          (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
            AddCommGrpCat.{v + 1}).obj
            ((upperStar AddCommGrpCat.{v + 1} (Scheme.strictLocalizationToBase s)).obj
              ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
                ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj
                  ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))),
        IsStrictHenselizationStalkRestriction s
            ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
              ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) r ∧
          IsIso (r ≫ strictHenselizationCohomologyComparison s f F q)) ∧
    ∀ (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})),
      Scheme.HasTorsionEtaleCohomology ((DerivedCategory.Plus.ι).obj K) → ∀ n : ℤ,
      ∃ r : (Scheme.pointSmallEtale s).sheafFiber.obj
          ((DerivedCategory.Plus.homologyFunctor _ n).obj
            ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K)) ⟶
          (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
            AddCommGrpCat.{v + 1}).obj
            ((upperStar AddCommGrpCat.{v + 1} (Scheme.strictLocalizationToBase s)).obj
              ((DerivedCategory.Plus.homologyFunctor _ n).obj
                ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K))),
        IsStrictHenselizationStalkRestriction s
            ((DerivedCategory.Plus.homologyFunctor _ n).obj
              ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K)) r ∧
          IsIso (r ≫
            (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
              AddCommGrpCat.{v + 1}).map
              ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
                (upperStar AddCommGrpCat.{v + 1} (Scheme.strictLocalizationToBase s))
                n).hom.app _) ≫
            (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
              AddCommGrpCat.{v + 1}).map
              ((DerivedCategory.Plus.homologyFunctor _ n).map
                ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
                  (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
                    (pullback.snd f (Scheme.strictLocalizationToBase s))).derivedPlus
                  (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
                    (IsPullback.of_hasPullback f
                      (Scheme.strictLocalizationToBase s)).toCommSq).hom))
                    |>.app K)) ≫
            (strictHenselizationLerayHomologyIso s f n _).hom) := by
  constructor
  · exact (fun (_ : F.IsTorsion) ↦ unrestricted_strictHenselization_stalk f s F q) hF
  · intro K _ n
    obtain ⟨r, hr, _⟩ := existsUnique_strictHenselizationStalkRestriction s
      ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K))
    have := isIso_strictHenselizationStalkRestriction s _ r hr
    have := isIso_strictHenselization_baseChange_globalHomology f s K n
    exact ⟨r, hr, inferInstance⟩

end AlgebraicGeometry.Etale
