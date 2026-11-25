/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonSquareEtalePathNormalizationSupplement
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonSquareProEtalePathNormalizationSupplement

/-! # Derived transport of a coherent comparison square -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Derived pullback comparisons transport an underived coherent square to the bounded-below
comparison square. This is the categorical transport portion of
`comparison_square`; the underived square is supplied separately so that arbitrary commutative
coefficient rings are allowed.
Source: blueprint `stage3-proetale-comparison-square`, proof step 4; Stacks Project, Tag 0B65.
(blueprint: stage3-proetale-comparison-square-transport)

Proof: the component equations make the two pasted natural transformations equal by
extensionality. Apply the exact functors degreewise to complexes and localize at
quasi-isomorphisms. The naturality and associativity equations for
`mapDerivedCategoryCompIso` identify the resulting pasted maps with the induced maps on
unbounded derived categories. Conjugate the pro-étale pullbacks by
`leftDerivedUpperStarIsoMapDerivedCategory`; its composition and equality-transport
compatibilities identify the conjugated square with `leftDerivedUpperStarSquareIso`.
On the étale side restrict along the bounded-below inclusion and use
`mapDerivedCategoryPlusCompatibility` for each edge and each composition. Cancel the
invertible comparison factors. The remaining composites are exactly the displayed equation.
Only the supplied component equations enter this calculation; it does not invoke the theorem
`comparison_square` or a theorem asserting underived coherence.
-/
theorem comparison_square_of_component
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hcomp : ∀ F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      ComparisonSquareComponent
        (comparisonSquareData (ModuleCat.{u + 1} Λ) g' f' f g
          { toCommSq := sq.toCommSq
            isoPullback := sq.isoPullback
            hom_fst := sq.isoPullback_hom_fst
            hom_snd := sq.isoPullback_hom_snd }) F) :
    (DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).map
        ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M) ≫
      (leftDerivedUpperStarComparisonIso g' Λ).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
        ((leftDerivedUpperStarComparisonIso f Λ).hom.app M) =
    (leftDerivedUpperStarComparisonIso f' Λ).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f').map
        ((leftDerivedUpperStarComparisonIso g Λ).hom.app M) ≫
      (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app
        ((DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj M) := by
  let cs : ChosenCartesianSquare g' f' f g :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  have he : comparisonSquareEtalePath Λ cs = comparisonSquareProEtalePath Λ cs :=
    comparisonSquarePaths_eq (comparisonSquareData (ModuleCat.{u + 1} Λ) g' f' f g cs) hcomp
  have hL := comparisonSquareEtalePath_normalization Λ sq M
  have hR := comparisonSquareProEtalePath_normalization Λ sq M
  have hd := congrFun (congrArg (comparisonSquareDerivedPath Λ g' f' f g) he) M
  exact eq_of_heq (HEq.trans (HEq.symm hL) (HEq.trans (heq_of_eq hd) hR))

end AlgebraicGeometry.ProEtale
