/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonComposition
import all WeilConjectures.AlgebraicGeometry.OpenRestrictedCounitFactorization

/-! # The counit equation for literal open restriction

Source: Stacks Project, Tags 0D5S and 0D5U.
(blueprint: lem-pc-open-restricted-counit-compatibility).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- The constructed representative and composition maps respect the pullback counit.
This equation precedes stalks and cohomology and does not invert any counit.

Proof: put j = U.ι, p and q for the two pullback projections and Pg for
termwise g'-pullback of P. The tensor-to-restriction natural isomorphisms
for j and p are the unique comparisons of left adjoints to the same
pushforward, with the chosen tensor adjunctions. Their universal derived
comparisons are openDerivedRestrictionIso. The factorization equation for
leftDerivedUnique identifies openRestrictionRepresentativeIso with the
inverse exact-restriction localization factor followed by this comparison.
Evaluate the defining leftDerivedLift equation for the two composition
isomorphisms, at the homotopy quotient of P, for (q,j) and (p,g'). Each
composition counit is the first pullback's counit followed by the second
pullback's counit and the localized tensor-composition isomorphism.
Use the pullback condition q;j = p;g' to identify the direct pullbacks;
stalks are not involved. Naturality of the counit for q with the tensor-to-
restriction isomorphism for j identifies its input with the literal Q.
The corresponding factor for p at Pg is the representative isomorphism.
The remaining two tensor-composition factors and the two open comparisons
are exactly openTensorRestrictionSquareIso, hence its localized chain
isomorphism is openRestrictedTensorDerivedIso. Cancel the composition
isomorphisms to obtain the displayed equality. This holds for every P,
without K-flatness, counit invertibility, a base-change square to S,
or a chosen point or cohomological degree. Top and empty opens and zero
complexes use the same natural-transformation equations.
Source: Stacks Project, Tag 0D5S, pullback composition; Tag 0D5U, exact
restriction to an open subspace.
(blueprint: lem-pc-open-restricted-counit-compatibility). -/
private theorem openRestricted_counit_compatibility_private
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let Q := ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
    (derivedPullback (pullback.snd g' U.ι)).map (openRestrictionRepresentativeIso U.ι P).hom ≫
        openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P) ≫
        (derivedPullback (pullback.fst g' U.ι)).map
          ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) ≫
        (openRestrictedTensorDerivedIso g' U P).inv := by
  dsimp only
  rw [openRestricted_counit_factorization]
  simp

/-- Public export of the private `openRestricted_counit_compatibility_private`
(used by `import all` importers; linter.privateModule). -/
alias openRestricted_counit_compatibility := openRestricted_counit_compatibility_private

end AlgebraicGeometry.SingleComplexBaseChange
