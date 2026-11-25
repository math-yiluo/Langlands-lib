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
import all WeilConjectures.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange
/-- The open restricted composition map followed by the pulled back counit
factors through the inverse of the representative restriction map.

Proof: write q and p for the two projections of the pullback square. Apply
 the defining left-derived counit factorization for the chosen composition
 comparison, first to q followed by the open immersion and then to p followed
 by g'. Naturality of the counit identifies the restriction term with the
 literal restricted complex. The characterization of the representative
 restriction isomorphism by the exact restriction adjunction replaces the
 remaining q-factor by its inverse. The two tensor-composition comparisons
 are, by construction, the components of `openTensorRestrictionSquareIso`;
 after localization their composite is `openRestrictedTensorDerivedIso`.
Associativity and cancellation of the displayed isomorphisms give exactly the
factorization equation. This uses no stalk or cohomology calculation and also
covers empty opens and zero complexes by the same naturality equations.
Source: Stacks Project, Tags 0D5S and 0D5U.
(blueprint: lem-pc-open-restricted-counit-factorization). -/
private theorem openRestricted_counit_factorization_private
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P) ≫
        (derivedPullback (pullback.fst g' U.ι)).map
          ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (derivedPullback (pullback.snd g' U.ι)).map
          (openRestrictionRepresentativeIso U.ι P).inv ≫
        (counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (openRestrictedTensorDerivedIso g' U P).inv  := by
  have h := openRestricted_counit_compatibility_aux g' U P
  apply (cancel_epi ((derivedPullback (pullback.snd g' U.ι)).map
    (openRestrictionRepresentativeIso U.ι P).hom)).1
  rw [h]
  simp only [← Category.assoc]
  rw [← Functor.map_comp, Iso.hom_inv_id]
  simp

/-- Public export of the private `openRestricted_counit_factorization_private`
(used by `import all` importers; linter.privateModule). -/
alias openRestricted_counit_factorization := openRestricted_counit_factorization_private

end AlgebraicGeometry.SingleComplexBaseChange
