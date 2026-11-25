/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteReductionPullback
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.CategoryTheory.SiteCoveringAxioms

/-!
# Inverse image of the three coefficient comparisons

md`, clauses 1--3
(blueprint: lemma-comparison-completed-coefficients--4).

The integral comparison is normalized by the same adjunction mate as its dependency.
Localization is stated for any module-colimit representatives with their localization
ring structures. The algebraic-closure clause uses the published finite-subextension cocone.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The normalization of the integral comparison from the integral-limit dependency:
its adjunction mate is reduction on every profinite test object, using the natural
finite-label representation. This predicate introduces no new coefficient object.
Source: blueprint integral-limit clause 3 and pullback proof Steps 2--3
(blueprint: lemma-comparison-completed-coefficients--4). -/
def SfbIntegralComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (e : (coefficientRing X (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E X) :
    Prop :=
  IsMonHom e.hom ∧ IsMonHom e.inv ∧
    ∃ (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
      (c : Cone (sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite))
      (j : sfbIntegralProfinite l E ≅ c.pt),
      (∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers l E),
        (j.hom ≫ c.π.app (op n)) x =
          Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x) ∧
      Nonempty (IsLimit c) ∧
      ∀ (S : Profinite.{u}) (g : S ⟶ sfbIntegralProfinite l E) (n : ℕ),
        (sfbIntegralFiniteRepresentation l E X a n).hom.app
            (op ((profiniteToProEtOf X).obj S))
          (((limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app
              (op ((profiniteToProEtOf X).obj S)))
            ((e.hom.hom.app (op ((profiniteToProEtOf X).obj S)))
              (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
                (op S) (ULift.up g.hom.hom)))) =
          ULift.up ((profiniteToProEtOf X).map (g ≫ j.hom ≫ c.π.app (op n)))

end AlgebraicGeometry.ProEtale
