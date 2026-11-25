/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Linear.FunctorCategory
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceExists
import WeilConjectures.AlgebraicGeometry.DirectImageSplitCoverProduct
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleModuleTraceData

/-!
# Coefficient-linear finite étale trace with prescribed degree

Source: Stacks Project, Section 03SH (section-trace-method), Definition 03SE
(definition-trace-map) and the restriction/trace composite following it.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A finite étale map with geometric fibres of cardinality `d` admits a coefficient-linear
trace whose composite with restriction is `d` times the identity. No invertibility of `d`
is assumed, and the coefficients may be any commutative ring.

Source: Stacks Project, Section 03SH (section-trace-method), Definition 03SE
(definition-trace-map), its characterization, and the following degree formula.
(blueprint: lem-weil-pbc-finite-etale-module-trace-degree)

Proof: Choose jointly surjective étale neighbourhoods splitting the finite étale map into
finitely many copies of the neighbourhood (Stacks 04HN). A geometric point of each
nonempty neighbourhood identifies the summands with the lifts of that point, so the
hypothesis makes their number `d`. On these neighbourhoods the pullback/direct-image
adjunction identifies its unit with the diagonal map into the product of the copies of
`G`. Define the trace by adding the coordinates. Each coordinate projection and addition
is coefficient-linear. The sum is invariant under permutations; on overlaps the two
splittings differ locally by permutations, so their sums coincide. The sheaf condition
therefore glues these local maps to a coefficient-linear sheaf morphism. On a splitting
neighbourhood the composite sends a section `s` to the sum of `d` copies of `s`, namely
`d • s`. Equality of morphisms is checked after this jointly surjective covering by sheaf
separatedness, giving the global formula. Empty fibres give the zero sum and the same
formula for `d = 0`; the degree-one case gives the identity. No local constancy, finite
rank, connectedness of the cover, or characteristic assumption is required. -/
theorem exists_finiteEtaleModuleTrace_degree
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (d : ℕ)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nat.card (f.GeometricFiber s) = d) :
    ∃ t : (f)_*[ModuleCat.{u + 1} R].obj ((f)^*[ModuleCat.{u + 1} R].obj G) ⟶ G,
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G ≫ t =
        (d : R) • 𝟙 G := by
  obtain ⟨h, _⟩ := finiteEtaleModuleTraceData R f G d hdeg
  exact h

end AlgebraicGeometry.Etale
