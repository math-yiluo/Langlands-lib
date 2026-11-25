/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.GabberH1TorsorCohomologyBridge
import WeilConjectures.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial

/-!
# Gabber's vanishing of first constant étale cohomology

Source: Stacks Project, Étale Cohomology, Lemma 09ZB
(blueprint: lem-weil-pbc-gabber-h1-absolutely-algebraically-closed).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Étale Cohomology, Lemma 09ZB
(blueprint: lem-weil-pbc-gabber-h1-absolutely-algebraically-closed).
For a normal domain with separably closed fraction field, first étale cohomology of any
finite constant abelian sheaf on any closed subscheme of its spectrum vanishes.

Proof outline:
1. By `thm-galois-torsor-h1` (Stacks 03AJ), a degree-one cohomology class corresponds
   to a torsor under the constant sheaf. It suffices to trivialize this torsor.
2. The torsor is finite locally constant (`def-weil-pbc-finite-torsors`), so
   `thm-galois-lc-etale` (Stacks 03RV) represents it by a finite étale scheme over `Z`.
   The representing morphism is surjective because the torsor is locally trivial.
3. `lem-weil-pbc-gabber-finite-etale-section` (Stacks 09ZA) gives a section of that
   morphism. This is a global section of the torsor. Translation by it trivializes
   the torsor, so the original class is zero. Thus every degree-one class is zero. -/
theorem isZero_constant_cohomology_one_of_isIntegrallyClosed
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsSepClosed (FractionRing R)] (Z : Scheme.{u})
    (i : Z ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion i]
    (M : Type (u + 1)) [AddCommGroup M] [Finite M] :
    IsZero ((cohomology AddCommGrpCat.{u + 1} Z 1).obj
      ((DerivedCategory.singleFunctor (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)))) := by
  apply isZero_constant_cohomology_one_of_torsors_trivial R Z i M
  exact torsors_trivial_of_finite_etale_sections R Z i M

end AlgebraicGeometry.Etale
