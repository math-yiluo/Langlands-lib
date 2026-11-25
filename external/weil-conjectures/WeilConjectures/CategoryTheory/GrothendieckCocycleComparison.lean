/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckComposablePair
import WeilConjectures.CategoryTheory.HypercohomologyEdgeCocycle
import WeilConjectures.CategoryTheory.GrothendieckHypercohomologyEdge

/-! # Comparing the Grothendieck edge with the cocycle quotient

Source: Stacks Project, Derived Categories, Tags 015N and 015J, with the
quotient/inclusion edge of the double-complex model
(blueprint: lem-pc-grothendieck-cocycle-comparison).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The fixed-degree comparison between the abstract left edge and the cocycle quotient.
The morphism c is given, and only its compatibility with the cycle inclusions is assumed.
This lemma asserts no existence of c, no filtration properties, and no collapse criterion.

Source: the Cartan--Eilenberg construction of Stacks Project, Derived Categories,
Tags 015N and 015J; the explicit cocycle calculation in step 2 of
lem-pc-grothendieck-edge-cocycle
(blueprint: lem-pc-grothendieck-cocycle-comparison).

Proof:
Choose a Cartan--Eilenberg resolution of F(I), extending I by zero in negative degrees.
Apply grothendieckSSDoubleComplexModel to its presentation with the given resolution I.
The model gives the augmentation a from GF(I) to the total complex, the abutment
isomorphisms h, and the quotient/inclusion description of the left edge. Its equation
for homologyMap a identifies h with I.isoRightDerivedObj (F composed with G) inverse.
Each term F(I^q) is G-acyclic by hFG and injectivity of I^q. Consequently the
augmentation into its resolved column becomes a quasi-isomorphism after G.
For the other filtration, the horizontal cycles, boundaries and cohomology of the
Cartan--Eilenberg resolution are injective. Their short exact sequences split, so
applying G commutes with their horizontal cohomology. The resolved cohomology row
computes R^p G(H^n(F(I))), and its degree-zero cycles identify E2^{0,n} with
G(H^n(F(I))) through the canonical rightDerivedZeroIsoSelf.
Precompose the augmentation's homology map with c followed by the homology quotient.
The inclusion condition on c says that its representative is G of the original cycle
inclusion. The quotient by the first filtration step takes the resolution-degree-zero
component; under the horizontal-cohomology identification this component is precisely
G of the quotient from cycles to H^n(F(I)). Explicitly, write U for the horizontal
degree-zero-resolution row, b: H^n(F(I)) -> H^n(U) for its induced augmentation,
and a_Z: Z^n(F(I)) -> Z^n(U) for the map on cycles. Naturality of the homology
quotient gives a_Z followed by the quotient of U equal to the quotient of F(I)
followed by b. Apply G to this equality; the split horizontal sequences identify
the quotients after G with G of these quotients. The resulting class lies in the
kernel of the next resolution differential because b is an augmentation of a
resolution. The degree-zero resolution comparison sends this class back to
G(H^n(F(I))). There are no incoming boundaries at resolution degree zero.
The stable-page inclusion into E2 preserves this representative; the transpose
sign is (-1)^(n*0)=1 on this summand. Substitute the model's left-edge and
augmentation equations.
Finally identify H^n(F(I)) with R^n F(X) by I.isoRightDerivedObj F n, giving the displayed
equality. Any two lifts c satisfying the inclusion condition agree, since iCycles is
monic, so the calculation applies to the given c, independently of the CE resolution.
-/
theorem grothendieck_cocycle_comparison
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (X : A) (I : InjectiveResolution X) (n : ℕ)
    (c : G.obj
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles n) ⟶
      (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles n)
    (hc : c ≫
        (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles n =
      G.map (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles n)) :
    c ≫ (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ n ≫
        (I.isoRightDerivedObj (F ⋙ G) n).inv ≫
        (F.grothendieckLeftEdgeMap G hFG n).app X ≫
        G.map (I.isoRightDerivedObj F n).hom =
      G.map (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ n) := by
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have h := G.cochainHypercohomologyLeftEdge_cocycle K n c hc
  have e := grothendieckLeftEdgeMap_eq_hypercohomology F G hFG X I n
  rw [← e] at h
  exact h

end CategoryTheory
