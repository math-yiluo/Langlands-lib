/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionDerivedPull
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPullTransport

/-!
# Ordinary finite reduction of constant-to-completed scalar insertion

Source: Stacks Project, sites-modules.tex, Tags 03EK, 03EL, 093M;
sites-cohomology.tex, Tag 06YY.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ConstantCompletion

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']
variable {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)

/-- Ordinary scalar insertion becomes invertible after extension to a finite quotient.
Source: Stacks Project, sites-modules.tex, Tags 03EK, 03EL, 093M;
sites-cohomology.tex, Tag 06YY.
(auxiliary; not a blueprint node).

Proof: write R and B for the constant and completed ring sheaves, S for the
finite quotient, and phi, q and p for R to B, R to S and B to S. Use primes for
the second site and c for completedMap. Let k identify F(S) with S'.
The common-quotient comparison gives Res(phi) followed by change(q) isomorphic
to change(p), with s tensor m preserved, and gives the analogous isomorphism
on the second site. The normalized inverse-image/scalar-extension comparison
then identifies the reduced source with change(p) followed by pull(S), and
hence with (F.algebra B).modules followed by change(F.rings.map p followed by k).
For the target, first use the second common-quotient comparison, then scalar
associativity: pull(B) followed by Res(phi') and change(q') identifies with
(F.algebra B).modules followed by change(c followed by p').
By the defining limit-projection equation for c, c followed by p' equals
F.rings.map p followed by k. Thus source and target identify with the same
ordinary S'-module functor. On the quotient unit ordinaryPullComparison sends
1 tensor m to 1 tensor m by its defining insertion equation. The normalized
coefficient comparison and scalar associativity preserve these units, so the
adjunction hom equivalence identifies the reduced comparison followed by the
target isomorphism with the source isomorphism. Cancel the target isomorphism.
This is the ordinary common-quotient insertion argument, transported along
F.constants and the prescribed scalar-extension presentations; it involves no
complexes or derived-category computation. It also covers I = 0, I = A and the
zero ring. -/
theorem ordinaryReducedPull_isIso
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    IsIso (Functor.whiskerRight (ordinaryPullComparison F A I)
      (change (quotient J' A I n))) := by
  let _adj := adj
  obtain ⟨X, s, t, h⟩ := ordinaryReducedPull_transport F V adj A I n
  have hi : IsIso (Functor.whiskerRight (ordinaryPullComparison F A I)
      (change (quotient J' A I n)) ≫ t.hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (Functor.whiskerRight (ordinaryPullComparison F A I)
      (change (quotient J' A I n))) t.hom

end CategoryTheory.ConstantCompletion
