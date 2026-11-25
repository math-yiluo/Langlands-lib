/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.AlgebraicGeometry.Curve.ConstructiblePrimeFieldFiltration
import WeilConjectures.AlgebraicGeometry.Curve.UnderlyingAbelianAssertions
import WeilConjectures.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions

/-! # Prime devissage for constructible module sheaves

Source: Stacks Project, Theorem 59.83.10 (03SC), second paragraph of the proof.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- On a fixed reduced curve, the eight assertions for constructible prime-field sheaves
imply the assertions for constructible sheaves over any finite coefficient ring.
Source: Stacks Project, Theorem 59.83.10 (03SC), second proof paragraph.
(blueprint: lem-weil-pbc-constructible-prime-module-devissage)

Proof: Since Λ is finite, its additive group has a positive exponent N, so N • 1 = 0
in Λ. Every Λ-module, and hence F, is killed by N. Decompose F into the
kernels of its prime-power annihilators using the Chinese remainder idempotents. They
are constructible because constructible sheaves form a Serre subcategory over finite Λ.
For an r-primary summand killed by r^e, induct on e using
0 → F[r] → F → F/F[r] → 0. The quotient is killed by r^(e-1), and both outer terms
are constructible. The term F[r] has its canonical ULift (ZMod r)-module structure;
its underlying abelian sheaf is unchanged and it is constructible over this finite ring.
Use the hypothesis for e = 1, then short-exact devissage for the induction and the
finite direct sum. Cohomology and pullback commute with forgetting these scalars.
For C3 restrict the decomposition to characteristic-primary pieces; for C4 and C6
restrict to primes invertible in k. These restrictions are justified stalkwise by
primary torsion and invertibility of the stalk orders. C1,C2,C5,C7,C8 use all pieces.
The zero ring or zero sheaf gives only zero pieces and all assertions hold. -/
theorem IsCurve.assertions_of_constructible_prime_devissage
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsReduced C]
    (H : ∀ (r : ℕ) [Fact r.Prime]
      (G : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
      [Scheme.IsConstructibleSheaf G], IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f G)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] : IsCurve.Assertions Λ f F := by
  have hfil := Scheme.constructible_hasPrimeFieldFiltration Λ C F
  induction hfil with
  | prime r F G e =>
    exact IsCurve.assertions_of_underlying_abelian_iso f e (H r G)
  | extension S hS h₁ h₃ ih₁ ih₃ =>
    exact IsCurve.Assertions.of_constructible_shortExact Λ f hS ih₁ ih₃

end AlgebraicGeometry
