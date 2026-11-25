/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Boundary.FiniteBoundarySourceEndpointTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Boundary.FiniteBoundaryTargetEndpointTransport

/-! The finite boundary square assembled after its two endpoint transports. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

abbrev source_endpoint_statement
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r) (n : ℕ) : Prop :=
  let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
  let e := finiteBoundaryRestrictionUnderlying l T r n
  S.map (finiteQuotient l (ULift (Padic l)) T n) ≫
      S.map (e.inv.app (coefficient T (Arings l (ULift (Padic l)) T))) =
    S.map (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
      k.coefficientForget.inv.app (op n))

abbrev target_endpoint_statement
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) : Prop :=
  let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
  let e := finiteBoundaryRestrictionUnderlying l T r n
  S.map (finiteRootMap l (ULift (Padic l)) T n) ≫
      S.map ((finiteForget l (ULift (Padic l)) T n).mapIso
        (lineEvaluation l (ULift (Padic l)) c n)).inv ≫
      S.map (e.inv.app (lineModule l (ULift (Padic l)) c)) ≫
      S.map (k.lineForget.hom.app (op n)) ≫
      S.map (cartierProRootMap A (l ^ (n + 1)) hA T
        (pow_pos (Fact.out : l.Prime).pos _) hN) =
    S.map (cartierProRootMap A (l ^ (n + 1)) hA T
      (pow_pos (Fact.out : l.Prime).pos _) hN)

/-- Assemble the finite boundary square once the source coefficient-one and
root endpoint equations have been supplied.  The assembly is the exact
single-arrow naturality square followed by the two endpoint substitutions; its
proof is independent of the coefficient and root calculations.
(blueprint: lem-diagonal-local-finite-boundary-assembly) -/
theorem finiteBoundary_transport_assembly
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (hc : FiniteChernNormalization l (ULift.{u} (Padic l)) c) (P : T.Pic)
    (hs : source_endpoint_statement l T c r k n)
    (ht : target_endpoint_statement l T c r k A n hA hN) :
    (finiteConeChernClass l T c r k A n hA hN
        (firstChern l (ULift.{u} (Padic l)) c P)).hom =
      (evaluatedIntegralKummerClass l T A n hA c.kummer hN P).hom := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
