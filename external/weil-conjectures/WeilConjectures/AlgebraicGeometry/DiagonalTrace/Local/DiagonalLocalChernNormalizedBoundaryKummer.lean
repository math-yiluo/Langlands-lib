/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalFiniteConeChernClass
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Boundary.FiniteBoundaryKummerArrowTransport

/-! # Finite integral coordinates for a strict Chern arrow -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses
attribute [local irreducible] Functor.mapDerivedCategory HasDerivedCategory.standard
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Finite Chern normalization identifies the integral finite cone coordinates
with the positive Kummer class. No completed arrow or limit normalization is used.
Source: geometric tower classes proof (2), finite Kummer normalization; diagonal
tower trace proof (1), coefficient-one and pure-tensor root normalization.
(blueprint: lem-diagonal-local-finite-cone-kummer).

Proof: apply hc to P,n and eliminate the heterogeneous endpoint witnesses. Restrict,
evaluate, and forget by restrictionUnderlying and mapSingleArrow_natIso. The source
map is the integer quotient: coefficient_one fixes its value on 1; additivity and
the constant-sheaf adjunction fix its value on every integer. At the target, expand
finiteBoundary_rootMap. The ordinary scalar unit sends x to its scalar-extension
section. The line_tensor field sends that section to the original root. Cancel
lineEvaluation and the restriction comparison to see that finiteRootMap followed
by the target coordinate is the identity on roots. Postcompose the finite boundary
equation with the Cartier root map and substitute the two endpoint identities.
Finally Ext.comp_hom, mapExactFunctor_hom, and extClass_hom identify the evaluated
positive Kummer composite with evaluatedIntegralKummerClass. Positivity of n+1
covers n=0; all maps preserve zero and the argument covers empty schemes and zero
coefficient rings. -/
theorem localChern_normalized_boundary_kummer
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (hc : FiniteChernNormalization l (ULift.{u} (Padic l)) c) (P : T.Pic) :
    finiteConeChernClass l T c r k A n hA hN
        (firstChern l (ULift.{u} (Padic l)) c P) =
      evaluatedIntegralKummerClass l T A n hA c.kummer hN P := by
  apply Ext.ext
  have hs : source_endpoint_statement l T c r k n := finiteBoundary_source_endpoint l T c r k n
  have ht : target_endpoint_statement l T c r k A n hA hN :=
    finiteBoundary_target_endpoint l T c r k A n hA hN
  exact finiteBoundary_transport_assembly l T c r k A n hA hN hc P hs ht

end AlgebraicGeometry.ProEtale.DiagonalTrace
