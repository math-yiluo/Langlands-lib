/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions
import WeilConjectures.AlgebraicGeometry.Curve.Reductions

/-! # The eight curve assertions for finite coefficients

The eight assertions `C(X, F)` hold for every sheaf of modules `F` over a finite coefficient
ring on every curve `X` over an algebraically closed field. This is the reduction
`AlgebraicGeometry.IsCurve.Assertions.of_forall_isReduced` applied to the prime-field case
`AlgebraicGeometry.IsCurve.primeCoefficientCurveAssertions`, which holds on every reduced curve.
In particular the assertions for `F` and for `j_! j^* F` are equivalent for every open `j`,
without any condition on the torsion of `F`.

Source: Stacks Project, Theorem 03SC and Lemma 0GJA (blueprint: `app:curve-package`,
`lemma-removing-finitely-many-points`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- **The curve package.** Let `k` be algebraically closed, `X` a curve over `k` and `Λ` a
finite ring. Then the eight assertions `C(X, F)` hold for every sheaf `F` of `Λ`-modules on
`X_ét`; such a sheaf is torsion because `Λ` is finite.

Source: Stacks Project, Theorem 03SC (blueprint: `app:curve-package`).

Proof: by `AlgebraicGeometry.IsCurve.Assertions.of_forall_isReduced` it suffices to prove
`C(Y, G)` for every reduced curve `Y`, every prime `ℓ` and every constructible sheaf `G` of
`𝐅_ℓ`-modules on `Y`, which is `AlgebraicGeometry.IsCurve.primeCoefficientCurveAssertions`. -/
theorem Assertions.of_finite_coefficients (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsCurve.Assertions Λ f F :=
  IsCurve.Assertions.of_forall_isReduced Λ
    (fun g _ _ _ _ G _ ↦ primeCoefficientCurveAssertions g G) f F

/-- **Extension by zero from an open does not change the eight assertions**, for sheaves of
modules over a finite ring. Let `k` be algebraically closed, `X` a curve over `k`, `Λ` a
finite ring, `F` a sheaf of `Λ`-modules on `X_ét` and `j : U ⟶ X` an open immersion. Then
`C(X, F)` holds if and only if `C(X, j_! j^* F)` holds. No condition on the torsion of `F` is
needed, and the statement holds for every open `U`, in particular for every dense open.

Source: Stacks Project, Lemma 0GJA (blueprint: `lemma-removing-finitely-many-points`).

Proof: both sides hold by `AlgebraicGeometry.IsCurve.Assertions.of_finite_coefficients`. -/
theorem assertions_iff_dense_open_of_finite_coefficients (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Opens) :
    IsCurve.Assertions Λ f F ↔ IsCurve.Assertions Λ f
      ((U.ι)_!open[ModuleCat.{u + 1} Λ].obj ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)) :=
  iff_of_true (Assertions.of_finite_coefficients Λ f F)
    (Assertions.of_finite_coefficients Λ f _)

end AlgebraicGeometry.IsCurve
