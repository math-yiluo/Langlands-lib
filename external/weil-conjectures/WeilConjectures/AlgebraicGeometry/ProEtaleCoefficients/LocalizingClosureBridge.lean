/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing

/-!
# The two localizing closures of the pro-étale coefficients agree

`Loc(Dctf(X, Λ))`, the localizing closure of the bounded constructible complexes of finite Tor
amplitude, is `AlgebraicGeometry.ProEtale.localizingClosureProEtale` (defined for every condensed
ring `Λ`). The six operations with `ℓ`-adic coefficients are built on
`AlgebraicGeometry.ProEtale.CondensedRing.localizingBoundedConstructible`, the localizing closure of
the bounded constructible complexes `Dᵇc` in the sense of locally finitely presented
constructibility. For the `ℓ`-adic coefficient rings on a compact, locally noetherian,
quasi-separated scheme the two agree:

* `boundedConstructible = constantModelBoundedConstructible`
  (`AlgebraicGeometry.ProEtale.adicConstructibilityPredicateComparison`);
* `Loc(Dctf) = Loc(Dᵇc)` for the constant-model categories, the Loc assertion of
  `AlgebraicGeometry.ProEtale.localizingClosure_ctf_equals_bc`;
* the two generic closures are the same
  (`CategoryTheory.localizingClosure_eq_objectProperty`).

This is the bridge lemma
`AlgebraicGeometry.ProEtale.localizingClosureProEtale_eq_localizingBoundedConstructible`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- **The localizing closures agree**: for an `ℓ`-adic coefficient ring `Λ` and a compact, locally
noetherian, quasi-separated scheme `X`, the localizing closure of `Dctf(X, Λ)`
(`AlgebraicGeometry.ProEtale.localizingClosureProEtale`) is the localizing closure of `Dᵇc(X)⟦Λ⟧`
used by the six operations
(`AlgebraicGeometry.ProEtale.CondensedRing.localizingBoundedConstructible`). The hypothesis `hΛ`
is the form of the `ℓ`-adic ring used by the constructibility comparison, `hΛ'` the form used by
`localizingClosure_ctf_equals_bc`. -/
theorem localizingClosureProEtale_eq_localizingBoundedConstructible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X] [QuasiSeparatedSpace X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : CondensedRing.IsEllAdicCoefficient ℓ Λ inferInstance)
    (hΛ' :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    localizingClosureProEtale Λ X = CondensedRing.localizingBoundedConstructible Λ X := by
  have hLoc := (localizingClosure_ctf_equals_bc ℓ X Λ hΛ').1.2.2.2.1
  have hbc := (adicConstructibilityPredicateComparison ℓ X Λ hΛ).2
  unfold localizingClosureProEtale CondensedRing.localizingBoundedConstructible
  rw [hbc, ← CategoryTheory.localizingClosure_eq_objectProperty, ← hLoc]

end AlgebraicGeometry.ProEtale
