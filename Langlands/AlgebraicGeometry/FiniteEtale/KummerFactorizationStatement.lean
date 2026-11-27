import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Langlands.AlgebraicGeometry.FiniteEtale.Pullback
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Kummer factorization of finite `ℓ`-group quotients over a strictly Henselian regular
local ring

For a regular local ring `R` and an element `t` of `R`, the Kummer algebra of level `m` is
`R[1/t][X]/(X^m - t)`. This module defines it with Mathlib's `Localization.Away` and
`AdjoinRoot`, defines the morphism of spectra to `Spec R[1/t]`, and states that over a
strictly Henselian regular local ring every continuous homomorphism from the finite étale
fundamental group of `Spec R[1/t]` to a finite `ℓ`-group, `ℓ` invertible in `R`, vanishes on
the fundamental group of the Kummer cover of some level `ℓ^n`. The module states this and does
not prove it.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry IsLocalRing Polynomial

namespace Langlands.AlgebraicGeometry.FiniteEtale

/-- The Kummer algebra `R[1/t][X]/(X^m - t)` of level `m` over the localization
`R[1/t] = Localization.Away t`. -/
abbrev KummerAlgebra {R : Type u} [CommRing R] (t : R) (m : ℕ) : Type u :=
  AdjoinRoot (X ^ m - C (algebraMap R (Localization.Away t) t))

/-- The Kummer morphism `Spec (R[1/t][X]/(X^m - t)) ⟶ Spec R[1/t]`, the spectrum of the
structure map of `KummerAlgebra t m`. -/
def kummerMorphism {R : Type u} [CommRing R] (t : R) (m : ℕ) :
    Spec (.of (KummerAlgebra t m)) ⟶ Spec (.of (Localization.Away t)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away t) (KummerAlgebra t m)))

/-- **Kummer factorization over a strictly Henselian regular local ring.** Let `R` be a
strictly Henselian regular local domain, `t ∈ 𝔪 \ 𝔪²` a regular parameter, and `ℓ` a prime
invertible in `R`. Let `x` be a geometric point of `U = Spec R[1/t]`. Every continuous
homomorphism `ρ` from the finite étale fundamental group `π₁(U, x)` to a finite discrete
`ℓ`-group is trivial on the image of `π₁(U_n, y) → π₁(U, x)` for some `n` and some geometric
point `y` of the Kummer cover `U_n = Spec (R[1/t][X]/(X^(ℓ^n) - t))` lying over `x`. -/
def StrictlyHenselianKummerFactorizationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)] (t : R), t ∈ maximalIdeal R → t ∉ maximalIdeal R ^ 2 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : R) →
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ Spec (.of (Localization.Away t)))
      (H : Type v) [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H],
      IsPGroup ℓ H →
      ∀ ρ : FundamentalGroup x (geometricFiberFinite x) →* H, Continuous ρ →
        ∃ (n : ℕ) (y : Spec (.of Ω) ⟶ Spec (.of (KummerAlgebra t (ℓ ^ n))))
          (hy : y ≫ kummerMorphism t (ℓ ^ n) = x),
          ρ.comp (fundamentalGroupMap (kummerMorphism t (ℓ ^ n)) y x hy
            (geometricFiberFinite y) (geometricFiberFinite x)) = 1

end Langlands.AlgebraicGeometry.FiniteEtale
