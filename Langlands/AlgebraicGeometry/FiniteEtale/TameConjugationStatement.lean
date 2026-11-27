import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Langlands.AlgebraicGeometry.FiniteEtale.Pullback
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Tame conjugation of finite `ℓ`-group images along a regular local divisor

Let `R` be a Henselian regular local ring, `t` a regular parameter with `R/(t)` regular,
`ℓ` a prime invertible in `R`, and `U = Spec R[1/t]`. A local homomorphism from `R` to a
strictly Henselian discrete valuation ring `W` sending `t` to a uniformizer induces a morphism
`j : Spec L ⟶ U` from the spectrum of the fraction field `L` of `W`. This module defines the
cyclotomic condition on an exponent `q`, defines `j`, and states that in every finite
`ℓ`-group quotient of `π₁(U)` the image of each element coming from `π₁(Spec L)` is conjugate
to its `q`-th power. The module states this and does not prove it.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.AlgebraicGeometry.FiniteEtale

/-- The cyclotomic condition on an exponent `q` for a field `k` and a prime `ℓ`: `1 < q`, and
for every `n` some `k`-automorphism of the separable closure `SeparableClosure k` sends every
`ℓ^n`-th root of unity `ζ` to `ζ ^ q`. The automorphism may depend on `n`; the exponent `q`
does not. -/
def CyclotomicPowerCondition (k : Type u) [Field k] (ℓ q : ℕ) : Prop :=
  1 < q ∧ ∀ n : ℕ, ∃ φ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
    ∀ ζ : SeparableClosure k, ζ ^ (ℓ ^ n) = 1 → φ ζ = ζ ^ q

/-- The ring homomorphism `R[1/t] →+* L` induced by `R → W → L`, when the image of `t` in
`W` is nonzero, so that its image in the fraction field `L` is a unit. -/
def traitGenericRingHom {R W : Type u} (L : Type u) [CommRing R] [CommRing W] [IsDomain W]
    [Field L] [Algebra R W] [Algebra W L] [IsFractionRing W L] (t : R)
    (ht : algebraMap R W t ≠ 0) : Localization.Away t →+* L :=
  IsLocalization.Away.lift (S := Localization.Away t) t
    (g := (algebraMap W L).comp (algebraMap R W))
    (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective W L)).mpr ht))

/-- The morphism `j : Spec L ⟶ Spec R[1/t]`, the spectrum of `traitGenericRingHom`. -/
def traitGenericMorphism {R W : Type u} (L : Type u) [CommRing R] [CommRing W] [IsDomain W]
    [Field L] [Algebra R W] [Algebra W L] [IsFractionRing W L] (t : R)
    (ht : algebraMap R W t ≠ 0) :
    Spec (.of L) ⟶ Spec (.of (Localization.Away t)) :=
  Spec.map (CommRingCat.ofHom (traitGenericRingHom L t ht))

/-- **Tame conjugation along a regular local divisor.** Let `R` be a Henselian regular local
domain with residue field `k`, `t ∈ 𝔪 \ 𝔪²` a regular parameter with `R/(t)` regular, and `ℓ`
a prime invertible in `R`. Let `R → W` be a local homomorphism to a strictly Henselian discrete
valuation ring sending `t` to a uniformizer, `L` the fraction field of `W`, and
`j : Spec L ⟶ U = Spec R[1/t]` the induced morphism. Let `s` be a geometric point of `Spec L`
and suppose that `q` satisfies `CyclotomicPowerCondition k ℓ q`. Then for every continuous
homomorphism `ρ` from `π₁(U, s ≫ j)` to a finite discrete `ℓ`-group and every
`g ∈ π₁(Spec L, s)` there is `σ ∈ π₁(U, s ≫ j)` with
`ρ (σ * j₍*₎ g * σ⁻¹) = ρ (j₍*₎ g) ^ q`. -/
def RegularDivisorTameConjugationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R] [HenselianLocalRing R]
    (t : R), t ∈ maximalIdeal R → t ∉ maximalIdeal R ^ 2 →
    IsRegularLocalRing (R ⧸ Ideal.span {t}) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : R) →
    ∀ (W L : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
      [HenselianLocalRing W] [IsSepClosed (ResidueField W)]
      [Field L] [Algebra W L] [IsFractionRing W L]
      [Algebra R W] [IsLocalHom (algebraMap R W)]
      (ht : Irreducible (algebraMap R W t))
      (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of L))
      (q : ℕ), CyclotomicPowerCondition (ResidueField R) ℓ q →
      ∀ (H : Type v) [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H],
        IsPGroup ℓ H →
        let j := traitGenericMorphism L t ht.ne_zero
        ∀ ρ : FundamentalGroup (s ≫ j) (geometricFiberFinite (s ≫ j)) →* H, Continuous ρ →
          ∀ g : FundamentalGroup s (geometricFiberFinite s),
            let jg := fundamentalGroupMap j s (s ≫ j) rfl
              (geometricFiberFinite s) (geometricFiberFinite (s ≫ j)) g
            ∃ σ : FundamentalGroup (s ≫ j) (geometricFiberFinite (s ≫ j)),
              ρ (σ * jg * σ⁻¹) = ρ jg ^ q

end Langlands.AlgebraicGeometry.FiniteEtale
