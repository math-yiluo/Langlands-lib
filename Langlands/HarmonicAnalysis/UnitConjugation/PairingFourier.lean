import Langlands.HarmonicAnalysis.Bicharacter.Fourier
import Langlands.HarmonicAnalysis.Distribution.Basic

/-!
# The Fourier transform of distributions for an invariant pairing

Let `F` be a nonarchimedean local field, `ψ` a nontrivial continuous unitary additive character
of `F` (`UnitaryAdditiveCharacter F`), `V` a finite-dimensional `F`-vector space with its module
topology and `B` a symmetric nondegenerate bilinear form on `V`. Then `(Y, X) ↦ ψ(B(Y, X))` is a
self-dual bicharacter (`isSelfDualBicharacter_pairingCharacter`, an application of the Library's
`isSelfDualBicharacter_of_symm`), and for an additive Haar measure `μ` on `V` the Library's
Fourier operator `bicharacterFourierSB` of this bicharacter is

`f̂(Y) = ∫ ψ(B(Y, X)) f(X) dμ(X)`  (`pairingFourierSB`, `pairingFourierSB_apply`),

an endomorphism of the Schwartz–Bruhat space. The Fourier transform of a distribution `T` is
`T̂(f) = T(f̂)` (`distributionFourier`).

For an `F`-algebra `A`, a pairing is *invariant* when it is symmetric, nondegenerate and
invariant under conjugation by the units: `B(u X u⁻¹, u Y u⁻¹) = B(X, Y)` (`IsInvariantPairing`).

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), Introduction, printed p. 2: "Fix a symmetric, nondegenerate,
`G`-invariant bilinear form `B` on `g` … Also fix a character `χ ≠ 1` of the additive group of
`Ω`. Let `dX` denote a Haar measure … and define `f̂(Y) = ∫ χ(B(Y, X)) f(X) dX` … `T̂(f) = T(f̂)`."
-/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.UnitConjugation

universe u v

section Character

variable {F : Type u} [Field F] [TopologicalSpace F] {V : Type v} [AddCommGroup V] [Module F V]

/-- The bicharacter `(Y, X) ↦ ψ(B(Y, X))` of `V`. -/
def pairingCharacter (ψ : UnitaryAdditiveCharacter F) (B : LinearMap.BilinForm F V) :
    V → V → ℂ :=
  fun Y X => ψ.complex (B Y X)

@[simp]
theorem pairingCharacter_apply (ψ : UnitaryAdditiveCharacter F) (B : LinearMap.BilinForm F V)
    (Y X : V) : pairingCharacter ψ B Y X = (ψ (B Y X) : ℂ) := rfl

end Character

section Pairing

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V]
  [IsModuleTopology F V]

/-- **Self-duality** of `(Y, X) ↦ ψ(B(Y, X))` for a symmetric nondegenerate form `B`: the
certificate used by the Fourier operator `pairingFourierSB`. -/
theorem isSelfDualBicharacter_pairingCharacter (ψ : UnitaryAdditiveCharacter F)
    {B : LinearMap.BilinForm F V} (hs : B.IsSymm) (hnd : B.Nondegenerate) :
    IsSelfDualBicharacter (pairingCharacter ψ B) :=
  isSelfDualBicharacter_of_symm ψ.continuous_complex ψ.norm_complex ψ.complex_ne_one B hs.eq
    hnd.2

variable [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform `f ↦ f̂`, `f̂(Y) = ∫ ψ(B(Y, X)) f(X) dμ(X)`, on the Schwartz–Bruhat
space of `V`: the Library's `bicharacterFourierSB` of the self-dual bicharacter
`pairingCharacter ψ B`. -/
def pairingFourierSB (ψ : UnitaryAdditiveCharacter F) {B : LinearMap.BilinForm F V}
    (hs : B.IsSymm) (hnd : B.Nondegenerate) (μ : AdditiveHaarMeasure V) :
    SchwartzBruhat V →ₗ[ℂ] SchwartzBruhat V :=
  haveI := IsModuleTopology.isTopologicalAddGroup F V
  bicharacterFourierSB μ.measure (isSelfDualBicharacter_pairingCharacter ψ hs hnd)

theorem pairingFourierSB_apply (ψ : UnitaryAdditiveCharacter F) {B : LinearMap.BilinForm F V}
    (hs : B.IsSymm) (hnd : B.Nondegenerate) (μ : AdditiveHaarMeasure V) (f : SchwartzBruhat V)
    (Y : V) :
    pairingFourierSB ψ hs hnd μ f Y = ∫ X, (ψ (B Y X) : ℂ) * f X ∂μ.measure := rfl

/-- The Fourier transform of distributions on `V`: `T̂(f) = T(f̂)`, the transpose of
`pairingFourierSB`. -/
def distributionFourier (ψ : UnitaryAdditiveCharacter F) {B : LinearMap.BilinForm F V}
    (hs : B.IsSymm) (hnd : B.Nondegenerate) (μ : AdditiveHaarMeasure V) :
    Distribution V →ₗ[ℂ] Distribution V :=
  (pairingFourierSB ψ hs hnd μ).dualMap

@[simp]
theorem distributionFourier_apply (ψ : UnitaryAdditiveCharacter F)
    {B : LinearMap.BilinForm F V} (hs : B.IsSymm) (hnd : B.Nondegenerate)
    (μ : AdditiveHaarMeasure V) (T : Distribution V) (f : SchwartzBruhat V) :
    distributionFourier ψ hs hnd μ T f = T (pairingFourierSB ψ hs hnd μ f) := rfl

end Pairing

section Invariant

variable {F : Type u} [Field F] {A : Type v} [Ring A] [Algebra F A]

/-- A bilinear form on the algebra `A` is an *invariant pairing* when it is symmetric,
nondegenerate and invariant under conjugation by the units of `A`:
`B(u X u⁻¹, u Y u⁻¹) = B(X, Y)`. -/
structure IsInvariantPairing (B : LinearMap.BilinForm F A) : Prop where
  isSymm : B.IsSymm
  nondegenerate : B.Nondegenerate
  conj_invariant : ∀ (u : Aˣ) (X Y : A),
    B ((u : A) * X * ((u⁻¹ : Aˣ) : A)) ((u : A) * Y * ((u⁻¹ : Aˣ) : A)) = B X Y

end Invariant

end Langlands.HarmonicAnalysis.UnitConjugation
