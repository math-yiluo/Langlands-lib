import Langlands.Global.AdelicSquareIntegrableInducedForms
import Langlands.Global.AdelicCharacterLog
import Langlands.Global.AdelicSubgroupHaarMeasure
import Langlands.Global.LeftCosetFundamentalDomain
import Langlands.Global.AdelicIntertwiningOperator

/-! # The inner product on `A^2_P` and the measures on `𝔞_P` and `i𝔞_P^*`

Lapid 2011, §2 (p.311) and §3 (p.314): the inner product `(·,·)_P`, Haar measures compatible
with the Iwasawa decomposition, dual coordinates and measures on `𝔞_P` and `i𝔞_P^*`, and the
Weyl set `Ω(P, P')` of Arthur and Lapid. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct CompactlySupported

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

section Coordinates

variable (F : Type u) [Field F] [NumberField F] (P : GroupScheme (Spec (CommRingCat.of F)))

/-- The coordinates `y_j = ⟨e(b_j), H⟩` of `H ∈ Hom(X^*(P), ℝ)` dual to a real basis
`e : ℝⁿ ≃ X^*(P) ⊗ ℝ`, so that `⟨i e(x), H⟩ = i ∑_j x_j y_j`. -/
def parameterCoordinates {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (H : RealCharacterDual F P) : Fin n → ℝ :=
  fun j => realParameterPairing F P (e (Pi.single j 1)) H

/-- The measure `(2π)^{-n} dx` on `ℝⁿ`. In the coordinates `x ↦ i e(x)` of `i𝔞_P^*` and `y` of
`𝔞_P`, it is the measure dual to `dy` for the pairing `e^{i x·y}`. -/
def spectralMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ ^ n • volume

end Coordinates

section Measures

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]

/-- The Haar measure `μ_M` on `M(𝔸)` is compatible with Mathlib's Haar measure on `G(𝔸)` for
the Iwasawa decomposition `G(𝔸) = U(𝔸) M(𝔸) K`:
`∫_G f = ∫_K ∫_M ∫_U δ_P(m)⁻¹ f(u m k) du dμ_M(m) dk` for every compactly supported continuous
`f`, where `du` is the Haar measure with `vol(U(F) \ U(𝔸)) = 1` and `dk` the Haar probability
measure on `K`. -/
def IsIwasawaCompatibleMeasure (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) (p : P ⟶ G) [IsAffine U.X.left]
    (iU : U ⟶ P) [IsClosedImmersion (iU ≫ p).hom.hom.left] (l : M ⟶ P)
    (μM : Measure (AdelicGroupPoints F M)) : Prop :=
  haveI : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p)) :
      Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU ≫ p)
  ∀ f : C_c(AdelicGroupPoints F G, ℂ),
    ∫ g, f g ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
      ∫ k : K, ∫ m, ∫ u,
        parameterPower F P (-modulusParameter F P) (map F M P l m) *
          f ((u : AdelicGroupPoints F G) * map F P G p (map F M P l m) *
            (k : AdelicGroupPoints F G))
        ∂(AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range (iU ≫ p)))
        ∂μM ∂(compactHaarProbability F G K hKc)

/-- The inner product `(φ, ψ)_P = ∫_{A_M U(𝔸) M(F) \ G(𝔸)} φ ψ̄` of Lapid §2, in Iwasawa
coordinates and with the `A_M`-integration replaced by a weight:
`∫_K ∫_{M(F) \ M(𝔸)} β(y(m)) δ_P(m)⁻¹ φ(m k) conj ψ(m k) dm dk`. Here `dm` is the quotient of
`μ_M` by counting measure on `M(F)`, `y(m)` are the coordinates of `H_P(m)` dual to `e`, and
`β` is a weight on `ℝⁿ`. For `φ, ψ` in `A^n_P` and `∫ β = 1` this is Lapid's inner product for
the measure `dy` on `𝔞_P`. -/
def inducedInnerProduct (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) (p : P ⟶ G) (l : M ⟶ P)
    (μM : Measure (AdelicGroupPoints F M)) {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ)
    (φ ψ : AdelicGroupPoints F G → ℂ) : ℂ :=
  ∫ k : K, ∫ x : RationalQuotient F M,
      (β (parameterCoordinates F P e (characterLog F P (map F M P l x.out))) : ℂ) *
        parameterPower F P (-modulusParameter F P) (map F M P l x.out) *
        φ (map F P G p (map F M P l x.out) * (k : AdelicGroupPoints F G)) *
        (starRingEnd ℂ) (ψ (map F P G p (map F M P l x.out) * (k : AdelicGroupPoints F G)))
    ∂(LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
        (isDiscrete_rationalSubgroup F M) μM)
    ∂(compactHaarProbability F G K hKc)

end Measures

section Weyl

variable {F : Type u} [Field F] [NumberField F]
  {G P M Q M' : GroupScheme (Spec (CommRingCat.of F))}

/-- The real form `μ ↦ wμ`, `X^*(P) ⊗ ℝ → X^*(Q) ⊗ ℝ`, of `weylParameter l c π'`: `χ ↦ χ ∘ l ∘ c ∘ π'`
on characters, tensored with `ℝ`. -/
def realWeylParameter (l : M ⟶ P) (c : M' ⟶ M) (π' : Q ⟶ M') :
    RealCharacterParameter F P →ₗ[ℝ] RealCharacterParameter F Q :=
  AlgebraTensorModule.map LinearMap.id (characterRestrict (π' ≫ c ≫ l)).toIntLinearMap

/-- The Weyl set `Ω(P, Q)` (Lapid §2, after Arthur; `W(𝔞_M, 𝔞_{M'})` of Getz–Hahn §10.2), as the
set of linear maps `λ ↦ wλ` from `X^*(P) ⊗ ℂ` to `X^*(Q) ⊗ ℂ` given by the pairs `(w, c)` with
`w ∈ G(F)`, `w M w⁻¹ = M'`. -/
def weylParameterSet (p : P ⟶ G) (l : M ⟶ P) (q : Q ⟶ G) (l' : M' ⟶ Q) (π' : Q ⟶ M') :
    Set (ComplexCharacterParameter F P →ₗ[ℂ] ComplexCharacterParameter F Q) :=
  {s | ∃ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsWeylConjugation p l q l' w c ∧ weylParameter l c π' = s}

end Weyl

end Langlands.Global.AdelicGroupPoints
