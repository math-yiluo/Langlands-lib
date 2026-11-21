import Langlands.Global.AdelicWavePacketCompletenessReduction

/-! # Reduction of the spectral witness to Bernstein's eigenfunctions and a growth lemma

`SpectralWitnessStatement` (Delorme 2023, Lemma 7.10 with the preliminary remark before it)
follows from two propositions:

* `CyclicSpectralEigenfunctionStatement` (Bernstein 1988, §3.1–3.3 and the key lemma p.686, with
  a weight summable by Delorme's (2.10) and Remark 3.4; Delorme 2023, proof of Lemma 7.10, after
  Carmona–Delorme 1998, Lemma 11, Delorme's reference [10]): every nonzero `f ∈ L²([G])` has, in
  the weighted `L²` closure of the span of its right translates, a nonzero smooth, `K_∞`-finite,
  `𝔷`-finite, `G(F)`-invariant function with a unitary `A_G`-character and in
  `L²([G], σ_{[G]}^{-2m})`;
* `WeightedSquareIntegrableModerateGrowthStatement` (Harish-Chandra 1966, §8, Theorem 1, and
  the counting lemma Mœglin–Waldspurger I.2.4 (a)(i), as in the proof of MW I.2.5 (b); compare
  Delorme 2023, Proposition 3.5): such a function has moderate growth.

The theorem `spectralWitness_of_reduction` derives `SpectralWitnessStatement` from the two. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Generalized eigenfunctions in the cyclic subspace of a nonzero `L²` function (Bernstein 1988,
the Theorem of §3.2 and Cond(w) for the weight `w = σ_{[G]}^{2m}`, summable for `2m ≥ d_G` by
the Criterion of §3.3 with Delorme's (2.10) and Remark 3.4; Delorme 2023, proof of Lemma 7.10).
Let `f ∈ L²([G])` be not zero almost everywhere. There are `m` and a function `Φ` on `G(𝔸)`,
not identically zero, which is left `G(F)`-invariant, smooth, `K_∞`-finite and `𝔷`-finite,
transforms under a unitary character `a ↦ a^{iν}` of `A_G`, satisfies
`Φ / σ_{[G]}^m ∈ L²([G])`, and lies in the closure of the span of the right translates of `f` in
`L²([G], σ_{[G]}^{-2m})`, in the dual form: `Φ` is orthogonal to every `Θ` with
`Θ σ_{[G]}^m ∈ L²([G])` that is orthogonal to all right translates of `f`. Moderate growth is
not asserted. -/
def CyclicSpectralEigenfunctionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      (∃ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left) (p₀ : P₀ ⟶ G)
        (_ : IsClosedImmersion p₀.hom.hom.left),
        IsMinimalParabolicSubgroup p₀ ∧ IsIwasawaCompact p₀ K) →
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    ∀ f : RationalQuotient F G → ℂ, MemLp f 2 μG → ¬ f =ᵐ[μG] 0 →
      ∃ (m : ℕ) (Φ : AdelicGroupPoints F G → ℂ),
        IsLeftInvariantUnder F G (rationalSubgroup F G) Φ ∧
        IsAdelicSmoothFunction F G Φ ∧
        IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom) Φ ∧
        IsCenterFiniteFunction F G hsmooth hcalc Φ ∧
        (∃ ν : RealCharacterParameter F G,
          ∀ a ∈ RestrictionSplitCentre.canonicalSubgroup F G, ∀ g : AdelicGroupPoints F G,
            Φ (a * g) = parameterPower F G (imaginaryParameter F G ν) a * Φ g) ∧
        MemLp (fun y : RationalQuotient F G =>
          Φ y.out / (rationalLogHeight F G rho y : ℂ) ^ m) 2 μG ∧
        (∃ g, Φ g ≠ 0) ∧
        ∀ Θ : AdelicGroupPoints F G → ℂ,
          MemLp (fun y : RationalQuotient F G =>
            Θ y.out * (rationalLogHeight F G rho y : ℂ) ^ m) 2 μG →
          (∀ g : AdelicGroupPoints F G,
            ∫ y, f (LeftCosetSpace.rightTranslate (rationalSubgroup F G) g y) *
              (starRingEnd ℂ) (Θ y.out) ∂μG = 0) →
          ∫ y, Φ y.out * (starRingEnd ℂ) (Θ y.out) ∂μG = 0

/-- Weighted square-integrable smooth functions have moderate growth (Harish-Chandra 1966, §8,
Theorem 1: a smooth `K_∞`-finite `𝔷`-finite function satisfies `Φ = Φ * α` for some
`α ∈ C_c^∞(G(F_∞))`; then `|Φ(x)|` is bounded by an integral of `|Φ|` over `x · supp α`, which
the counting lemma Mœglin–Waldspurger I.2.4 (a)(i) and the Cauchy–Schwarz inequality bound by a
power of `max(1, ‖x‖)`, as in the proof of MW I.2.5 (b); compare Delorme 2023, Proposition 3.5).
If `Φ`
on `G(𝔸)` is left `G(F)`-invariant, smooth, `K_∞`-finite and `𝔷`-finite and
`Φ / σ_{[G]}^m ∈ L²([G])` for some `m`, then `Φ` has moderate growth. -/
def WeightedSquareIntegrableModerateGrowthStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      (∃ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left) (p₀ : P₀ ⟶ G)
        (_ : IsClosedImmersion p₀.hom.hom.left),
        IsMinimalParabolicSubgroup p₀ ∧ IsIwasawaCompact p₀ K) →
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    ∀ (m : ℕ) (Φ : AdelicGroupPoints F G → ℂ),
      IsLeftInvariantUnder F G (rationalSubgroup F G) Φ →
      IsAdelicSmoothFunction F G Φ →
      IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom) Φ →
      IsCenterFiniteFunction F G hsmooth hcalc Φ →
      MemLp (fun y : RationalQuotient F G =>
        Φ y.out / (rationalLogHeight F G rho y : ℂ) ^ m) 2 μG →
      HasModerateGrowthFunction F G rho Φ

/-- The generalized eigenfunctions and the growth lemma imply the spectral witness (Delorme 2023,
Lemma 7.10 with the preliminary remark before it). -/
theorem spectralWitness_of_reduction (hE : CyclicSpectralEigenfunctionStatement)
    (hM : WeightedSquareIntegrableModerateGrowthStatement) : SpectralWitnessStatement := by
  intro F _ _ G _ _ _ hred K N d rho hsmooth hcalc hKmax hrho hP₀ μG W hW htrans f hf horth hne
  obtain ⟨m, Φ, hleft, hsm, hKfin, hZfin, hν, hL2, hne', hdual⟩ :=
    hE F G hred K rho hsmooth hcalc hKmax hrho hP₀ f hf hne
  refine ⟨Φ, ⟨⟨hleft, hsm, hKfin, hZfin,
    hM F G hred K rho hsmooth hcalc hKmax hrho hP₀ m Φ hleft hsm hKfin hZfin hL2⟩,
    hν, m, hL2⟩, hne', fun Θ hΘ => hdual Θ (hW Θ hΘ m) fun g => htrans f hf horth g Θ hΘ⟩

end Langlands.Global
