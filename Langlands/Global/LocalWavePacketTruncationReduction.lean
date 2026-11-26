import Langlands.Global.AdelicLocalWavePacketStatement
import Langlands.Global.LapidArthurTruncationPairing
import Langlands.Global.ArthurTruncationFinitenessProof
import Langlands.Global.ArthurCuspidalRepresentativeBounds

/-! # Lapid's Proposition 2 from the limit of truncated inner products, for one compact subgroup

Lapid 2011, §8, p.328, opening sentence: by Lemma 9, to prove Proposition 2 it suffices to show
that `(Λ^T Θ_{P,φ}, Λ^T Θ_{P',φ'})` converges to the right side of (4) as `T → ∞` in a
cone. Lapid uses one compact subgroup `K`, in good position with respect to `M₀` (§2), for the
Eisenstein series, the intertwining operators and the truncation.

* `LocalWavePacketInnerProductTruncationCompactStatement` is `LocalWavePacketInnerProductStatement`
  with three additional hypotheses on `K`: `P₀(𝔸)K = G(𝔸)` for the minimal parabolic `P₀` of the
  presentation `r`, the commutation of `P₀(𝔸) ∩ K` with the positive torus of every Siegel setup,
  and the extension of the full-quotient truncation `Λ^T` with respect to `K` to an orthogonal
  projection on `L²` for sufficiently regular `T`. A compact subgroup in Lapid's good position
  satisfies them when Arthur's Proposition 13.1 holds for it; the class they define is wider.
* `TruncatedWavePacketLimitStatement` is Lapid's sufficient condition for the same data, along
  every ray of truncation parameters in a direction on which the simple roots are positive.
* `localWavePacketInnerProductTruncationCompact_of_truncatedLimit` derives the first from the
  second, using the single direction `1 ⊗ r.data.ν`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Filter
open scoped CategoryTheory.MonObj TensorProduct Topology

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic
  ArthurTruncation ArthurParabolicSpaces

/-- Lapid 2011, Proposition 2 (p.314), for wave packets in `W_P`, under three additional
hypotheses on the compact subgroup `K`: `LocalWavePacketInnerProductStatement` with
`P₀(𝔸)K = G(𝔸)` for the minimal parabolic `P₀` of the presentation `r` (maximal split torus
`r.data.i`, generic cocharacter `r.data.ν`), with `P₀(𝔸) ∩ K` commuting with the positive torus of
every Siegel setup, and with the full-quotient truncation with respect to `K` (for reflection data
`D₀`) extending to an orthogonal projection on `L²(G(F) \ G(𝔸))` for sufficiently regular
parameters. These hypotheses do not include Lapid's good position of `K` with respect to `M₀`.
The conclusion is that of `LocalWavePacketInnerProductStatement`. -/
def LocalWavePacketInnerProductTruncationCompactStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    [IsAffine P'.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
    [IsAffine U'.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (iU' : U' ⟶ P') (l' : M' ⟶ P')
    [IsClosedImmersion (iU' ≫ p').hom.hom.left]
    (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation p' l' a')
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp) (π' : P' ⟶ M'),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    haveI : LocallyOfFiniteType P'.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
    ∀ hG : IsConnectedReductive G, LeviSubgroup.IsGeometricUnipotentRadical iU →
    LeviSubgroup.IsGeometricUnipotentRadical iU' → l' ≫ π' = 𝟙 M' →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact p' K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM' : Measure (AdelicGroupPoints F M')) [μM'.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM' →
    ∀ {n n' : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
      (e' : (Fin n' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P') (β' : (Fin n' → ℝ) → ℝ),
      Continuous β' → HasCompactSupport β' → ∫ y, β' y = 1 →
    ∀ (k : ℕ) (v : Fin k → AdelicGroupPoints F G → ℂ) (c : Fin k → (Fin n → ℝ) → ℂ)
      (S : Set (Fin n → ℝ))
      (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) →
      IsCompact S →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j) ∧ ∀ x ∉ S, c j x = 0) →
      (fun x => imaginaryParameter F P (e x)) '' S ⊆ D →
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) →
      (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
        E j lam = hK.eisensteinSeries (v j) lam) →
    ∀ (k' : ℕ) (v' : Fin k' → AdelicGroupPoints F G → ℂ) (c' : Fin k' → (Fin n' → ℝ) → ℂ)
      (S' : Set (Fin n' → ℝ))
      (E' : Fin k' → ComplexCharacterParameter F P' → AdelicGroupPoints F G → ℂ)
      (D' : Set (ComplexCharacterParameter F P')),
      (∀ j, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (v' j)) →
      IsCompact S' →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c' j) ∧ ∀ x ∉ S', c' j x = 0) →
      (fun x => imaginaryParameter F P' (e' x)) '' S' ⊆ D' →
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E' j lam g) D') →
      (∀ j, ∃ R : ℝ, ∀ lam, r'.IsRegularParameter hA' hT' R lam →
        E' j lam = hK'.eisensteinSeries (v' j) lam) →
    ∀ (T : Type) [Fintype T] (w : T → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
      (cw : T → (M' ⟶ M)),
      (∀ t, IsWeylConjugation p l p' l' (w t) (cw t)) →
      Function.Injective (fun t => weylParameter l (cw t) π') →
      (∀ s ∈ weylParameterSet p l p' l' π', ∃ t, weylParameter l (cw t) π' = s) →
    ∀ (m : ℕ) (ψ : T → Fin k → Fin m → AdelicGroupPoints F G → ℂ)
      (coeff : T → Fin k → Fin m → ComplexCharacterParameter F P → ℂ)
      (DM : Set (ComplexCharacterParameter F P)),
      (∀ t j i,
        IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψ t j i)) →
      (fun x => imaginaryParameter F P (e x)) '' S ⊆ DM →
      (∀ t j i, IsMeromorphicInCoordinatesOn (coeff t j i) DM) →
      (∀ t j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
        hK.intertwiningOperator hK' iU l iU' (cw t) π' (w t) (v j) lam g =
          ∑ i, coeff t j i lam * ψ t j i g) →
    ∀ (D₀ : RelativeRootReflectionData r.data.i)
      (hK₀ : IsIwasawaCompact (Standard.parabolicHom r.data.i r.data.ν ∅) K)
      (hρ₀ : Function.Bijective (restrictToTorus F r.data.i r.data.ν ∅)),
      (∀ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ r.data.T),
        AdelicSiegelFactors.IsSiegelAlgebraicSetup F G r.data.T r.data.i r.data.ν T₀ j →
          AdelicSiegelFactors.IsPositiveTorusCompatible F G r.data.T r.data.i r.data.ν T₀ j K) →
      (∃ C : ℝ, ∀ Tp : V r.data.T,
        (∀ β ∈ simpleRelativeRoots r.data.i r.data.ν, C < eval r.data.T β Tp) →
        IsOrthogonalL2Extension (rationalQuotientHaarMeasure F G)
          (fun f q => truncation hG r.isCompatible.maximalSplit D₀ hK₀ hρ₀ Tp
            (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out)) →
    let Θ : AdelicGroupPoints F G → ℂ := fun g =>
      ∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x)) g ∂(spectralMeasure n)
    let Θ' : AdelicGroupPoints F G → ℂ := fun g =>
      ∫ x, ∑ j, c' j x * E' j (imaginaryParameter F P' (e' x)) g ∂(spectralMeasure n')
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    MemLp (fun y : RationalQuotient F G => Θ y.out) 2 μG ∧
      MemLp (fun y : RationalQuotient F G => Θ' y.out) 2 μG ∧
      ∫ y, Θ y.out * (starRingEnd ℂ) (Θ' y.out) ∂μG =
        ∫ x, ∑ t, ∑ j, ∑ i, ∑ j',
            c j x * coeff t j i (imaginaryParameter F P (e x)) *
              (starRingEnd ℂ) (c' j' (e'.symm (realWeylParameter l (cw t) π' (e x)))) *
              inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ t j i) (v' j')
          ∂(spectralMeasure n)

/-- Lapid 2011, §8, p.328 (the sufficient condition obtained from Lemma 9), for the data of
`LocalWavePacketInnerProductTruncationCompactStatement` and every direction `v₀` on which every
simple root of `r.data.i`, `r.data.ν` is positive: the functions `y ↦ Θ(y.out)` and
`y ↦ Θ'(y.out)` on `G(F) \ G(𝔸)` are measurable and bounded on compact sets, their truncations
`Λ^{j v₀}` with respect to `K` are eventually square integrable with bounded norms, and
`(Λ^{j v₀} Θ, Λ^{j v₀} Θ')` tends to the right side of (4) as `j → ∞`. -/
def TruncatedWavePacketLimitStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    [IsAffine P'.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
    [IsAffine U'.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (iU' : U' ⟶ P') (l' : M' ⟶ P')
    [IsClosedImmersion (iU' ≫ p').hom.hom.left]
    (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation p' l' a')
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp) (π' : P' ⟶ M'),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    haveI : LocallyOfFiniteType P'.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
    ∀ hG : IsConnectedReductive G, LeviSubgroup.IsGeometricUnipotentRadical iU →
    LeviSubgroup.IsGeometricUnipotentRadical iU' → l' ≫ π' = 𝟙 M' →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact p' K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM' : Measure (AdelicGroupPoints F M')) [μM'.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM' →
    ∀ {n n' : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
      (e' : (Fin n' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P') (β' : (Fin n' → ℝ) → ℝ),
      Continuous β' → HasCompactSupport β' → ∫ y, β' y = 1 →
    ∀ (k : ℕ) (v : Fin k → AdelicGroupPoints F G → ℂ) (c : Fin k → (Fin n → ℝ) → ℂ)
      (S : Set (Fin n → ℝ))
      (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) →
      IsCompact S →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j) ∧ ∀ x ∉ S, c j x = 0) →
      (fun x => imaginaryParameter F P (e x)) '' S ⊆ D →
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) →
      (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
        E j lam = hK.eisensteinSeries (v j) lam) →
    ∀ (k' : ℕ) (v' : Fin k' → AdelicGroupPoints F G → ℂ) (c' : Fin k' → (Fin n' → ℝ) → ℂ)
      (S' : Set (Fin n' → ℝ))
      (E' : Fin k' → ComplexCharacterParameter F P' → AdelicGroupPoints F G → ℂ)
      (D' : Set (ComplexCharacterParameter F P')),
      (∀ j, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (v' j)) →
      IsCompact S' →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c' j) ∧ ∀ x ∉ S', c' j x = 0) →
      (fun x => imaginaryParameter F P' (e' x)) '' S' ⊆ D' →
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E' j lam g) D') →
      (∀ j, ∃ R : ℝ, ∀ lam, r'.IsRegularParameter hA' hT' R lam →
        E' j lam = hK'.eisensteinSeries (v' j) lam) →
    ∀ (T : Type) [Fintype T] (w : T → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
      (cw : T → (M' ⟶ M)),
      (∀ t, IsWeylConjugation p l p' l' (w t) (cw t)) →
      Function.Injective (fun t => weylParameter l (cw t) π') →
      (∀ s ∈ weylParameterSet p l p' l' π', ∃ t, weylParameter l (cw t) π' = s) →
    ∀ (m : ℕ) (ψ : T → Fin k → Fin m → AdelicGroupPoints F G → ℂ)
      (coeff : T → Fin k → Fin m → ComplexCharacterParameter F P → ℂ)
      (DM : Set (ComplexCharacterParameter F P)),
      (∀ t j i,
        IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψ t j i)) →
      (fun x => imaginaryParameter F P (e x)) '' S ⊆ DM →
      (∀ t j i, IsMeromorphicInCoordinatesOn (coeff t j i) DM) →
      (∀ t j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
        hK.intertwiningOperator hK' iU l iU' (cw t) π' (w t) (v j) lam g =
          ∑ i, coeff t j i lam * ψ t j i g) →
    ∀ (D₀ : RelativeRootReflectionData r.data.i)
      (hK₀ : IsIwasawaCompact (Standard.parabolicHom r.data.i r.data.ν ∅) K)
      (hρ₀ : Function.Bijective (restrictToTorus F r.data.i r.data.ν ∅)),
      (∀ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ r.data.T),
        AdelicSiegelFactors.IsSiegelAlgebraicSetup F G r.data.T r.data.i r.data.ν T₀ j →
          AdelicSiegelFactors.IsPositiveTorusCompatible F G r.data.T r.data.i r.data.ν T₀ j K) →
      (∃ C : ℝ, ∀ Tp : V r.data.T,
        (∀ β ∈ simpleRelativeRoots r.data.i r.data.ν, C < eval r.data.T β Tp) →
        IsOrthogonalL2Extension (rationalQuotientHaarMeasure F G)
          (fun f q => truncation hG r.isCompatible.maximalSplit D₀ hK₀ hρ₀ Tp
            (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out)) →
    ∀ v₀ : V r.data.T, (∀ β ∈ simpleRelativeRoots r.data.i r.data.ν, 0 < eval r.data.T β v₀) →
    let Θ : AdelicGroupPoints F G → ℂ := fun g =>
      ∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x)) g ∂(spectralMeasure n)
    let Θ' : AdelicGroupPoints F G → ℂ := fun g =>
      ∫ x, ∑ j, c' j x * E' j (imaginaryParameter F P' (e' x)) g ∂(spectralMeasure n')
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    let trunc (j : ℕ) (b : RationalQuotient F G → ℂ) (q : RationalQuotient F G) : ℂ :=
      truncation hG r.isCompatible.maximalSplit D₀ hK₀ hρ₀ ((j : ℝ) • v₀)
        (fun x => b (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out
    let f : RationalQuotient F G → ℂ := fun y => Θ y.out
    let f' : RationalQuotient F G → ℂ := fun y => Θ' y.out
    Measurable f ∧ Measurable f' ∧
      (∀ C : Set (RationalQuotient F G), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖f x‖ ≤ B) ∧
      (∀ C : Set (RationalQuotient F G), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖f' x‖ ≤ B) ∧
      (∀ᶠ j : ℕ in atTop, MemLp (trunc j f) 2 μG) ∧
      (∀ᶠ j : ℕ in atTop, MemLp (trunc j f') 2 μG) ∧
      (∃ B : ℝ, ∀ᶠ j : ℕ in atTop,
        (∫ q, trunc j f q * (starRingEnd ℂ) (trunc j f q) ∂μG).re ≤ B) ∧
      (∃ B : ℝ, ∀ᶠ j : ℕ in atTop,
        (∫ q, trunc j f' q * (starRingEnd ℂ) (trunc j f' q) ∂μG).re ≤ B) ∧
      Tendsto (fun j : ℕ => ∫ q, trunc j f q * (starRingEnd ℂ) (trunc j f' q) ∂μG) atTop
        (𝓝 (∫ x, ∑ t, ∑ j, ∑ i, ∑ j',
            c j x * coeff t j i (imaginaryParameter F P (e x)) *
              (starRingEnd ℂ) (c' j' (e'.symm (realWeylParameter l (cw t) π' (e x)))) *
              inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ t j i) (v' j')
          ∂(spectralMeasure n)))

/-- Lapid 2011, §8, p.328, opening: Lemma 9 reduces Proposition 2 to the limit of truncated
inner products. The measure-theoretic form of Lemma 9, `fullQuotientTruncationPairing`, applied
along the single ray of `1 ⊗ r.data.ν`, gives `LocalWavePacketInnerProductTruncationCompactStatement`
from `TruncatedWavePacketLimitStatement`. -/
theorem localWavePacketInnerProductTruncationCompact_of_truncatedLimit
    (hlim : TruncatedWavePacketLimitStatement) :
    LocalWavePacketInnerProductTruncationCompactStatement := by
  intro F _ _ G P M U P' M' U' A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT p' _ iU' l' _
    a' r' _ _ _ hA' hT' π' hG hU hU' hlπ' K hK hK' Nr dr rho hsmooth hcalc hKmax hrho μM' _ hμM'
    n n' e e' β' hβc' hβs' hβ1' k v c S E D hv hS hc hD hE hEis k' v' c' S' E' D' hv' hS' hc' hD'
    hE' hEis' T _ w cw hw hinj hsurj m ψ coeff DM hψ hDM hcoeff hexp D₀ hK₀ hρ₀ hpos hproj
    Θ Θ' μG
  have hi := r.isCompatible.maximalSplit
  have hν := r.isCompatible.generic
  have hv₀ : ∀ β ∈ simpleRelativeRoots r.data.i r.data.ν,
      0 < eval r.data.T β ((1 : ℝ) ⊗ₜ[ℤ] r.data.ν) := fun β hβ => cocharacter_simple_pos hβ
  obtain ⟨hfm, hf'm, hfb, hf'b, hL2, hL2', hdiag, hdiag', hmix⟩ :=
    hlim F G P M U P' M' U' A A' p iU l a r hA hT p' iU' l' a' r' hA' hT' π' hG hU hU'
      hlπ' K hK hK' rho hsmooth hcalc hKmax hrho μM' hμM' e e' β' hβc' hβs' hβ1' k v c S E D hv hS
      hc hD hE hEis k' v' c' S' E' D' hv' hS' hc' hD' hE' hEis' T w cw hw hinj hsurj m ψ coeff DM
      hψ hDM hcoeff hexp D₀ hK₀ hρ₀ hpos hproj _ hv₀
  exact fullQuotientTruncationPairing truncationFiniteness F G r.data.T r.data.i r.data.ν hG hi hν
    D₀ K hK₀ hρ₀ _ hv₀ hproj _ _ hfm hf'm hfb hf'b _ hL2 hL2' hdiag hdiag' hmix

end Langlands.Global
