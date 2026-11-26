import Langlands.Global.AdelicLocalWavePacketStatement
import Langlands.Global.ArthurTruncationL2Statement
import Langlands.Global.LapidArthurTruncationPairing
import Langlands.Global.ArthurTruncationFinitenessProof
import Langlands.Global.ArthurCuspidalRepresentativeBounds
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof

/-! # Lapid's Proposition 2 for holomorphic families and one compact subgroup

Lapid 2011, §3, p.314, states Proposition 2 for wave packets of smooth maps into a
finite-dimensional subspace of `A^2_P` whose Eisenstein series `E_P(·, φ(λ), λ)` is smooth, for
one maximal compact subgroup `K` in good position (§2, p.311). This module states formula (4)
for wave packets whose inducing vectors are holomorphic families `λ ↦ ∑_i b_i(λ) v_i` with
entire coefficients `b_i`, in the form that SOME maximal compact `K` with
`P(𝔸)K = P'(𝔸)K = G(𝔸)` satisfies it for all such data, together with Lapid's sufficient
condition from §8 in the same existential form.

* `LocalWavePacketSectionSomeCompactStatement`: some `K` satisfies formula (4) for all such
  families.
* `TruncatedWavePacketSectionSomeCompactLimitStatement`: some `K` with `P₀(𝔸)K = G(𝔸)` and
  an orthogonal-projection extension of the full-quotient truncation satisfies the limit of
  truncated inner products for all such families.
* `localWavePacketSectionSomeCompact_of_limit`: the first from the second (Lemma 9).
* `LocalWavePacketSomeCompactChangeStatement`: `LocalWavePacketInnerProductStatement`, for every
  maximal compact `K` with `P(𝔸)K = P'(𝔸)K = G(𝔸)` and fixed inducing vectors, from the first
  statement. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Filter
open scoped CategoryTheory.MonObj TensorProduct Topology

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic
  ArthurTruncation ArthurParabolicSpaces

/-- Lapid 2011, Proposition 2 (p.314), formula (4), for wave packets of holomorphic families of
inducing vectors and one compact subgroup. For the parabolic data `P`, `r`, `P'`, `r'` of
`LocalWavePacketInnerProductStatement` there is a maximal compact `K` with
`P(𝔸)K = P'(𝔸)K = G(𝔸)` such that the following holds for all data with respect to `K`. The
packet of `P` is `Θ(g) = ∫ ∑_j c_j(x) E_j(i e(x))(g) dx`, where `E_j` is holomorphic near the
support and agrees on the regular region with the Eisenstein series of the family
`λ ↦ ∑_i b_{j,i}(λ) v_{j,i}`, the `b_{j,i}` entire; likewise for `P'`. The expansions are those
of `M(w, λ) (∑_i b_{j,i}(λ) v_{j,i})`. The conclusion is `Θ, Θ' ∈ L²(G(F) \ G(𝔸))` and
`(Θ, Θ') = ∫ ∑_{w ∈ Ω(P,P')} (M(w, λ)φ(λ), φ'(wλ))_{P'} dλ`. -/
def LocalWavePacketSectionSomeCompactStatement : Prop :=
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
    ∃ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact p' K), IsMaximalCompactSubgroup F G K ∧
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth), IsClosedSubgroup rho →
    ∀ (μM' : Measure (AdelicGroupPoints F M')) [μM'.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM' →
    ∀ {n n' : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
      (e' : (Fin n' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P') (β' : (Fin n' → ℝ) → ℝ),
      Continuous β' → HasCompactSupport β' → ∫ y, β' y = 1 →
    ∀ (k q : ℕ) (v : Fin k → Fin q → AdelicGroupPoints F G → ℂ)
      (b : Fin k → Fin q → ComplexCharacterParameter F P → ℂ)
      (c : Fin k → (Fin n → ℝ) → ℂ) (S : Set (Fin n → ℝ))
      (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      (∀ j i, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j i)) →
      (∀ j i, IsMeromorphicInCoordinatesOn (b j i) Set.univ) →
      IsCompact S →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j) ∧ ∀ x ∉ S, c j x = 0) →
      (fun x => imaginaryParameter F P (e x)) '' S ⊆ D →
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) →
      (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
        E j lam g = ∑ i, b j i lam * hK.eisensteinSeries (v j i) lam g) →
    ∀ (k' q' : ℕ) (v' : Fin k' → Fin q' → AdelicGroupPoints F G → ℂ)
      (b' : Fin k' → Fin q' → ComplexCharacterParameter F P' → ℂ)
      (c' : Fin k' → (Fin n' → ℝ) → ℂ) (S' : Set (Fin n' → ℝ))
      (E' : Fin k' → ComplexCharacterParameter F P' → AdelicGroupPoints F G → ℂ)
      (D' : Set (ComplexCharacterParameter F P')),
      (∀ j i,
        IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (v' j i)) →
      (∀ j i, IsMeromorphicInCoordinatesOn (b' j i) Set.univ) →
      IsCompact S' →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c' j) ∧ ∀ x ∉ S', c' j x = 0) →
      (fun x => imaginaryParameter F P' (e' x)) '' S' ⊆ D' →
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E' j lam g) D') →
      (∀ j, ∃ R : ℝ, ∀ lam, r'.IsRegularParameter hA' hT' R lam → ∀ g,
        E' j lam g = ∑ i, b' j i lam * hK'.eisensteinSeries (v' j i) lam g) →
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
        ∑ i, b j i lam * hK.intertwiningOperator hK' iU l iU' (cw t) π' (w t) (v j i) lam g =
          ∑ i, coeff t j i lam * ψ t j i g) →
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
        ∫ x, ∑ t, ∑ j, ∑ i, ∑ j', ∑ i',
            c j x * coeff t j i (imaginaryParameter F P (e x)) *
              (starRingEnd ℂ) (c' j' (e'.symm (realWeylParameter l (cw t) π' (e x)))) *
              (starRingEnd ℂ)
                (b' j' i' (weylParameter l (cw t) π' (imaginaryParameter F P (e x)))) *
              inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ t j i) (v' j' i')
          ∂(spectralMeasure n)

/-- Lapid 2011, §8, p.328 (the sufficient condition obtained from Lemma 9), for one compact
subgroup. For the parabolic data `P`, `r`, `P'`, `r'` there is a maximal compact `K` with
`P(𝔸)K = P'(𝔸)K = P₀(𝔸)K = G(𝔸)` for the minimal parabolic `P₀` of `r`, whose full-quotient
truncation with respect to `K` extends, for every reflection data `D₀` and comparison `hρ₀`
and sufficiently regular parameters, to an orthogonal projection on `L²(G(F) \ G(𝔸))`, such
that the following holds for the data of `LocalWavePacketSectionSomeCompactStatement` with
respect to `K`, every `D₀`, `hρ₀` and every direction `v₀` on which every simple root of
`r.data.i`, `r.data.ν` is positive: the functions `y ↦ Θ(y.out)` and `y ↦ Θ'(y.out)` on
`G(F) \ G(𝔸)` are measurable and bounded on compact sets, their full-quotient truncations
`Λ^{j v₀}` are eventually square integrable with bounded norms, and
`(Λ^{j v₀} Θ, Λ^{j v₀} Θ')` tends to the right side of (4) as `j → ∞`. -/
def TruncatedWavePacketSectionSomeCompactLimitStatement : Prop :=
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
    ∃ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact p' K)
      (hK₀ : IsIwasawaCompact (Standard.parabolicHom r.data.i r.data.ν ∅) K),
      IsMaximalCompactSubgroup F G K ∧
      (∀ (D₀ : RelativeRootReflectionData r.data.i)
        (hρ₀ : Function.Bijective (restrictToTorus F r.data.i r.data.ν ∅)),
        ∃ C : ℝ, ∀ Tp : V r.data.T,
          (∀ β ∈ simpleRelativeRoots r.data.i r.data.ν, C < eval r.data.T β Tp) →
          IsOrthogonalL2Extension (rationalQuotientHaarMeasure F G)
            (fun f q => truncation hG r.isCompatible.maximalSplit D₀ hK₀ hρ₀ Tp
              (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out)) ∧
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth), IsClosedSubgroup rho →
    ∀ (μM' : Measure (AdelicGroupPoints F M')) [μM'.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM' →
    ∀ {n n' : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
      (e' : (Fin n' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P') (β' : (Fin n' → ℝ) → ℝ),
      Continuous β' → HasCompactSupport β' → ∫ y, β' y = 1 →
    ∀ (k q : ℕ) (v : Fin k → Fin q → AdelicGroupPoints F G → ℂ)
      (b : Fin k → Fin q → ComplexCharacterParameter F P → ℂ)
      (c : Fin k → (Fin n → ℝ) → ℂ) (S : Set (Fin n → ℝ))
      (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      (∀ j i, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j i)) →
      (∀ j i, IsMeromorphicInCoordinatesOn (b j i) Set.univ) →
      IsCompact S →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j) ∧ ∀ x ∉ S, c j x = 0) →
      (fun x => imaginaryParameter F P (e x)) '' S ⊆ D →
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) →
      (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
        E j lam g = ∑ i, b j i lam * hK.eisensteinSeries (v j i) lam g) →
    ∀ (k' q' : ℕ) (v' : Fin k' → Fin q' → AdelicGroupPoints F G → ℂ)
      (b' : Fin k' → Fin q' → ComplexCharacterParameter F P' → ℂ)
      (c' : Fin k' → (Fin n' → ℝ) → ℂ) (S' : Set (Fin n' → ℝ))
      (E' : Fin k' → ComplexCharacterParameter F P' → AdelicGroupPoints F G → ℂ)
      (D' : Set (ComplexCharacterParameter F P')),
      (∀ j i,
        IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (v' j i)) →
      (∀ j i, IsMeromorphicInCoordinatesOn (b' j i) Set.univ) →
      IsCompact S' →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c' j) ∧ ∀ x ∉ S', c' j x = 0) →
      (fun x => imaginaryParameter F P' (e' x)) '' S' ⊆ D' →
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E' j lam g) D') →
      (∀ j, ∃ R : ℝ, ∀ lam, r'.IsRegularParameter hA' hT' R lam → ∀ g,
        E' j lam g = ∑ i, b' j i lam * hK'.eisensteinSeries (v' j i) lam g) →
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
        ∑ i, b j i lam * hK.intertwiningOperator hK' iU l iU' (cw t) π' (w t) (v j i) lam g =
          ∑ i, coeff t j i lam * ψ t j i g) →
    ∀ (D₀ : RelativeRootReflectionData r.data.i)
      (hρ₀ : Function.Bijective (restrictToTorus F r.data.i r.data.ν ∅)),
    ∀ v₀ : V r.data.T, (∀ β ∈ simpleRelativeRoots r.data.i r.data.ν, 0 < eval r.data.T β v₀) →
    let Θ : AdelicGroupPoints F G → ℂ := fun g =>
      ∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x)) g ∂(spectralMeasure n)
    let Θ' : AdelicGroupPoints F G → ℂ := fun g =>
      ∫ x, ∑ j, c' j x * E' j (imaginaryParameter F P' (e' x)) g ∂(spectralMeasure n')
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    let trunc (j : ℕ) (f : RationalQuotient F G → ℂ) (y : RationalQuotient F G) : ℂ :=
      truncation hG r.isCompatible.maximalSplit D₀ hK₀ hρ₀ ((j : ℝ) • v₀)
        (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) y.out
    let f : RationalQuotient F G → ℂ := fun y => Θ y.out
    let f' : RationalQuotient F G → ℂ := fun y => Θ' y.out
    Measurable f ∧ Measurable f' ∧
      (∀ C : Set (RationalQuotient F G), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖f x‖ ≤ B) ∧
      (∀ C : Set (RationalQuotient F G), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖f' x‖ ≤ B) ∧
      (∀ᶠ j : ℕ in atTop, MemLp (trunc j f) 2 μG) ∧
      (∀ᶠ j : ℕ in atTop, MemLp (trunc j f') 2 μG) ∧
      (∃ B : ℝ, ∀ᶠ j : ℕ in atTop,
        (∫ y, trunc j f y * (starRingEnd ℂ) (trunc j f y) ∂μG).re ≤ B) ∧
      (∃ B : ℝ, ∀ᶠ j : ℕ in atTop,
        (∫ y, trunc j f' y * (starRingEnd ℂ) (trunc j f' y) ∂μG).re ≤ B) ∧
      Tendsto (fun j : ℕ => ∫ y, trunc j f y * (starRingEnd ℂ) (trunc j f' y) ∂μG) atTop
        (𝓝 (∫ x, ∑ t, ∑ j, ∑ i, ∑ j', ∑ i',
            c j x * coeff t j i (imaginaryParameter F P (e x)) *
              (starRingEnd ℂ) (c' j' (e'.symm (realWeylParameter l (cw t) π' (e x)))) *
              (starRingEnd ℂ)
                (b' j' i' (weylParameter l (cw t) π' (imaginaryParameter F P (e x)))) *
              inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ t j i) (v' j' i')
          ∂(spectralMeasure n)))

/-- Lapid 2011, §8, p.328, opening: Lemma 9 reduces Proposition 2 to the limit of truncated
inner products. The compact subgroup of `TruncatedWavePacketSectionSomeCompactLimitStatement`
serves for `LocalWavePacketSectionSomeCompactStatement`: reflection data exist
(`relativeRootReflectionExistence`), the character comparison is
`bijective_restrictToTorus_minimal`, and `fullQuotientTruncationPairing`, the measure-theoretic
form of Lemma 9, applied along the ray of `1 ⊗ r.data.ν`, gives formula (4). -/
theorem localWavePacketSectionSomeCompact_of_limit
    (hlim : TruncatedWavePacketSectionSomeCompactLimitStatement) :
    LocalWavePacketSectionSomeCompactStatement := by
  intro F _ _ G P M U P' M' U' A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT p' _ iU' l' _
    a' r' _ _ _ hA' hT' π' hG hU hU' hlπ'
  obtain ⟨K, hK, hK', hK₀, hKmax, hproj, hlimK⟩ :=
    hlim F G P M U P' M' U' A A' p iU l a r hA hT p' iU' l' a' r' hA' hT' π' hG hU hU' hlπ'
  refine ⟨K, hK, hK', hKmax, ?_⟩
  intro Nr dr rho hsmooth hcalc hrho μM' _ hμM' n n' e e' β' hβc' hβs' hβ1' k q v b c S E D hv
    hb hS hc hD hE hEis k' q' v' b' c' S' E' D' hv' hb' hS' hc' hD' hE' hEis' T _ w cw hw hinj
    hsurj m ψ coeff DM hψ hDM hcoeff hexp Θ Θ' μG
  have hi := r.isCompatible.maximalSplit
  have hν := r.isCompatible.generic
  obtain ⟨D₀, -⟩ := relativeRootReflectionExistence F G hG r.data.T r.data.i hi
  have hρ₀ := bijective_restrictToTorus_minimal F G r.data.T r.data.i r.data.ν hG hi hν
  have hv₀ : ∀ β ∈ simpleRelativeRoots r.data.i r.data.ν,
      0 < eval r.data.T β ((1 : ℝ) ⊗ₜ[ℤ] r.data.ν) := fun β hβ => cocharacter_simple_pos hβ
  obtain ⟨hfm, hf'm, hfb, hf'b, hL2, hL2', hdiag, hdiag', hmix⟩ :=
    hlimK rho hsmooth hcalc hrho μM' hμM' e e' β' hβc' hβs' hβ1' k q v b c S E D hv hb hS hc hD
      hE hEis k' q' v' b' c' S' E' D' hv' hb' hS' hc' hD' hE' hEis' T w cw hw hinj hsurj m ψ
      coeff DM hψ hDM hcoeff hexp D₀ hρ₀ _ hv₀
  exact fullQuotientTruncationPairing truncationFiniteness F G r.data.T r.data.i r.data.ν hG hi hν
    D₀ K hK₀ hρ₀ _ hv₀ (hproj D₀ hρ₀) _ _ hfm hf'm hfb hf'b _ hL2 hL2' hdiag hdiag' hmix

/-- The change of the compact subgroup in Lapid's Proposition 2. The proposition asserts that
formula (4) for holomorphic families of inducing vectors and one compact subgroup, for every
choice of the parabolic data (`LocalWavePacketSectionSomeCompactStatement`), implies
`LocalWavePacketInnerProductStatement`, which is stated for every maximal compact `K` with
`P(𝔸)K = P'(𝔸)K = G(𝔸)` and fixed inducing vectors. -/
def LocalWavePacketSomeCompactChangeStatement : Prop :=
  LocalWavePacketSectionSomeCompactStatement → LocalWavePacketInnerProductStatement

end Langlands.Global
