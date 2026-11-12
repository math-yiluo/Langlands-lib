import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Bounded wave packets of Eisenstein series

Lapid 2011, Lemma 10 (p.329): Proposition 2 holds for bounded measurable `φ` from `i𝔞_P^*` to a
finite-dimensional subspace of `A^2_P`, supported in a compact set on which the Eisenstein series
are regular; in particular `‖Θ_φ‖² ≤ |Ω| ‖φ‖²_*` (19), stated here with the sharper constant
`|Ω(P, P)|`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Lapid 2011, Lemma 10, inner product formula: Proposition 2 for bounded measurable wave
packets supported where the Eisenstein series are regular. The data are those of
`WavePacketInnerProductStatement`, except that the coefficients `c j` are measurable, bounded and
zero outside a compact set `S` of coordinates, the continuations `E j` are only required to be
holomorphic on `D ⊇ {i e(x) | x ∈ S}`, the coefficients `coeff t j i` on `DM ⊇ {i e(x) | x ∈ S}`,
and similarly for `P'` with `S'`. The conclusion is that of Proposition 2: the wave packets `Θ`
and `Θ'` are square integrable on `G(F) \ G(𝔸)`, and
`(Θ, Θ') = ∫ ∑ t, (M(w t, λ)φ(λ), φ'(w_t λ))_{P'} dλ`, written out in the data. -/
def BoundedWavePacketInnerProductStatement : Prop :=
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
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
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
      (∀ j, Measurable (c j) ∧ (∃ C : ℝ, ∀ x, ‖c j x‖ ≤ C) ∧ ∀ x ∉ S, c j x = 0) →
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
      (∀ j, Measurable (c' j) ∧ (∃ C : ℝ, ∀ x, ‖c' j x‖ ≤ C) ∧ ∀ x ∉ S', c' j x = 0) →
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

/-- Lapid 2011, Lemma 10, bound (19): `‖Θ_φ‖² ≤ |Ω(P, P)| · ∫_{i𝔞_P^*} ‖φ(λ)‖²_P dλ` for a
bounded measurable wave packet `φ` supported where the Eisenstein series are regular. Let
`P = MU` be a parabolic with presentation `r` and Levi projection `π`, `K` a maximal compact
subgroup with `P(𝔸)K = G(𝔸)`, `μ_M` a Haar measure compatible with Mathlib's Haar measure on
`G(𝔸)` for the Iwasawa decomposition, `e` coordinates on `X^*(P) ⊗ ℝ` and `β` a weight with
integral `1`, which define `dλ` (`spectralMeasure`) and `(·,·)_P` (`inducedInnerProduct`). Let
`φ(x) = ∑ j, c j x · v j` with `v j ∈ A^2_P` and `c j` measurable, bounded and zero outside a
compact set `S`, and let `E j` be meromorphic continuations of `E(v j, λ)` holomorphic on
`D ⊇ {i e(x) | x ∈ S}`. Then `Ω(P, P)` (`weylParameterSet p l p l π`) is finite, the wave packet
`Θ = ∫ ∑ j, c j x • E j (i e(x)) dx` is square integrable on `G(F) \ G(𝔸)`, and
`∫ |Θ|² ≤ |Ω(P, P)| · ∫ (φ(x), φ(x))_P dx`. -/
def BoundedWavePacketNormBoundStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (π : P ⟶ M),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU → l ≫ π = 𝟙 M →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM →
    ∀ {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ),
      Continuous β → HasCompactSupport β → ∫ y, β y = 1 →
    ∀ (k : ℕ) (v : Fin k → AdelicGroupPoints F G → ℂ) (c : Fin k → (Fin n → ℝ) → ℂ)
      (S : Set (Fin n → ℝ))
      (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) →
      IsCompact S →
      (∀ j, Measurable (c j) ∧ (∃ C : ℝ, ∀ x, ‖c j x‖ ≤ C) ∧ ∀ x ∉ S, c j x = 0) →
      (fun x => imaginaryParameter F P (e x)) '' S ⊆ D →
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) →
      (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
        E j lam = hK.eisensteinSeries (v j) lam) →
    let Θ : AdelicGroupPoints F G → ℂ := fun g =>
      ∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x)) g ∂(spectralMeasure n)
    let φ : (Fin n → ℝ) → AdelicGroupPoints F G → ℂ := fun x g => ∑ j, c j x * v j g
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    (weylParameterSet p l p l π).Finite ∧
      MemLp (fun y : RationalQuotient F G => Θ y.out) 2 μG ∧
      ∫ y, ‖Θ y.out‖ ^ 2 ∂μG ≤
        Nat.card (weylParameterSet p l p l π) *
          ∫ x, (inducedInnerProduct K hK.isCompact p l μM e β (φ x) (φ x)).re
            ∂(spectralMeasure n)

/-- Lapid 2011, Lemma 10: Proposition 2 for bounded measurable wave packets supported where the
Eisenstein series are regular, and the bound (19). -/
def BoundedWavePacketStatement : Prop :=
  BoundedWavePacketInnerProductStatement ∧ BoundedWavePacketNormBoundStatement

end Langlands.Global
