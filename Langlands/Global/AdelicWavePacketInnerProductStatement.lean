import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Square integrability and inner products of wave packets of Eisenstein series

Lapid 2011, Proposition 2 (p.314): for `φ ∈ W_P` the wave packet
`Θ_{P,φ} = ∫_{i𝔞_P^*} E_P(·, φ(λ), λ) dλ` lies in `L²(G(F) \ G(𝔸))`, and
`(Θ_{P,φ}, Θ_{P',φ'}) = ∫_{i𝔞_P^*} ∑_{w ∈ Ω(P, P')} (M(w, λ)φ(λ), φ'(wλ))_{P'} dλ`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Wave packets of Eisenstein series and their inner products (Lapid 2011, Proposition 2).
Let `P = MU` and `P' = M'U'` be parabolics with presentations `r`, `r'`, `π'` a Levi projection
of `P'`, `K` a maximal compact subgroup with `P(𝔸)K = P'(𝔸)K = G(𝔸)`, and `μ_{M'}` a Haar
measure compatible with Mathlib's Haar measure on `G(𝔸)` for the Iwasawa decomposition of `P'`.
Coordinates `e`, `e'` on `𝔞_P^*`, `𝔞_{P'}^*` give the measures `dλ` on `i𝔞_P^*`, `i𝔞_{P'}^*`
(`spectralMeasure`), and a weight `β'` with `∫ β' = 1` gives `(·,·)_{P'}`
(`inducedInnerProduct`). Let `φ = ∑ j, c j · v j` with `v j ∈ A^2_P` and `c j` smooth and
compactly supported in the coordinates `x` of `λ = i e(x)`, and let `E j` be meromorphic
continuations of `E(v j, λ)` holomorphic near `i𝔞_P^*`; similarly `φ'` for `P'`. Let
`(w t, cw t)` present each element of `Ω(P, P')` once, and let
`M(w t, λ) v j = ∑ i, coeff t j i λ • ψ t j i` with `ψ t j i ∈ A^2_{P'}` and `coeff t j i`
meromorphic and holomorphic near `i𝔞_P^*`. Then the wave packets
`Θ = ∫ ∑ j, c j x • E j (i e(x)) dx` and `Θ'` are square integrable on `G(F) \ G(𝔸)`, and
`(Θ, Θ') = ∫ ∑ t, (M(w t, λ)φ(λ), φ'(w_t λ))_{P'} dλ`, written out in the data. -/
def WavePacketInnerProductStatement : Prop :=
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
      (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j) ∧ HasCompactSupport (c j)) →
      Set.range (imaginaryParameter F P) ⊆ D →
      (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) →
      (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
        E j lam = hK.eisensteinSeries (v j) lam) →
    ∀ (k' : ℕ) (v' : Fin k' → AdelicGroupPoints F G → ℂ) (c' : Fin k' → (Fin n' → ℝ) → ℂ)
      (E' : Fin k' → ComplexCharacterParameter F P' → AdelicGroupPoints F G → ℂ)
      (D' : Set (ComplexCharacterParameter F P')),
      (∀ j, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (v' j)) →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c' j) ∧ HasCompactSupport (c' j)) →
      Set.range (imaginaryParameter F P') ⊆ D' →
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
      Set.range (imaginaryParameter F P) ⊆ DM →
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

end Langlands.Global
