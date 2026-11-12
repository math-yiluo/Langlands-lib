import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Unitarity of intertwining operators on the imaginary axis

Lapid 2011, §2 (p.312), and Mœglin–Waldspurger IV.1.11 (b), IV.3.12 and VI.2.1 (i): for
`λ ∈ i𝔞_P^*` the intertwining operator `M(w, λ) : A^2_P → A^2_{P'}` is holomorphic and unitary,
`(M(w, λ)φ, M(w, λ)φ')_{P'} = (φ, φ')_P`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Holomorphy and unitarity of `M(w, λ)` on the imaginary axis (Lapid 2011, p.312;
Mœglin–Waldspurger IV.1.11 (b), VI.2.1 (i)). Let `P = MU` be a parabolic with presentation `r`,
`P' = M'U'` a parabolic with rational Levi `l'`, unipotent radical `iU'` and Levi projection `π'`
(`P' = M' ⋉ U'`), `(w, cw)` a presentation of an element of
`W(P, P')`, and
`K` a maximal compact subgroup with `P(𝔸)K = P'(𝔸)K = G(𝔸)`. Let `μ_M`, `μ_{M'}` be Haar
measures compatible with Mathlib's Haar measure on `G(𝔸)` for the Iwasawa decompositions of `P`
and `P'`, let `e` be coordinates on `X^*(P) ⊗ ℝ` and `e' = w ∘ e` the transported coordinates on
`X^*(P') ⊗ ℝ`, and let `β`, `β'` be weights with integral `1`, which define the inner products
`(·,·)_P` and `(·,·)_{P'}` (`inducedInnerProduct`). Let `v j ∈ A^2_P` and suppose that
`M(w, λ) v j = ∑ i, coeff j i λ • ψ j i` for `Re λ` sufficiently regular, with
`ψ j i ∈ A^2_{P'}` and `coeff j i` meromorphic with one domain of holomorphy `DM`. Then there are
coefficients `coeff'`, meromorphic with one domain `DM'` containing `i(X^*(P) ⊗ ℝ)`, that give
the same functions `∑ i, coeff' j i λ • ψ j i = ∑ i, coeff j i λ • ψ j i` for `λ ∈ DM ∩ DM'`,
and for every imaginary `λ`
`(∑ i, coeff' j i λ • ψ j i, ∑ i', coeff' j' i' λ • ψ j' i')_{P'} = (v j, v j')_P`. -/
def IntertwiningImaginaryUnitarityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
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
    [IsClosedImmersion (iU' ≫ p').hom.hom.left] (π' : P' ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (cw : M' ⟶ M),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    haveI : LocallyOfFiniteType P'.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsParabolicSubgroup p' → LeviSubgroup.IsGeometricUnipotentRadical iU' →
    IsRationalLeviSubgroup l' → IsIso (subgroupMultiplication l' iU') → l' ≫ π' = 𝟙 M' →
    IsWeylConjugation p l p' l' w cw →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact p' K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure]
      (μM' : Measure (AdelicGroupPoints F M')) [μM'.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM →
      IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM' →
    ∀ {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
      (e' : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P'),
      (∀ x, e' x = realWeylParameter l cw π' (e x)) →
    ∀ (β β' : (Fin n → ℝ) → ℝ),
      Continuous β → HasCompactSupport β → ∫ y, β y = 1 →
      Continuous β' → HasCompactSupport β' → ∫ y, β' y = 1 →
    ∀ (k m : ℕ) (v : Fin k → AdelicGroupPoints F G → ℂ)
      (ψ : Fin k → Fin m → AdelicGroupPoints F G → ℂ)
      (coeff : Fin k → Fin m → ComplexCharacterParameter F P → ℂ)
      (DM : Set (ComplexCharacterParameter F P)),
      (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) →
      (∀ j i,
        IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψ j i)) →
      (∀ j i, IsMeromorphicInCoordinatesOn (coeff j i) DM) →
      (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
        hK.intertwiningOperator hK' iU l iU' cw π' w (v j) lam g =
          ∑ i, coeff j i lam * ψ j i g) →
    ∃ (coeff' : Fin k → Fin m → ComplexCharacterParameter F P → ℂ)
      (DM' : Set (ComplexCharacterParameter F P)),
      Set.range (imaginaryParameter F P) ⊆ DM' ∧
      (∀ j i, IsMeromorphicInCoordinatesOn (coeff' j i) DM') ∧
      (∀ j, ∀ lam ∈ DM ∩ DM', ∀ g,
        ∑ i, coeff' j i lam * ψ j i g = ∑ i, coeff j i lam * ψ j i g) ∧
      ∀ (mu : RealCharacterParameter F P) (j j' : Fin k),
        ∑ i, ∑ i', coeff' j i (imaginaryParameter F P mu) *
            (starRingEnd ℂ) (coeff' j' i' (imaginaryParameter F P mu)) *
            inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ j i) (ψ j' i') =
          inducedInnerProduct K hK.isCompact p l μM e β (v j) (v j')

end Langlands.Global
