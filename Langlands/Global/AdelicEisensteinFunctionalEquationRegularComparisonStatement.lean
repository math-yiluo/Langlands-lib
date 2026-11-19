import Langlands.Global.AdelicEisensteinFunctionalEquationStatement

/-! # Eisenstein functional equation on a regular parameter patch -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Comparison of the continued `P`-series with a convergent `Q`-series for
the continued intertwining datum on a nonempty open patch. The bound on the
transported regular parameter can be specified in advance. -/
def EisensteinFunctionalEquationRegularComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation q l' a')
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp) (π' : Q ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    LeviSubgroup.IsGeometricUnipotentRadical iV → l' ≫ π' = 𝟙 M' →
    IsWeylConjugation p l q l' w c →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact q K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∀ (EP : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
        (DP : Set (ComplexCharacterParameter F P)),
        (∀ g, IsMeromorphicInCoordinatesOn (fun lam => EP lam g) DP) →
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
          EP lam = hK.eisensteinSeries φ lam) →
      ∀ (k : ℕ) (ψ : Fin k → AdelicGroupPoints F G → ℂ)
        (coeff : Fin k → ComplexCharacterParameter F P → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        (∀ i, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F q iV l')
          (K.comap (ofInfinite F G).toMonoidHom) rho (ψ i)) →
        (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) →
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
          hK.intertwiningOperator hK' iU l iV c π' w φ lam g = ∑ i, coeff i lam * ψ i g) →
      ∀ R : ℝ,
        ∃ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
          (O : Set (Fin n → ℂ)), IsOpen O ∧ O.Nonempty ∧
          ∀ x ∈ O, r'.IsRegularParameter hA' hT' R (weylParameter l c π' (e x)) ∧
            ∀ g : AdelicGroupPoints F G,
              EP (e x) g =
                ∑ i, coeff i (e x) * hK'.eisensteinSeries (ψ i) (weylParameter l c π' (e x)) g

/-- The open-patch comparison supplies the missing analytic input to the
published functional equation. -/
def EisensteinFunctionalEquationRegularComparisonReductionStatement : Prop :=
  EisensteinFunctionalEquationRegularComparisonStatement.{u} →
    EisensteinFunctionalEquationStatement.{u}

end Langlands.Global
