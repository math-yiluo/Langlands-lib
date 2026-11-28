import Langlands.Global.AdelicEisensteinUnitaryExponentStatement
import Langlands.Global.AdelicExponentPolynomials

/-! # Exponent labels of constant terms of Eisenstein series at regular parameters

Lapid 2011, Proposition 4, (12), (13) and Lemma 6, with Delorme 2023, (4.2)–(4.4): for
`φ ∈ A^2_P` and `λ` sufficiently regular, the constant term of the Eisenstein series
`E_P(·, φ, λ)` along a standard parabolic `Q` is a finite sum of functions with polynomial
orbits along the positive split component `𝔄_Q`. Their exponents are affine functions of `λ`,
which are subunitary when `λ` is unitary. The number of terms and the polynomial degrees are
bounded independently of `Q`, of the standard parabolic family and of `λ`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- **Exponent labels of constant terms of Eisenstein series at regular parameters**
(Lapid 2011, Proposition 4, (12), (13) and Lemma 6; Delorme 2023, (4.2)–(4.4)). The data and
hypotheses are those of `EisensteinUnitaryExponentStatement` up to `φ ∈ A^2_P`. Then there are
`b, n : ℕ` such that for every standard parabolic family `𝓕` of `G` and every standard index
`J` there are a real `R`, a number `k ≤ b` of labels and, for `j < k`, a complex linear map
`L j : X^*(P) ⊗ ℂ → X^*(P_J) ⊗ ℂ` and a parameter `c j ∈ X^*(P_J) ⊗ ℂ`, with:

* *subunitarity at unitary parameters*: for every `x ∈ X^*(P) ⊗ ℝ` and every dominant positive
  point `s` of `A_J`, with image `a ∈ 𝔄_J`, `|a^{L j (i x) + c j}| ≤ δ_{P_J}(a)^{1/2}`;
* *expansion at regular parameters*: for every `λ` with `B(Re λ, α) > R` for the roots `α` of
  `A` in the unipotent radical of `P`, the constant term along `P_J` of `E(φ, λ)` is a sum
  `∑_{j < k} f_j` where `a ↦ f_j(a g) a^{-(L j λ + c j)}` is, on `𝔄_J` and for every `g`, a
  polynomial of degree at most `n` in `H_J(a)` (`HasPolynomialOrbit`).

The labels `L j λ + c j` are unnormalized exponents. -/
def EisensteinConstantTermExponentLabelsStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ →
      ∃ b n : ℕ, ∀ (𝓕 : StandardParabolicFamily F G) (J : StandardIndex F G 𝓕.i 𝓕.ν),
        ∃ (R : ℝ) (k : ℕ)
          (L : Fin k → ComplexCharacterParameter F P →ₗ[ℂ] ComplexCharacterParameter F (𝓕.P J))
          (c : Fin k → ComplexCharacterParameter F (𝓕.P J)),
          k ≤ b ∧
          (∀ (j : Fin k) (x : RealCharacterParameter F P)
            (s : PositiveRealTorus.intrinsicSubgroup F (𝓕.A J)), 𝓕.IsDominantSplitPoint J s →
            ‖parameterPower F (𝓕.P J) (L j (imaginaryParameter F P x) + c j)
                (PositiveRealTorus.positivePointMap F (𝓕.P J) (𝓕.A J) (𝓕.a J ≫ 𝓕.l J) s)‖ ≤
              ‖𝓕.halfModulus J
                (PositiveRealTorus.positivePointMap F (𝓕.P J) (𝓕.A J) (𝓕.a J ≫ 𝓕.l J) s)‖) ∧
          ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R lam →
            ∃ f : Fin k → AdelicGroupPoints F G → ℂ,
              (∀ j, 𝓕.HasPolynomialOrbit J (L j lam + c j) n (f j)) ∧
              𝓕.constantTerm J (hK.eisensteinSeries φ lam) = ∑ j, f j

end Langlands.Global
