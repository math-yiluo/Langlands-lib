import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.AdelicLogSection
import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Subunitary exponents of constant terms of Eisenstein series at unitary parameters

Lapid 2011, Proposition 4, (13) and Lemma 6, with Delorme 2023, (4.2)–(4.4): for `φ ∈ A^2_P`
and `λ ∈ i𝔞_P^*`, the exponents of the constant term of the continued Eisenstein series
`E_P(·, φ, λ)` along every standard parabolic `Q` are subunitary, and their number, counted
with multiplicity, is bounded independently of `λ` in a compact set and of `Q`. The statement
expresses this through the difference equations that the exponents impose along the dominant
points of the positive split component `𝔄_Q`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

namespace StandardParabolicFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

/-- A positive real point `s` of the split component `A_J` is **dominant** when every simple
root `α ∉ J` satisfies `|α(s)| ≥ 1`. Here `α(s)` is the value at `s` of the restriction of `α`
along `A_J → T`, and `|·|` is the idele norm. -/
def IsDominantSplitPoint (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (s : PositiveRealTorus.intrinsicSubgroup F (𝓕.A J)) : Prop :=
  ∀ α ∈ simpleRelativeRoots 𝓕.i 𝓕.ν, α ∉ J.1 →
    1 ≤ PositiveRealTorus.normCharacter F (𝓕.A J) (𝓕.f J ≫ α) s

/-- `φ` **satisfies subunitary shift equations of order `m` along `𝔄_J`**: for every dominant
positive point `s` of `A_J`, with image `a ∈ 𝔄_J ⊆ P_J(𝔸)`, there are `w_0, …, w_{m-1} ∈ ℂ`
with `|w_k| ≤ δ_{P_J}(a)^{1/2}` such that left translation by `a` satisfies
`∏_k (L_a - w_k) φ = 0`, that is `∑_k c_k φ(a^k g) = 0` for every `g`, where
`∏_k (X - w_k) = ∑_k c_k X^k`.

If `φ = ∑_μ φ_μ` is a finite sum of functions with normalized exponents `μ` along `𝔄_J` whose
polynomial parts have degrees `d_μ`, with `∑_μ (d_μ + 1) ≤ m`, and every `μ` is subunitary, then
`φ` satisfies these equations: the roots are `a^{μ + ρ_J}`, each repeated `d_μ + 1` times, and
`|a^{μ + ρ_J}| = |a^μ| δ_{P_J}(a)^{1/2}` with `|a^μ| ≤ 1` for dominant `a`. -/
def HasSubunitaryShiftEquations (J : StandardIndex F G 𝓕.i 𝓕.ν) (m : ℕ)
    (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ s : PositiveRealTorus.intrinsicSubgroup F (𝓕.A J), 𝓕.IsDominantSplitPoint J s →
    ∃ w : Fin m → ℂ,
      (∀ k, ‖w k‖ ≤
        ‖𝓕.halfModulus J (PositiveRealTorus.positivePointMap F (𝓕.P J) (𝓕.A J)
          (𝓕.a J ≫ 𝓕.l J) s)‖) ∧
      IsTranslationPolynomialSolution
        (map F (𝓕.P J) G (𝓕.p J)
          (PositiveRealTorus.positivePointMap F (𝓕.P J) (𝓕.A J) (𝓕.a J ≫ 𝓕.l J) s))
        (∏ k, (Polynomial.X - Polynomial.C (w k))) φ

end StandardParabolicFamily

/-- **Subunitary exponents of constant terms of Eisenstein series at unitary parameters**
(Lapid 2011, Proposition 4, (13) and Lemma 6; Delorme 2023, (4.2)–(4.4)). The data and
hypotheses are those of `EisensteinUniformTemperednessStatement`. Let `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` be
real linear coordinates and `C ⊆ ℝⁿ` compact. Then there is `m : ℕ` such that for every
standard parabolic family `𝓕` of `G`, every standard index `J` and every `x ∈ C`, the constant
term along `P_J` of `E(i e(x))` satisfies subunitary shift equations of order `m` along `𝔄_J`
(`HasSubunitaryShiftEquations`). -/
def EisensteinUnitaryExponentStatement : Prop :=
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
      ∀ (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        Set.range (imaginaryParameter F P) ⊆ D →
        (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
          E lam = hK.eisensteinSeries φ lam) →
        ∀ (n : ℕ) (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (C : Set (Fin n → ℝ)),
          IsCompact C →
          ∃ m : ℕ, ∀ (𝓕 : StandardParabolicFamily F G) (J : StandardIndex F G 𝓕.i 𝓕.ν),
            ∀ x ∈ C, 𝓕.HasSubunitaryShiftEquations J m
              (𝓕.constantTerm J (E (imaginaryParameter F P (e x))))

end Langlands.Global
