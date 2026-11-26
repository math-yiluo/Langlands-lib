import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Langlands.Global.SimpleRootBoxCompact

/-! # Approximation of Eisenstein series by their weak constant terms on cones

Delorme 2023, Lemma 5.3, together with the formula (4.3) for the weak constant term, the
characterization (4.1) of the relative Eisenstein series and Proposition 4.1 for the Levi
subgroups: on a cone of the positive chamber on which the simple roots outside a proper standard
parabolic `Q` are large, the Eisenstein series `E(φ, λ)` of `φ ∈ A^2_P` is approximated up to
`O(δ(a)^{1/2} e^{-ε‖log a‖})`, uniformly for `λ` in a compact subset of `i𝔞_P^*`, by a finite sum
of smooth multiples of functions that transform under the imaginary parameters of `Q` through
the Iwasawa height `H_Q` and are bounded by `δ(a)^{1/2} σ^m`. In Delorme's setting the weak
constant term of `E(φ, λ)` along `Q` is such a sum. The statement asserts the existence of a sum
with these properties; it does not identify the sum with the weak constant term. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors Langlands.Analysis.Meromorphic PositiveRealTorus

/-- **Approximation by the weak constant term on cones** (Delorme 2023, Lemma 5.3 with (4.3),
(4.1) and Proposition 4.1 for the Levi subgroups). Let `P = MU` be a parabolic with presentation
`r`, `K` a maximal compact subgroup with `P(𝔸)K = G(𝔸)`, `rho` a closed matrix embedding and
`φ ∈ A^2_P`. Let `E` be meromorphic in `λ ∈ X^*(P) ⊗ ℂ` at each point `g`, with one domain of
holomorphy `D` containing the imaginary parameters, and equal to the Eisenstein series `E(φ, λ)`
for `Re λ` sufficiently regular. Let `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` be real linear coordinates and
`C ⊆ ℝⁿ` compact. Let `(T, i, ν, T₀, j)` be an algebraic Siegel setup, with `K` also an Iwasawa
subgroup for its standard minimal parabolic, and let `Q = Q_J` be the standard parabolic of a
proper subset `J` of the simple roots `Δ`, with `Q(𝔸)K = G(𝔸)` and Iwasawa height `H_Q`. Let
`δ > 0`, `t` a threshold and `Ω ⊆ G(𝔸)` compact.

Then there are `ε > 0`, `m : ℕ`, `B` and finitely many triples `(c_k, L_k, Φ_k)`, where
`c_k : ℝⁿ → ℂ` is smooth, `L_k` is a real linear surjection from a subspace `V_k ⊆ ℝⁿ` onto
`X^*(Q) ⊗ ℝ` and `Φ_k : ℝⁿ × G(𝔸) → ℂ` is continuous in `x`, such that
* `Φ_k(x + v, g) = m_Q(g)^{i L_k(v)} Φ_k(x, g)` for `v ∈ V_k`, where
  `m_Q(g)^λ = exp ⟨λ, H_Q(g)⟩`;
* `‖Φ_k(x, z b ω)‖ ≤ B δ(b)^{1/2} σ(z b ω)^m` for `x ∈ C`, `z ∈ A_G`, `b` in the weak
  simple-root chamber `|β(b)| ≥ t` of `A_{T₀}` and `ω ∈ Ω`;
* `‖E(i e(x))(z b ω) - ∑_k c_k(x) Φ_k(x, z b ω)‖ ≤ B δ(b)^{1/2} e^{-ε R}` for the same `x`,
  `z`, `b`, `ω` and every `R` with `|log |β(b)|| ≤ R` for all `β ∈ Δ` and
  `δ R ≤ log |α(b)|` for all `α ∈ Δ \ J`.

Here `δ = siegelModulus`, `σ = adelicLogHeight` and `|β(b)|` is the idele norm of `β(b)`. In
Delorme's setting the weak constant term (4.3) supplies such triples: the `Φ_k` are relative
Eisenstein series `E^Q` of a basis of the finite-dimensional space containing the vectors
`M(s, λ) φ`, and the `c_k` are the coefficients of `M(s, λ) φ` in that basis. The conclusion only
asserts the existence of triples with the listed properties. -/
def EisensteinWeakConstantTermApproximationStatement : Prop :=
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
          ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
            (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
            (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j →
            IsIwasawaCompact (Standard.parabolicHom i ν ∅) K →
            ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
              (∃ α ∈ simpleRelativeRoots i ν, α ∉ J) →
              haveI : IsClosedImmersion (Standard.parabolicHom i ν J).hom.hom.left :=
                Standard.isClosedSubgroup_parabolicHom i ν J
              haveI : IsAffineHom (Standard.parabolicScheme i ν J).X.hom :=
                (Standard.isClosedSubgroup_parabolicHom i ν J).isAffineHom
              haveI : IsAffine (Standard.parabolicScheme i ν J).X.left :=
                isAffine_of_isAffineHom (Standard.parabolicScheme i ν J).X.hom
              ∀ (hKQ : IsIwasawaCompact (Standard.parabolicHom i ν J) K) (δ : ℝ), 0 < δ →
              ∀ (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω →
              ∃ (ε : ℝ) (m : ℕ) (B : ℝ) (k : ℕ) (c : Fin k → (Fin n → ℝ) → ℂ)
                (V : Fin k → Submodule ℝ (Fin n → ℝ))
                (L : ∀ q, V q →ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν J))
                (Φ : Fin k → (Fin n → ℝ) → AdelicGroupPoints F G → ℂ),
                0 < ε ∧
                (∀ q, ContDiff ℝ (⊤ : ℕ∞) (c q)) ∧
                (∀ q, Function.Surjective (L q)) ∧
                (∀ q (v : V q) (x : Fin n → ℝ) (g : AdelicGroupPoints F G),
                  Φ q (x + v) g =
                    hKQ.heightPower
                      (imaginaryParameter F (Standard.parabolicScheme i ν J) (L q v)) g *
                      Φ q x g) ∧
                (∀ q (g : AdelicGroupPoints F G), Continuous fun x => Φ q x g) ∧
                (∀ q, ∀ x ∈ C, ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
                  ∀ b ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t, ∀ ω ∈ Ω,
                    ‖Φ q x (z * positiveMap F G T i T₀ j b * ω)‖ ≤
                      B * Real.sqrt (siegelModulus F G T i ν T₀ j b) *
                        adelicLogHeight F G rho (z * positiveMap F G T i T₀ j b * ω) ^ m) ∧
                (∀ x ∈ C, ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
                  ∀ b ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t, ∀ ω ∈ Ω,
                  ∀ R : ℝ,
                    (∀ β ∈ simpleRelativeRoots i ν, |logNormHom F T₀ b.val (j ≫ β)| ≤ R) →
                    (∀ α ∈ simpleRelativeRoots i ν, α ∉ J →
                      δ * R ≤ logNormHom F T₀ b.val (j ≫ α)) →
                    ‖E (imaginaryParameter F P (e x)) (z * positiveMap F G T i T₀ j b * ω) -
                        ∑ q, c q x * Φ q x (z * positiveMap F G T i T₀ j b * ω)‖ ≤
                      B * Real.sqrt (siegelModulus F G T i ν T₀ j b) * Real.exp (-(ε * R)))

end Langlands.Global
