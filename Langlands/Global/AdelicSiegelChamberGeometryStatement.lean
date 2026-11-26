import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Langlands.Global.SimpleRootBoxCompact

/-! # Heights on the chambers of an algebraic Siegel setup

Two comparisons between the logarithmic coordinates `log |β(b)|` of a point `b` of the positive
torus `A_{T₀}` and heights at the points `z b ω` (`z ∈ A_G`, `ω` in a compact set):

* on a cone where the simple roots outside a proper subset `J` are large, the Iwasawa height
  `H_Q` of the standard parabolic `Q = Q_J` grows linearly in a fixed direction;
* the logarithmic height `σ(z b ω)` is at most linear in the coordinates `log |β(b)|`
  (`β` simple) and `log ‖χ(z b ω)‖` (`χ` in a finite set of rational characters of `G`). -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

/-- **Growth of the Iwasawa height of a standard parabolic on a cone** (the modulus
`δ_Q(a) = e^{2ρ_Q(H_Q(a))}` and Delorme 2023, §2 and the proof of Lemma 5.2). For an algebraic
Siegel setup `(T, i, ν, T₀, j)` of a connected reductive `G`, a proper subset `J` of the simple
roots `Δ`, the standard parabolic `Q = Q_J` with a compact `K` such that `Q(𝔸)K = G(𝔸)` and
Iwasawa height `H_Q`, `δ > 0`, a threshold `t` and a compact `Ω ⊆ G(𝔸)`, there are
`μ ∈ X^*(Q) ⊗ ℝ`, `c > 0` and `C` with `c R - C ≤ ⟨μ, H_Q(z b ω)⟩` for `z ∈ A_G`, `b` in the
weak simple-root chamber `|β(b)| ≥ t` of `A_{T₀}`, `ω ∈ Ω` and every `R` with
`|log |β(b)|| ≤ R` for all `β ∈ Δ` and `δ R ≤ log |α(b)|` for all `α ∈ Δ \ J`. One can take
`μ = 2ρ_Q = 1 ⊗ det(Ad | Lie Q)`. -/
def StandardParabolicConeHeightStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G))
      (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
      (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j →
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
        ∃ (wt : RealCharacterParameter F (Standard.parabolicScheme i ν J)) (c C : ℝ), 0 < c ∧
          ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
          ∀ b ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t, ∀ ω ∈ Ω,
          ∀ R : ℝ,
            (∀ β ∈ simpleRelativeRoots i ν, |logNormHom F T₀ b.val (j ≫ β)| ≤ R) →
            (∀ α ∈ simpleRelativeRoots i ν, α ∉ J →
              δ * R ≤ logNormHom F T₀ b.val (j ≫ α)) →
            c * R - C ≤ realParameterPairing F (Standard.parabolicScheme i ν J) wt
              (hKQ.height (z * positiveMap F G T i T₀ j b * ω))

/-- **Linear upper bound for the logarithmic height on Siegel chambers** (Delorme 2023, (2.8);
Mœglin–Waldspurger I.2). For an algebraic Siegel setup `(T, i, ν, T₀, j)` of a connected
reductive `G`, a closed matrix embedding `rho` and a compact `Ω ⊆ G(𝔸)`, there are finitely many
rational characters `χ_1, …, χ_r` of `G` and `C` with `σ(z b ω) ≤ C (1 + R)` for `z ∈ A_G`,
`b ∈ A_{T₀}`, `ω ∈ Ω` and every `R ≥ 0` with `|log |β(b)|| ≤ R` for all simple roots `β` and
`|log ‖χ_k(z b ω)‖| ≤ R` for all `k`. Here `σ = adelicLogHeight`, `|β(b)|` is the idele norm of
`β(b)` and `log ‖χ(g)‖` is the logarithm of the idele norm of `χ(g)`. -/
def SiegelChamberHeightComparisonStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ {N : ℕ} (rho : MatrixRepresentation G (Fin N)), IsClosedSubgroup rho →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
      (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j →
      ∀ (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω →
      ∃ (r : ℕ) (χ : Fin r → rationalCharacters G) (C : ℝ),
        ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
        ∀ b : PositiveRealTorus.intrinsicSubgroup F T₀, ∀ ω ∈ Ω, ∀ R : ℝ, 0 ≤ R →
          (∀ β ∈ simpleRelativeRoots i ν, |logNormHom F T₀ b.val (j ≫ β)| ≤ R) →
          (∀ q, |characterLog F G (z * positiveMap F G T i T₀ j b * ω) (χ q)| ≤ R) →
          adelicLogHeight F G rho (z * positiveMap F G T i T₀ j b * ω) ≤ C * (1 + R)

/-- The two comparisons `StandardParabolicConeHeightStatement` and
`SiegelChamberHeightComparisonStatement`. -/
def SiegelChamberGeometryStatement : Prop :=
  StandardParabolicConeHeightStatement ∧ SiegelChamberHeightComparisonStatement

end Langlands.Global
