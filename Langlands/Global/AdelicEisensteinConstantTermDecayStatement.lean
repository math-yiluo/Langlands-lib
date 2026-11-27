import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Langlands.Global.SimpleRootBoxCompact
import Langlands.Global.AdelicEisensteinConstantTermStatement

/-! # Decay of Eisenstein series minus their constant term along a standard parabolic

Delorme 2023, Lemma 3.1 (the variant of Mœglin–Waldspurger, Lemma I.2.10, for a standard
parabolic `Q`, with `β_Q = inf_{α ∈ Δ_0 \ Δ_0^Q} α` in place of the omitted simple root),
applied to the Eisenstein series `E(φ, λ)` uniformly for `λ` in a compact subset of `i𝔞_P^*`,
with the bounds of Proposition 4.1 as input. This is the bound for `|E − E_Q|` in the analogue
of Lemma 5.1 for Eisenstein series that proves Lemma 5.3: on a Siegel set of `G(𝔸)`, the
difference between `E(φ, λ)` and its constant term along `Q` is bounded by a fixed polynomial
in `‖H_0(b)‖` times `δ(b)^{1/2}` times every power of `e^{-β_Q(H_0(b))}`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors Langlands.Analysis.Meromorphic PositiveRealTorus

/-- **Eisenstein series minus their constant term along a standard parabolic** (Delorme 2023,
Lemma 3.1 applied to `E(φ, λ)`, as in the proofs of Lemmas 5.1 and 5.3). Let `P = MU` be a parabolic
with presentation `r`, `K` a maximal compact subgroup with `P(𝔸)K = G(𝔸)`, `rho` a closed matrix
embedding and `φ ∈ A^2_P`. Let `E` be meromorphic in `λ ∈ X^*(P) ⊗ ℂ` at each point `g`, with one
domain of holomorphy `D` containing the imaginary parameters, and equal to the Eisenstein series
`E(φ, λ)` for `Re λ` sufficiently regular. Let `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` be real linear coordinates
and `C ⊆ ℝⁿ` compact. Let `(T, i, ν, T₀, j)` be an algebraic Siegel setup, with `K` also an
Iwasawa subgroup for its standard minimal parabolic, and let `J` be a proper subset of the simple
roots `Δ`, with standard parabolic `Q = Q_J`, unipotent radical `N_Q` and constant term
`E_Q(g) = ∫_{N_Q(F) \ N_Q(𝔸)} E(u g) du` (`subgroupConstantTerm`).

Then there is `m : ℕ` such that for every threshold `t`, every compact `Ω ⊆ G(𝔸)` and every
`k : ℕ` there is `B` with
`‖E(i e(x))(z b ω) - E(i e(x))_Q(z b ω)‖ ≤ B δ(b)^{1/2} (1 + R)^m e^{-k s}`
for `x ∈ C`, `z ∈ A_G`, `b` in the weak simple-root chamber `|β(b)| ≥ t` of `A_{T₀}`, `ω ∈ Ω`
and all real `R`, `s` with `|log |β(b)|| ≤ R` for every `β ∈ Δ` and `s ≤ log |α(b)|` for every
`α ∈ Δ \ J`.

Here `δ = siegelModulus` and `|β(b)|` is the idele norm of `β(b)`. With the best choices of `R`
and `s` the right side is `B δ(b)^{1/2} (1 + max_β |log |β(b)||)^m e^{-k min_{α ∉ J} log |α(b)|}`,
which is Delorme's bound `(1 + ‖X‖)^m e^{ρ(X) - k β_Q(X)}` at `X = H_0(b)`, up to the
normalization of the idele norm. -/
def EisensteinConstantTermDecayStatement : Prop :=
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
              haveI : IsClosedImmersion (Standard.unipotentHom i ν J).hom.hom.left :=
                Standard.isClosedSubgroup_unipotentHom i ν J
              haveI : IsAffineHom (Standard.unipotentScheme i ν J).X.hom :=
                (Standard.isClosedSubgroup_unipotentHom i ν J).isAffineHom
              haveI : IsAffine (Standard.unipotentScheme i ν J).X.left :=
                isAffine_of_isAffineHom (Standard.unipotentScheme i ν J).X.hom
              ∃ m : ℕ, ∀ (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω →
                ∀ k : ℕ, ∃ B : ℝ,
                  ∀ x ∈ C, ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
                  ∀ b ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t, ∀ ω ∈ Ω,
                  ∀ R s : ℝ,
                    (∀ β ∈ simpleRelativeRoots i ν, |logNormHom F T₀ b.val (j ≫ β)| ≤ R) →
                    (∀ α ∈ simpleRelativeRoots i ν, α ∉ J →
                      s ≤ logNormHom F T₀ b.val (j ≫ α)) →
                    ‖E (imaginaryParameter F P (e x)) (z * positiveMap F G T i T₀ j b * ω) -
                        subgroupConstantTerm F (Standard.unipotentHom i ν J)
                          (E (imaginaryParameter F P (e x)))
                          (z * positiveMap F G T i T₀ j b * ω)‖ ≤
                      B * Real.sqrt (siegelModulus F G T i ν T₀ j b) * (1 + R) ^ m *
                        Real.exp (-(k * s))

end Langlands.Global
