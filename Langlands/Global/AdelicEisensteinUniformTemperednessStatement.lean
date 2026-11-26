import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction

/-! # Uniform temperedness of Eisenstein series on compact sets of unitary parameters

Delorme 2023, Proposition 4.1: for `φ ∈ A^2_P` and `λ` in a compact subset `Λ` of `i𝔞_P^*`,
the Eisenstein series `E_P(·, φ, λ)` is bounded on Siegel sets by `δ(a)^{1/2} σ^m`, with `m`
and the constant independent of `λ ∈ Λ`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors Langlands.Analysis.Meromorphic

/-- **Uniform temperedness of Eisenstein series** (Delorme 2023, Proposition 4.1, for the
functions themselves). Let `P = MU` be a parabolic with presentation `r`, `K` a maximal compact
subgroup with `P(𝔸)K = G(𝔸)`, `rho` a closed matrix embedding and `φ ∈ A^2_P`. Let `E` be
meromorphic in `λ ∈ X^*(P) ⊗ ℂ` at each point `g`, with one domain of holomorphy `D` containing
the imaginary parameters, and equal to the Eisenstein series `E(φ, λ)` for `Re λ` sufficiently
regular. Let `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` be real linear coordinates and `C ⊆ ℝⁿ` compact. Then there
is `m : ℕ` such that for every algebraic Siegel setup `(T, i, ν, T₀, j)`, every threshold `t`
and every compact `Ω ⊆ G(𝔸)` there is `B` with
`‖E(i e(x))(z b ω)‖ ≤ B · δ(b)^{1/2} · σ(z b ω)^m` for `x ∈ C`, `z ∈ A_G`, `b` in the weak
simple-root chamber `|β(b)| ≥ t` of `A_{T₀}` and `ω ∈ Ω`. Here `δ = siegelModulus` and
`σ = adelicLogHeight`. -/
def EisensteinUniformTemperednessStatement : Prop :=
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
          ∃ m : ℕ, ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
            (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
            (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j →
            ∀ (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω →
              ∃ B : ℝ, ∀ x ∈ C, ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
                ∀ b ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t, ∀ ω ∈ Ω,
                  ‖E (imaginaryParameter F P (e x)) (z * positiveMap F G T i T₀ j b * ω)‖ ≤
                    B * Real.sqrt (siegelModulus F G T i ν T₀ j b) *
                      adelicLogHeight F G rho (z * positiveMap F G T i T₀ j b * ω) ^ m

end Langlands.Global
