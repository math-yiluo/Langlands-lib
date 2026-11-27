import Langlands.Global.AdelicEisensteinUnitaryGrowthStatement
import Langlands.Global.AdelicEisensteinUnitaryExponentStatement

/-! # A uniform temperedness criterion on Siegel sets

Mœglin–Waldspurger 1995, Lemma I.4.1, and Delorme 2023, Proposition 3.6 (sufficiency), for a
family of functions with one moderate-growth exponent and constant terms with subunitary
exponents of bounded multiplicity: the family is bounded on Siegel sets by
`δ(b)^{1/2} σ^k`, with `k` independent of the Siegel data and constants independent of the
member of the family. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors

/-- **Uniform temperedness criterion on Siegel sets** (Mœglin–Waldspurger 1995, Lemma I.4.1;
Delorme 2023, Proposition 3.6, the sufficiency of the condition, for families). Let `G` be
connected reductive over a number field, `rho` a closed matrix embedding, and `f x`, `x ∈ S`,
smooth left `G(F)`-invariant functions with uniform moderate growth on `S` with exponent `R`
at an open level `L` (`IsUniformGrowthFamily`). Suppose that for some `m` and every standard
parabolic family `𝓕`, every standard index `J` and every `x ∈ S`, the constant term along
`P_J` of `f x` satisfies subunitary shift equations of order `m` along `𝔄_J`
(`HasSubunitaryShiftEquations`). Then there is `k : ℕ` such that for every algebraic Siegel
setup `(T, i, ν, T₀, j)`, every threshold `t` and every compact `Ω ⊆ G(𝔸)` there is `B` with
`‖f x (z b ω)‖ ≤ B · δ(b)^{1/2} · σ(z b ω)^k` for `x ∈ S`, `z ∈ A_G`, `b` in the weak
simple-root chamber `|β(b)| ≥ t` of `A_{T₀}` and `ω ∈ Ω`. Here `δ = siegelModulus` and
`σ = adelicLogHeight`. -/
def UniformTemperednessCriterionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsClosedSubgroup rho →
      ∀ {Idx : Type} (f : Idx → FinitePlotSmoothRationalFunctions F G) (S : Set Idx)
        (L : Subgroup (FiniteAdelicGroupPoints F G)) (R : ℝ) (m : ℕ),
        IsOpen (L : Set (FiniteAdelicGroupPoints F G)) →
        IsUniformGrowthFamily rho hsmooth hcalc L R f S →
        (∀ (𝓕 : StandardParabolicFamily F G) (J : StandardIndex F G 𝓕.i 𝓕.ν), ∀ x ∈ S,
          𝓕.HasSubunitaryShiftEquations J m (𝓕.constantTerm J (evaluate F G (f x).val))) →
        ∃ k : ℕ, ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
          (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
          (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j →
          ∀ (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω →
            ∃ B : ℝ, ∀ x ∈ S, ∀ z ∈ RestrictionSplitCentre.canonicalSubgroup F G,
              ∀ b ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t, ∀ ω ∈ Ω,
                ‖evaluate F G (f x).val (z * positiveMap F G T i T₀ j b * ω)‖ ≤
                  B * Real.sqrt (siegelModulus F G T i ν T₀ j b) *
                    adelicLogHeight F G rho (z * positiveMap F G T i T₀ j b * ω) ^ k

end Langlands.Global
