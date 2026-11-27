import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction

/-! # Counting rational points in conjugates of compact sets by points of Siegel sets

`SiegelRationalConjugateCountingStatement`: for a point `x` of a Siegel set
`A_G · Ω_N Ω_M A_{T₀}(t) K · Ω` of `G(𝔸)` with torus coordinate `a` and a compact `E ⊆ G(𝔸)`,
the number of points of `G(F)` in `x E x⁻¹` is at most a constant times the modulus
`δ_{P₀}(a) = siegelModulus a = e^{2ρ₀(H₀(a))}`. Through the multiplicity of the quotient map on a
ball `x Y`, it bounds Delorme's `Ξ^{[G]}(x)² = vol_{[G]}(xY)⁻¹` by a multiple of `δ_{P₀}(a)`; since
`e^{2ρ₀(H₀(x))}` is comparable to `δ_{P₀}(a)` up to constants on such a Siegel set, this is a
multiplicity refinement of the upper bound in Delorme 2023, Lemma 2.1 (i). The Library's
`AdelicRationalConjugateCountingAllPointsStatement` bounds the same number by a power of the
height of `x`, at every point `x`. This file states the proposition and does not prove it. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors

/-- **Rational points in conjugates of compact sets by Siegel points** (derived; a multiplicity
refinement of the upper bound in Delorme 2023, Lemma 2.1 (i)). Let `G` be a connected reductive group
over a number field `F`, `(T, i, ν, T₀, j)` an algebraic Siegel setup, `C` compact factors (with
any compact subgroup), `t` a threshold and `Ω ⊆ G(𝔸)` compact. For every compact `E ⊆ G(𝔸)`
there is `B ≥ 0` such that for every point `x` of the Siegel set
`A_G · Ω_N Ω_M A_{T₀}(t) K · Ω` with torus coordinate `a` (`IsSiegelPoint`), the set
`G(F) ∩ x E x⁻¹` is finite and has at most `B · δ_{P₀}(a)` elements, where
`δ_{P₀}(a) = siegelModulus a = ∏_{β > 0} |β(a)|^{m_β}`. -/
def SiegelRationalConjugateCountingStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
      (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j →
    ∀ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
      (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω →
    ∀ E : Set (AdelicGroupPoints F G), IsCompact E →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀)
        (x : AdelicGroupPoints F G), IsSiegelPoint F G T i ν T₀ j C t Ω a x →
          let P := (rationalSubgroup F G : Set (AdelicGroupPoints F G)) ∩
            ((fun y => x * y * x⁻¹) '' E)
          P.Finite ∧ (P.ncard : ℝ) ≤ B * siegelModulus F G T i ν T₀ j a

end Langlands.Global
