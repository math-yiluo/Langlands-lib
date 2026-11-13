import Langlands.Global.AdelicSiegelReductionStatement
import Langlands.Global.AdelicRepresentationHeight

/-! # Polynomial norm minimality on actual adelic Siegel products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

/-- Mœglin–Waldspurger I.2.2 (vii) in polynomial form: on every actual weak Siegel product of
an actual algebraic Siegel setup, the full adelic height of a point is bounded by a power of
the height of each of its rational left translates. -/
def SiegelNormMinimalityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {N : ℕ}
    (rho : GroupScheme.MatrixRepresentation G (Fin N)),
    IsConnectedReductive G → IsClosedSubgroup rho → 0 < N →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T)
      (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
      IsSiegelAlgebraicSetup F G T i ν T₀ j →
      ∀ (C : CompactFactors F G
          (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅)) (t : ℝ≥0ˣ),
        ∃ (c : ℝ) (e : ℕ), ∀ s ∈ weakSiegelProduct F G T i ν
            (canonicalStandardFactors F G T i ν) C T₀ j t,
          ∀ q : RationalGroupPoints F G,
            RepresentationGrowth.adelicHeight F G rho s ≤
              c * RepresentationGrowth.adelicHeight F G rho (rational F G q * s) ^ e

end Langlands.Global.AdelicSiegelFactors
