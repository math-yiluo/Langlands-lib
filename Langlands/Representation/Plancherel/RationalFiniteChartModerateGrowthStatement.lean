import Langlands.Representation.Exponents.RationalUnrestrictedLatticeBoundStatement
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # Global coefficient growth from supplied finite independent charts -/

noncomputable section

universe u uV uE uI

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open GroupScheme MatrixRepresentation BruhatTits.SpecialCompact
open Aubert.General Aubert.General.RationalPointFamily

/-- Supplied finite independent weakly positive charts and a simultaneous
standard basis imply the coefficientwise global matrix-norm bound. -/
def RationalFiniteChartModerateGrowthStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (ν : cocharacterLattice S) (K0 : Subgroup (rationalPoints G)),
      SimultaneousStandardBasisAt i ν K0 →
      ∀ (E : Type uE) [Fintype E] (I : Type uI) [Fintype I] [DecidableEq I]
        (gen : E → I → cocharacterLattice S),
        (∀ ε, LinearIndependent ℤ (gen ε)) →
        (∀ ε a β, 0 ≤ simpleRootPairing i ν β (gen ε a)) →
        ∀ (S₁ S₂ T : Set (rationalPoints G)),
          IsCompact S₁ → IsCompact S₂ → T.Finite →
          (∀ g : rationalPoints G, ∃ ε : E, ∃ m : I → ℕ,
            ∃ k₁ ∈ S₁, ∃ t ∈ T, ∃ k₂ ∈ S₂,
              g = k₁ * uniformizerPowers i (.ofAdd (∑ a, m a • gen ε a)) * t * k₂) →
          ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
            (ρ : MatrixRepresentation G n), IsClosedSubgroup ρ →
            ∀ (π : SmoothRep.{0, u, uV} ℂ (rationalPoints G)), π.IsAdmissible →
              ∀ (v : π) (φ : SmoothDual π.representation),
                ∃ (d : ℕ) (c : ℝ), 0 < c ∧ ∀ g : rationalPoints G,
                  ‖(φ : Module.Dual ℂ π) (π.representation g v)‖ ≤
                    c * rationalMatrixNorm F ρ g ^ d

end Langlands.Plancherel
