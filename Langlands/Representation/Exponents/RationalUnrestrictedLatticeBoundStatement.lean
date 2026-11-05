import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.Representation.Plancherel.RationalModerateGrowthStatement

/-! # Unrestricted coefficient growth on rational uniformizer lattices -/

noncomputable section

universe u uV uI

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.Plancherel

open GroupScheme BruhatTits.SpecialCompact Aubert.General Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology

/-- A supplied simultaneous standard compact-open basis bounds all smooth
coefficients on finite weakly dominant uniformizer lattices and their compact
translates. This retains the basis-existence premise. -/
def RationalUnrestrictedLatticeBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (ν : cocharacterLattice T) (K0 : Subgroup (rationalPoints G)),
      SimultaneousStandardBasisAt i ν K0 →
      ∀ (π : SmoothRep.{0, u, uV} ℂ (rationalPoints G)), π.IsAdmissible →
        ∀ (I : Type uI) [Fintype I] [DecidableEq I] (x : I → cocharacterLattice T),
          (∀ a β, 0 ≤ simpleRootPairing i ν β (x a)) →
          ∀ (S₁ S₂ F₀ : Set (rationalPoints G)),
            IsCompact S₁ → IsCompact S₂ → F₀.Finite →
            ∀ (φ : SmoothDual π.representation) (v : π),
              ∃ a : I → ℝ, (∀ j, 0 < a j) ∧
                ∃ C : ℝ, 0 < C ∧ ∀ (n : I → ℕ)
                  (k₁ : rationalPoints G), k₁ ∈ S₁ →
                  ∀ (t : rationalPoints G), t ∈ F₀ →
                  ∀ (k₂ : rationalPoints G), k₂ ∈ S₂ →
                    ‖(φ : Module.Dual ℂ π) (π.representation
                      (k₁ * uniformizerPowers i (.ofAdd (∑ j, n j • x j)) * t * k₂) v)‖ ≤
                      C * ∏ j, a j ^ n j

end Langlands.Plancherel
