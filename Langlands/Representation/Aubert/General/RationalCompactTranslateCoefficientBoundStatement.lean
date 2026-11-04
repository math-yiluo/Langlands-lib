import Langlands.Representation.Aubert.General.RationalSquareIntegrabilityStatement
import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.Representation.Smooth.Contragredient.Definitions

/-! # Actual rational lattice coefficient bounds on compact translates -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal BigOperators

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme BruhatTits.SpecialCompact
open Langlands.AlgebraicGeometry.PointTopology

/-- Strict normalized Jacquet exponents and a simultaneous standard basis give
uniform coefficient bounds on compact translates of every finite ray lattice. -/
def RationalCompactTranslateCoefficientBoundStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hU : ∀ J : Finset (SimpleRoot i ν),
        IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
      (A : SmoothRep.{0, _, max (u + 1) v} ℂ (RationalPoint k G.X)),
      A.IsAdmissible →
      HasStrictNormalizedJacquetExponents i ν
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν) hU A →
      ∀ K0 : Subgroup (RationalPoint k G.X),
        SimultaneousStandardBasisAt i ν K0 →
        ∀ (I : Type w) [Fintype I] [DecidableEq I]
          (J : I → Finset (SimpleRoot i ν)) (x : I → cocharacterLattice T),
          (∀ a β, β ∈ J a → simpleRootPairing i ν β (x a) = 0) →
          (∀ a β, β ∉ J a → 0 < simpleRootPairing i ν β (x a)) →
          (∀ a, ∃ β, β ∉ J a) →
          ∃ z : ∀ a, Subgroup.center (levi i ν (J a)),
            (∀ a, ((z a : levi i ν (J a)) : RationalPoint k G.X) =
              uniformizerPowers i (.ofAdd (x a))) ∧
            ∀ (S₁ S₂ F₀ : Set (RationalPoint k G.X)),
              IsCompact S₁ → IsCompact S₂ → F₀.Finite →
              ∀ (φ : SmoothDual A.representation) (v : A),
                ∃ r : I → ℝ, (∀ a, 0 < r a ∧ r a ^ 2 *
                  (((HaarModulus.closedRestrictCharacter (unipotent i ν (J a))
                    (hU (J a)) (levi i ν (J a)) (levi_le_normalizer i ν (J a))
                    (z a : levi i ν (J a)) : ℝ≥0) : ℝ))⁻¹ < 1) ∧
                  ∃ C : ℝ, 0 < C ∧ ∀ (n : I → ℕ)
                    (k₁ : RationalPoint k G.X), k₁ ∈ S₁ →
                    ∀ (t : RationalPoint k G.X), t ∈ F₀ →
                    ∀ (k₂ : RationalPoint k G.X), k₂ ∈ S₂ →
                      ‖(φ : Module.Dual ℂ A) (A.representation
                        (k₁ * uniformizerPowers i (.ofAdd (∑ a, n a • x a)) * t * k₂) v)‖ ≤
                        C * ∏ a, r a ^ n a

end Langlands.Aubert.General.RationalPointFamily
