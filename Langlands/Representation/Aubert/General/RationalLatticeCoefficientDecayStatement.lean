import Langlands.Representation.Aubert.General.RationalSquareIntegrabilityStatement
import Langlands.Representation.Aubert.General.RationalCartanLatticeModel

/-! # Actual rational lattice coefficients from a simultaneous standard basis -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal BigOperators

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme BruhatTits.SpecialCompact
open Langlands.AlgebraicGeometry.PointTopology

/-- A supplied simultaneous standard basis realizes every geometric premise
of the finite-lattice spectral estimate on actual noncentral uniformizer rays. -/
def RationalLatticeCoefficientDecayStatement : Prop :=
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
        ∃ B : Set (Subgroup (RationalPoint k G.X)),
          CompactOpenNormalBasis K0 B ∧
          ∀ (I : Type w) [Fintype I] [DecidableEq I]
            (J : I → Finset (SimpleRoot i ν)) (x : I → cocharacterLattice T),
            (∀ a β, β ∈ J a → simpleRootPairing i ν β (x a) = 0) →
            (∀ a β, β ∉ J a → 0 < simpleRootPairing i ν β (x a)) →
            (∀ a, ∃ β, β ∉ J a) →
            ∃ z : ∀ a, Subgroup.center (levi i ν (J a)),
              (∀ a, ((z a : levi i ν (J a)) : RationalPoint k G.X) =
                uniformizerPowers i (.ofAdd (x a))) ∧
              ∀ (K : OpenSubgroup (RationalPoint k G.X)), K.toSubgroup ∈ B →
                ∀ (v : fixedVectors A.representation K.toSubgroup)
                  (φ : Module.Dual ℂ A),
                  φ ∈ fixedVectors A.representation.dual K.toSubgroup →
                  ∃ r : I → ℝ, (∀ a, 0 < r a ∧ r a ^ 2 *
                    (((HaarModulus.closedRestrictCharacter (unipotent i ν (J a))
                      (hU (J a)) (levi i ν (J a)) (levi_le_normalizer i ν (J a))
                      (z a : levi i ν (J a)) : ℝ≥0) : ℝ))⁻¹ < 1) ∧
                    ∃ C : ℝ, 0 < C ∧ ∀ n : I → ℕ,
                      ‖φ (A.representation
                        (uniformizerPowers i (.ofAdd (∑ a, n a • x a))) (v : A))‖ ≤
                        C * ∏ a, r a ^ n a

end Langlands.Aubert.General.RationalPointFamily
