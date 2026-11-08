import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # Cuspidal discreteness from compactness of cuspidal convolutions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- If every compactly supported continuous weight integrates the original
right action on the full almost-everywhere cuspidal space to a compact
operator, then that space is a Hilbert sum of irreducible closed invariant
subspaces with finite multiplicities. -/
def GroupSchemeFullAEL2CuspidalDecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
    (∀ (f : C_c(AdelicGroupPoints F G, ℂ)) (hf : Integrable f Measure.haar),
      IsCompactOperator (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc
        Measure.haar f hf)) →
    ∃ A : Set (Submodule ℂ S),
      (∀ P ∈ A, P ≠ ⊥ ∧ IsClosed (P : Set S) ∧
        (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, πc a x ∈ P) ∧
        ∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
          (∀ (a : AdelicGroupPoints F G), ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) ∧
      IsHilbertSum ℂ (fun P : A => (P.1 : Submodule ℂ S)) (fun P => P.1.subtypeₗᵢ) ∧
      ∀ P ∈ A, ∀ hPi : (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, πc a x ∈ P),
        {Q : Submodule ℂ S | Q ∈ A ∧ ∃ U : P ≃ₗᵢ[ℂ] Q,
          ∀ (a : AdelicGroupPoints F G) (x : P), (U ⟨πc a x, hPi a x x.2⟩ : S) = πc a (U x)}.Finite

end Langlands.Automorphic.GroupSchemeFunctions
