import Langlands.Automorphic.GroupSchemeFullAEL2CuspidalDecompositionStatement
import Langlands.Analysis.OperatorIdeals
import Langlands.Global.AdelicLocalFinitenessStatement

/-! # Discrete cuspidal spectrum and trace class of smooth cuspidal convolutions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- The original cuspidal subspace is closed and is an internal Hilbert sum of
irreducible invariant subspaces of finite multiplicity. Every smooth test
convolution acts by a trace-class operator on it. -/
def GroupSchemeFullAEL2CuspidalSpectralStatement : Prop :=
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
    let μQ := positiveRationalQuotientHaarMeasure F G T i
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
    IsClosed (S : Set (Lp ℂ 2 μQ)) ∧
    (∀ (f : C_c(AdelicGroupPoints F G, ℂ)) (hf : Integrable f Measure.haar),
      IsAdelicTestFunction F G f →
        Langlands.Analysis.OperatorIdeals.IsTraceClass
          (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc Measure.haar f hf)) ∧
    ∃ A : Set (Submodule ℂ S),
      (∀ P ∈ A, P ≠ ⊥ ∧ IsClosed (P : Set S) ∧
        (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, πc a x ∈ P) ∧
        ∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
          (∀ (a : AdelicGroupPoints F G), ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) ∧
      IsHilbertSum ℂ (fun P : A => (P.val : Submodule ℂ S)) (fun P => P.val.subtypeₗᵢ) ∧
      ∀ P ∈ A, ∀ hPi : (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, πc a x ∈ P),
        {Q : Submodule ℂ S | Q ∈ A ∧ ∃ U : P ≃ₗᵢ[ℂ] Q,
          ∀ (a : AdelicGroupPoints F G) (x : P), (U ⟨πc a x, hPi a x x.2⟩ : S) = πc a (U x)}.Finite

end Langlands.Automorphic.GroupSchemeFunctions
