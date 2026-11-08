import Langlands.Automorphic.GroupSchemeQuotientL2Integrated
import Langlands.Analysis.OperatorIdeals
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Hilbert–Schmidt convolution and discrete decomposition on a compact actual quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- If the original positive rational quotient is compact, every compactly
supported continuous weight integrates the original right action on its `L²`
to a Hilbert–Schmidt operator, and that `L²` is a Hilbert sum of irreducible
closed invariant subspaces with finite multiplicities. -/
def GroupSchemeCompactQuotientL2DecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
    CompactSpace (PositiveRationalQuotient F G T i) →
    let μG : Measure (AdelicGroupPoints F G) := Measure.haar
    let μQ := positiveRationalQuotientHaarMeasure F G T i
    let π := haarQuotientL2BoundedRightAction F G T i hi I e hc
    (∀ (f : C_c(AdelicGroupPoints F G, ℂ)) (hf : Integrable f μG),
      Langlands.Analysis.OperatorIdeals.IsHilbertSchmidt
        (haarQuotientL2IntegratedAction F G T i hi I e hc μG f hf)) ∧
    ∃ A : Set (Submodule ℂ (Lp ℂ 2 μQ)),
      (∀ P ∈ A, P ≠ ⊥ ∧ IsClosed (P : Set (Lp ℂ 2 μQ)) ∧
        (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, π a x ∈ P) ∧
        ∀ Q : Submodule ℂ (Lp ℂ 2 μQ), Q ≤ P → IsClosed (Q : Set (Lp ℂ 2 μQ)) →
          (∀ (a : AdelicGroupPoints F G), ∀ x ∈ Q, π a x ∈ Q) → Q = ⊥ ∨ Q = P) ∧
      IsHilbertSum ℂ (fun P : A => (P.1 : Submodule ℂ (Lp ℂ 2 μQ)))
        (fun P => P.1.subtypeₗᵢ) ∧
      ∀ P ∈ A, ∀ hPi : (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, π a x ∈ P),
        {Q : Submodule ℂ (Lp ℂ 2 μQ) | Q ∈ A ∧ ∃ U : P ≃ₗᵢ[ℂ] Q,
          ∀ (a : AdelicGroupPoints F G) (x : P),
            (U ⟨π a x, hPi a x x.2⟩ : Lp ℂ 2 μQ) = π a (U x)}.Finite

end Langlands.Automorphic.GroupSchemeFunctions
