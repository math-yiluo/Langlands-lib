import Langlands.Automorphic.GroupSchemeFullAEL2Hilbert
import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Analysis.OperatorIdeals
import Langlands.Analysis.OperatorTrace
import Langlands.TraceFormula.TwistedOrbital
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Spectral expansion of twisted traces on the cuspidal spectrum

The statement expands the trace of an integrated right action with cuspidal image along any
Hilbert sum decomposition of the cuspidal space. The twisted expansion uses right-invariant
summands and an assignment `τ` with the twisted image of `P` contained in `τ P`. Its
sum runs over the fixed points of `τ`. This is derived from the spectral sides in Getz–Hahn
(2024), Theorem 18.2.5 and Corollaries 18.4.1 and 18.5.1, and relates to the spectral comparison
in Henniart–Lemaire (2011), II.6.6. See
`GroupSchemeTwistedCuspidalSpectralExpansionStatement.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals Langlands.QuotientIntegration

namespace Langlands.TraceFormula

/-- Spectral expansion of traces and twisted traces of integrated right actions with
cuspidal image, along any Hilbert sum decomposition of the full almost-everywhere cuspidal
space into complete subspaces. The cuspidal integrated action is trace class and has the
ambient trace. For a compatible automorphism, the compression of the twisted action to the
cuspidal space is trace class and has the ambient twisted trace. In either case each summand
compression is trace class and the norms of the traces are summable. The twisted sum assumes
right invariance and containment of the twisted image of each summand `P` in `τ P`, and
uses the terms with `τ P = P`. -/
def GroupSchemeTwistedCuspidalSpectralExpansionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (ν : Measure (AdelicGroupPoints F G)) (f : AdelicGroupPoints F G → ℂ)
    (hf : Integrable f ν),
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
    let Rf := haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf
    let RSf := fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν f hf
    IsTraceClass Rf → (∀ φ, Rf φ ∈ S) →
      (IsTraceClass RSf ∧ operatorTrace RSf = operatorTrace Rf ∧
        ∀ (A : Set (Submodule ℂ S)) [∀ P : A, CompleteSpace (P : Submodule ℂ S)],
          IsHilbertSum ℂ (fun P : A => (P : Submodule ℂ S))
            (fun P => (P : Submodule ℂ S).subtypeₗᵢ) →
          let cR : (P : A) → ((P : Submodule ℂ S) →L[ℂ] (P : Submodule ℂ S)) := fun P =>
            (P : Submodule ℂ S).orthogonalProjectionOnto ∘L RSf ∘L (P : Submodule ℂ S).subtypeL
          let tR : A → ℂ := fun P => operatorTrace (E := (P : Submodule ℂ S)) (cR P)
          (∀ P : A, IsTraceClass (E := (P : Submodule ℂ S)) (cR P)) ∧
          Summable (fun P : A => ‖tR P‖) ∧ HasSum tR (operatorTrace Rf)) ∧
      ∀ (Θ : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G)
        (hΘ : ∀ x, Θ x ∈ positiveRationalSubgroup F G T i ↔ x ∈ positiveRationalSubgroup F G T i)
        (hΘμ : MeasurePreserving
          (quotientAutomorphism (positiveRationalSubgroup F G T i) Θ hΘ).symm
          (positiveRationalQuotientHaarMeasure F G T i)
          (positiveRationalQuotientHaarMeasure F G T i)),
        let IΘ := twistOperator (positiveRationalSubgroup F G T i) Θ hΘ
          (positiveRationalQuotientHaarMeasure F G T i) hΘμ
        let B : S →L[ℂ] S := S.orthogonalProjectionOnto ∘L (Rf ∘L IΘ) ∘L S.subtypeL
        IsTraceClass B ∧ operatorTrace B = operatorTrace (Rf ∘L IΘ) ∧
          ∀ (A : Set (Submodule ℂ S)) [∀ P : A, CompleteSpace (P : Submodule ℂ S)],
            (∀ P ∈ A, ∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, πc a x ∈ P) →
            IsHilbertSum ℂ (fun P : A => (P : Submodule ℂ S))
              (fun P => (P : Submodule ℂ S).subtypeₗᵢ) →
            ∀ τ : A → A,
              (∀ P : A, ∀ x ∈ (P : Submodule ℂ S),
                ∃ y ∈ ((τ P : A) : Submodule ℂ S),
                  (y : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)) =
                    IΘ (x : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i))) →
              let cB : (P : A) → ((P : Submodule ℂ S) →L[ℂ] (P : Submodule ℂ S)) := fun P =>
                (P : Submodule ℂ S).orthogonalProjectionOnto ∘L B ∘L (P : Submodule ℂ S).subtypeL
              let tB : A → ℂ := fun P => operatorTrace (E := (P : Submodule ℂ S)) (cB P)
              (∀ P : A, IsTraceClass (E := (P : Submodule ℂ S)) (cB P)) ∧
              Summable (fun P : A => ‖tB P‖) ∧
              HasSum (fun P : {P : A // τ P = P} => tB P.1) (operatorTrace (Rf ∘L IΘ))

end Langlands.TraceFormula
