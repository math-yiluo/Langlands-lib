import Langlands.TraceFormula.GroupSchemeTwistedCuspidalSpectralExpansionStatement
import Langlands.Analysis.HilbertSumTraceProof
import Langlands.Analysis.TraceClassIdealProof

/-!
# Spectral expansion of twisted traces on the cuspidal spectrum: proof

This module proves `GroupSchemeTwistedCuspidalSpectralExpansionStatement`.

* The cuspidal integrated action `R_S(f)` is the compression `p_S ∘ R(f) ∘ ι_S` of the ambient
  integrated action, because `R(f)` restricts to `R_S(f)` on the cuspidal space.
* Part (1) of `Langlands.Analysis.OperatorIdeals.hilbertSumTrace` compresses `R(f)` and
  `R(f) ∘ I_Θ` to the cuspidal space without changing their traces; part (2) expands the traces
  of `R_S(f)` and of the compression `B` of `R(f) ∘ I_Θ` along the supplied Hilbert sum.
* A closed subspace invariant under the right action is invariant under `R_S(f)`, since the
  Bochner integral of a weighted orbit stays in a closed subspace containing the orbit. Hence
  `B` maps each summand `P` into `τ P`, which is the hypothesis of the twisted expansion.
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

/-- The Bochner integral of an integrable function with values in a closed subspace (a
subspace with an orthogonal projection) of a complex Hilbert space lies in that subspace. -/
theorem integral_mem_of_forall_mem {α : Type*} [MeasurableSpace α] {m : Measure α}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] {g : α → E} (hg : Integrable g m)
    (hK : ∀ a, g a ∈ K) : ∫ a, g a ∂m ∈ K := by
  rw [← Submodule.starProjection_eq_self_iff, ← K.starProjection.integral_comp_comm hg]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun a => Submodule.starProjection_eq_self_iff.mpr (hK a))

section Compression

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : Submodule ℂ H) [CompleteSpace S]

omit [CompleteSpace H] in
/-- An operator on `S` whose values agree with those of an operator `R` of `H` on `S` is the
compression of `R` to `S`. -/
theorem eq_compression_of_val (R : H →L[ℂ] H) (RS : S →L[ℂ] S)
    (hval : ∀ φ : S, (RS φ : H) = R φ) :
    RS = S.orthogonalProjectionOnto ∘L R ∘L S.subtypeL := by
  ext1 φ
  change RS φ = S.orthogonalProjectionOnto (R φ)
  rw [← hval, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- Ordinary expansion along a Hilbert sum: if `R` is trace class on `H` with range in `S`
and `RS` is its restriction to `S`, then `RS` is trace class with the trace of `R`, and the
traces of the compressions of `RS` to the summands of any Hilbert sum decomposition of `S`
are absolutely summable with sum `tr R`. -/
theorem compression_hilbertSum_trace (R : H →L[ℂ] H) (RS : S →L[ℂ] S)
    (hval : ∀ φ : S, (RS φ : H) = R φ) (hR : IsTraceClass R) (hrange : ∀ φ, R φ ∈ S) :
    IsTraceClass RS ∧ operatorTrace RS = operatorTrace R ∧
      ∀ (A : Set (Submodule ℂ S)) [∀ P : A, CompleteSpace (P : Submodule ℂ S)],
        IsHilbertSum ℂ (fun P : A => (P : Submodule ℂ S))
          (fun P => (P : Submodule ℂ S).subtypeₗᵢ) →
        let cR : (P : A) → ((P : Submodule ℂ S) →L[ℂ] (P : Submodule ℂ S)) := fun P =>
          (P : Submodule ℂ S).orthogonalProjectionOnto ∘L RS ∘L (P : Submodule ℂ S).subtypeL
        let tR : A → ℂ := fun P => operatorTrace (E := (P : Submodule ℂ S)) (cR P)
        (∀ P : A, IsTraceClass (E := (P : Submodule ℂ S)) (cR P)) ∧
        Summable (fun P : A => ‖tR P‖) ∧ HasSum tR (operatorTrace R) := by
  obtain ⟨hTC, htr⟩ := (hilbertSumTrace.{u, u}).1 H S R hR hrange
  rw [← eq_compression_of_val S R RS hval] at hTC htr
  refine ⟨hTC, htr, ?_⟩
  intro A _ hA
  obtain ⟨hcomp, hsum, hhas, -⟩ :=
    (hilbertSumTrace.{u, u}).2 S A (fun P : A => (P : Submodule ℂ S)) hA RS hTC
  refine ⟨hcomp, hsum, ?_⟩
  rw [← htr]
  exact hhas

/-- Twisted expansion along a Hilbert sum. Let `R` be trace class on `H` with range in `S`, let
`RS` be its restriction to `S` and `I` any bounded operator on `H`. The compression `B` of
`R ∘ I` to `S` is trace class with the trace of `R ∘ I`. Suppose `RS` preserves every closed
subspace of `S` invariant under a family `π` of operators, the summands of a Hilbert sum
decomposition of `S` are `π`-invariant, and `I` maps each summand `P` into `τ P`. Then the
compressions of `B` to the summands are trace class, the norms of their traces are summable,
and their traces summed over the fixed points of `τ` give `tr (R ∘ I)`. -/
theorem twisted_compression_hilbertSum_trace {X : Type*} (π : X → S →L[ℂ] S)
    (R I : H →L[ℂ] H) (RS : S →L[ℂ] S)
    (hval : ∀ φ : S, (RS φ : H) = R φ)
    (hinv : ∀ (P : Submodule ℂ S) [CompleteSpace P],
      (∀ a, ∀ x ∈ P, π a x ∈ P) → ∀ y ∈ P, RS y ∈ P)
    (hR : IsTraceClass R) (hrange : ∀ φ, R φ ∈ S) :
    let B : S →L[ℂ] S := S.orthogonalProjectionOnto ∘L (R ∘L I) ∘L S.subtypeL
    IsTraceClass B ∧ operatorTrace B = operatorTrace (R ∘L I) ∧
      ∀ (A : Set (Submodule ℂ S)) [∀ P : A, CompleteSpace (P : Submodule ℂ S)],
        (∀ P ∈ A, ∀ (a : X), ∀ x ∈ P, π a x ∈ P) →
        IsHilbertSum ℂ (fun P : A => (P : Submodule ℂ S))
          (fun P => (P : Submodule ℂ S).subtypeₗᵢ) →
        ∀ τ : A → A,
          (∀ P : A, ∀ x ∈ (P : Submodule ℂ S),
            ∃ y ∈ ((τ P : A) : Submodule ℂ S), (y : H) = I (x : H)) →
          let cB : (P : A) → ((P : Submodule ℂ S) →L[ℂ] (P : Submodule ℂ S)) := fun P =>
            (P : Submodule ℂ S).orthogonalProjectionOnto ∘L B ∘L (P : Submodule ℂ S).subtypeL
          let tB : A → ℂ := fun P => operatorTrace (E := (P : Submodule ℂ S)) (cB P)
          (∀ P : A, IsTraceClass (E := (P : Submodule ℂ S)) (cB P)) ∧
          Summable (fun P : A => ‖tB P‖) ∧
          HasSum (fun P : {P : A // τ P = P} => tB P.1) (operatorTrace (R ∘L I)) := by
  intro B
  have hTCI : IsTraceClass (R ∘L I) := isTraceClass_precomp R I hR
  obtain ⟨hTCB, htrB⟩ := (hilbertSumTrace.{u, u}).1 H S (R ∘L I) hTCI (fun x => hrange (I x))
  refine ⟨hTCB, htrB, ?_⟩
  intro A _ hπ hA τ hτ
  -- `B` maps each summand `P` into `τ P`.
  have hmaps : ∀ P : A, ∀ x ∈ (P : Submodule ℂ S), B x ∈ ((τ P : A) : Submodule ℂ S) := by
    intro P x hx
    obtain ⟨y, hy, hyx⟩ := hτ P x hx
    have hBx : B x = RS y := by
      rw [eq_compression_of_val S R RS hval]
      change S.orthogonalProjectionOnto (R (I x)) = S.orthogonalProjectionOnto (R y)
      rw [hyx]
    rw [hBx]
    exact hinv (τ P : A) (hπ (τ P : A) (τ P).2) y hy
  obtain ⟨hcomp, hsum, -, hfix⟩ :=
    (hilbertSumTrace.{u, u}).2 S A (fun P : A => (P : Submodule ℂ S)) hA B hTCB
  refine ⟨hcomp, hsum, ?_⟩
  rw [← htrB]
  exact hfix τ hmaps

end Compression

/-- The ordinary and twisted spectral expansions on the full almost-everywhere cuspidal
space. -/
theorem groupSchemeTwistedCuspidalSpectralExpansion :
    GroupSchemeTwistedCuspidalSpectralExpansionStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _ ν f hf S πc Rf RSf hRf hrange
  -- `R_S(f)` is the restriction of `R(f)` to `S`.
  have hval : ∀ φ : S, (RSf φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)) =
      Rf φ :=
    fullAEL2CuspidalIntegratedAction_val F G hPD hG T i hi I e hc ν f hf
  -- `R_S(f)` preserves closed subspaces invariant under the right action.
  have hinv : ∀ (P : Submodule ℂ S) [CompleteSpace P],
      (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, πc a x ∈ P) → ∀ y ∈ P, RSf y ∈ P := by
    intro P _ hP y hy
    change (∫ a, f a • fullAEL2CuspidalRightAction F G hPD hG T i hi I e hc a y ∂ν) ∈ P
    exact integral_mem_of_forall_mem P
      (fullAEL2CuspidalActionIntegrand_integrable F G hPD hG T i hi I e hc ν f hf y)
      (fun a => P.smul_mem (f a) (hP a y hy))
  exact ⟨compression_hilbertSum_trace S Rf RSf hval hRf hrange,
    fun Θ hΘ hΘμ => twisted_compression_hilbertSum_trace S πc Rf
      (twistOperator (positiveRationalSubgroup F G T i) Θ hΘ
        (positiveRationalQuotientHaarMeasure F G T i) hΘμ) RSf hval hinv hRf hrange⟩

end Langlands.TraceFormula
