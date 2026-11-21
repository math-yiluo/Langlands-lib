import Langlands.Representation.Archimedean.RealStandardHermitianDual
import Langlands.Representation.Archimedean.RealStandardReplacementInStages

/-! # The compact sesquilinear form for a Hermitian-dual intertwiner -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean InductionStages RealTemperedForm
open Langlands.Global.RankinSelbergGlobal Langlands.Global.RankinSelbergGlobal.RealLocalJacquet
open RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

variable {n : ℕ} {ds : List RealBlock}

private theorem exists_form_of_conjugate_dual_equiv
    (hr : realRank ds = n) (R : SplitFourierReplacement n (ds.flatMap repl) ds)
    (E : KFin n ds ≃ₗ[ℂ] KFin n ((ds.map dualBlock).map realBlockConjExponent))
    (hE : IsRealStandardIntertwiner n
      (realStandardRep n ((ds.map dualBlock).map realBlockConjExponent))
      (realStandardLie n ((ds.map dualBlock).map realBlockConjExponent)) ds E.toLinearMap) :
    ∃ B : KFin n ds →ₗ⋆[ℂ] KFin n ds →ₗ[ℂ] ℂ,
      (∀ v w, B v w = ∫ k : unitaryCompact ℝ n,
        (R.reverse w).val k * conj ((E v).val k) ∂haarK n) ∧
      B ≠ 0 ∧
      (∀ k v w, B (realStandardRep n ds k v) (realStandardRep n ds k w) = B v w) ∧
      ∀ (X : Matrix (Fin n) (Fin n) ℝ) v w,
        B (realStandardLie n ds (1 ⊗ₜ X) v) w +
          B v (realStandardLie n ds (1 ⊗ₜ X) w) = 0 := by
  let es := ds.map dualBlock
  let C := LinearEquiv.ofBijective (realStandardConjugation n es)
    ⟨realStandardConjugation_injective n es, realStandardConjugation_surjective n es⟩
  let H := C.symm.toLinearMap.comp E.toLinearMap
  have hHC (v : KFin n ds) : realStandardConjugation n es (H v) = E v :=
    C.apply_symm_apply (E v)
  have hval (v : KFin n ds) (g : Langlands.GeneralLinear n ℝ) :
      (H v).val g = conj ((E v).val g) := by
    have h := congrArg (fun f => f.val g) (hHC v)
    change conj ((H v).val g) = (E v).val g at h
    rw [← h, Complex.conj_conj]
  have hHK (k : Matrix.unitaryGroup (Fin n) ℝ) (v : KFin n ds) :
      H (realStandardRep n ds k v) = realStandardRep n es k (H v) := by
    apply realStandardConjugation_injective n es
    rw [hHC, realStandardConjugation_compact, hHC]
    exact hE.map_realStandardRep k v
  have hHL (X : Matrix (Fin n) (Fin n) ℝ) (v : KFin n ds) :
      H (realStandardLie n ds (1 ⊗ₜ X) v) = realStandardLie n es (1 ⊗ₜ X) (H v) := by
    apply realStandardConjugation_injective n es
    rw [hHC, realStandardConjugation_lie, hHC]
    exact hE.map_realStandardLie (1 ⊗ₜ X) v
  let Q := (pairing n (ds.flatMap repl) es).comp R.reverse
  obtain ⟨⟨hQK, hQL⟩, hQsep⟩ := realStandardCompactDualPairing n ds hr R.forward
    R.reverse R.slots R.weights R.split R.reverse_compact R.forward_lie R.disjoint R.coefficient
  let B : KFin n ds →ₗ⋆[ℂ] KFin n ds →ₗ[ℂ] ℂ := Q.flip.comp H
  have hB (v w : KFin n ds) : B v w = Q w (H v) := rfl
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro v w
    rw [hB]
    change pairing n (ds.flatMap repl) es (R.reverse w) (H v) = _
    simp only [pairing_apply, hval]
  · let _ := realStandardNontrivial n ds hr
    obtain ⟨v, hv⟩ := exists_ne (0 : KFin n ds)
    have hHv : H v ≠ 0 := fun hz => hv ((C.symm.injective.comp E.injective)
      (show H v = H 0 by rw [hz, map_zero]))
    obtain ⟨w, hw⟩ := hQsep (H v) hHv
    intro hz
    exact hw (show B v w = 0 by rw [hz]; rfl)
  · intro k v w
    simpa only [hB, hHK] using hQK k w (H v)
  · intro X v w
    rw [hB, hB, hHL, add_comm]
    exact hQL X w (H v)

/-- The split lift and an actual Hermitian-dual equivalence provide an
invariant form with the displayed compact integral. -/
def RealStandardCompactHermitianFormStatement : Prop :=
  ∀ {n : ℕ} {ds : List RealBlock}, realRank ds = n →
    ∀ (R : SplitFourierReplacement n (ds.flatMap repl) ds)
      (E : KFin n ds ≃ₗ[ℂ] KFin n (ds.map realHermitianDualBlock)),
      IsRealStandardIntertwiner n (realStandardRep n (ds.map realHermitianDualBlock))
        (realStandardLie n (ds.map realHermitianDualBlock)) ds E.toLinearMap →
      ∃ B : KFin n ds →ₗ⋆[ℂ] KFin n ds →ₗ[ℂ] ℂ,
        (∀ v w, B v w = ∫ k : unitaryCompact ℝ n,
          (R.reverse w).val k * conj ((E v).val k) ∂haarK n) ∧
        B ≠ 0 ∧
        (∀ k v w, B (realStandardRep n ds k v) (realStandardRep n ds k w) = B v w) ∧
        ∀ (X : Matrix (Fin n) (Fin n) ℝ) v w,
          B (realStandardLie n ds (1 ⊗ₜ X) v) w +
            B v (realStandardLie n ds (1 ⊗ₜ X) w) = 0

theorem realStandardCompactHermitianForm : RealStandardCompactHermitianFormStatement := by
  intro n ds
  have he : ds.map realHermitianDualBlock = (ds.map dualBlock).map realBlockConjExponent := by
    rw [List.map_map]
    rfl
  rw [he]
  exact exists_form_of_conjugate_dual_equiv

end Langlands.Archimedean
