import Langlands.Representation.Plancherel.TranslatedCoefficientValue
import Langlands.Representation.Plancherel.CoefficientTensorFormTransport
import Langlands.Representation.Unitary.Restriction

/-! # Hermitian coefficient forms before and after rational conjugation -/

noncomputable section

universe u uV

open scoped TensorProduct
open Langlands

namespace Langlands.Plancherel.TranslatedCoefficientValue

open Aubert.General Induction HarishChandraSchwartz

variable {H : Type u} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  {M N : Subgroup H} (g : H) (hM : ∀ x : H, x ∈ N ↔ g⁻¹ * x * g ∈ M)
  (A : SmoothRep.{0, u, uV} ℂ M)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Ag" => (conjugationFunctor g hM).obj A
set_option hygiene false in
set_option quotPrecheck false in
local notation "e" => conjugationEquiv g hM

variable (hcof : CompactOpenCofinal M) (hcof' : CompactOpenCofinal N)
  (hA : A.IsAdmissible) (hAg : (Ag).IsAdmissible)
  (b : InvariantPositiveForm A.representation)

set_option hygiene false in
set_option quotPrecheck false in
local notation "bg" => b.comp (e).toMonoidHom
set_option hygiene false in
set_option quotPrecheck false in
local notation "D" => CoefficientConjugation.conjugateDualEquiv g hM A

private theorem smoothDualEquiv_conjugateValue (v : A) :
    (D) (b.smoothDualEquiv hcof hA v) =
      (bg).smoothDualEquiv hcof' hAg v := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rfl

private theorem smoothDualEquiv_symm_conjugateValue (ℓ : SmoothDual A.representation) :
    ((bg).smoothDualEquiv hcof' hAg).symm ((D) ℓ) =
      (b.smoothDualEquiv hcof hA).symm ℓ := by
  apply ((bg).smoothDualEquiv hcof' hAg).injective
  let E := b.smoothDualEquiv hcof hA
  let E' := (bg).smoothDualEquiv hcof' hAg
  have hcomm : (D) (E (E.symm ℓ)) = E' (E.symm ℓ) :=
    smoothDualEquiv_conjugateValue g hM A hcof hcof' hA hAg b _
  exact (E'.apply_symm_apply ((D) ℓ)).trans
    ((congrArg (D) (E.apply_symm_apply ℓ).symm).trans hcomm)

set_option maxHeartbeats 600000 in
/-- The actual coefficient-value conjugation preserves the product Hermitian
form induced from the same positive form viewed on the conjugate Levi. -/
theorem conjugateValue_inner (t s : CoefficientTensor A) :
    (coefficientTensorInvariantForm Ag hcof' hAg bg).inner
        (conjugateValue g hM A t) (conjugateValue g hM A s) =
      (coefficientTensorInvariantForm A hcof hA b).inner t s := by
  have hd (ℓ m : SmoothDual A.representation) :
      (dualInvariantForm bg hcof' hAg).inner ((D) ℓ) ((D) m) =
        (dualInvariantForm b hcof hA).inner ℓ m := by
    change b.inner (((bg).smoothDualEquiv hcof' hAg).symm ((D) m))
      (((bg).smoothDualEquiv hcof' hAg).symm ((D) ℓ)) = _
    exact congrArg₂ b.inner
      (smoothDualEquiv_symm_conjugateValue g hM A hcof hcof' hA hAg b m)
      (smoothDualEquiv_symm_conjugateValue g hM A hcof hcof' hA hAg b ℓ)
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    induction s using TensorProduct.inductionOn with
    | tmul w m =>
      change (coefficientTensorInvariantForm Ag hcof' hAg bg).inner
        (v ⊗ₜ[ℂ] (D) ℓ) (w ⊗ₜ[ℂ] (D) m) = _
      calc
        _ = (bg).inner v w * (dualInvariantForm bg hcof' hAg).inner ((D) ℓ) ((D) m) :=
          coefficientTensorInvariantForm_inner_tmul Ag hcof' hAg bg v w ((D) ℓ) ((D) m)
        _ = b.inner v w * (dualInvariantForm b hcof hA).inner ℓ m :=
          congrArg (fun z : ℂ => b.inner v w * z) (hd ℓ m)
        _ = _ := (coefficientTensorInvariantForm_inner_tmul A hcof hA b v w ℓ m).symm
    | add s s' hs hs' =>
      simp only [map_add, InvariantPositiveForm.add_right, hs, hs']
  | add t t' ht ht' =>
    simp only [map_add, PreInnerProductSpace.Core.add_left, ht, ht']

end Langlands.Plancherel.TranslatedCoefficientValue
