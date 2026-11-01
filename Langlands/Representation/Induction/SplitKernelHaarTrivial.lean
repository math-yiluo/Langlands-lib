import Langlands.Representation.Induction.SplitKernelEquivariant
import Langlands.HarmonicAnalysis.HaarConjugacy

/-! The actual split-kernel Haar ratio when the inducing subgroup contains the kernel. -/

noncomputable section

namespace Langlands.Induction

open MeasureTheory QuotientIntegration
open scoped NNReal

universe uG uL

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {L : Type uL} [Group L]
variable (r : G →* L) (H : Subgroup G) (hker : r.ker ≤ H)

/-- Removing the redundant inducing-subgroup membership identifies the actual
kernel intersection with the entire kernel, preserving its topology. -/
def splitKernelFullIntersectionEquiv : H.comap r.ker.subtype ≃ₜ* r.ker where
  toFun n := n.val
  invFun n := ⟨n, hker n.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

@[simp] theorem splitKernelFullIntersectionEquiv_apply
    (n : H.comap r.ker.subtype) :
    splitKernelFullIntersectionEquiv r H hker n = n.val := rfl

variable (s : L →* G) (hsH : ∀ l, s l ∈ H)
variable [IsTopologicalGroup G]
variable [LocallyCompactSpace r.ker]
variable [MeasurableSpace r.ker] [BorelSpace r.ker]
variable [MeasurableSpace (H.comap r.ker.subtype)] [BorelSpace (H.comap r.ker.subtype)]
variable (hH : IsClosed (H : Set G))

include hker in
/-- The intersection and kernel conjugations have the same actual Haar scaling
when the inducing subgroup contains the whole kernel. -/
theorem splitKernelHaarRatio_eq_one_of_ker_le :
    splitKernelHaarRatio r s H hsH hH = 1 := by
  apply MonoidHom.ext
  intro l
  apply Units.ext
  let : LocallyCompactSpace (H.comap r.ker.subtype) :=
    (isClosed_splitKernelIntersection r H hH).locallyCompactSpace
  have he := Geometric.haarChar_eq_of_conjugacy
    (splitKernelFullIntersectionEquiv r H hker)
    (splitKernelIntersectionConjugation r s H hsH l)
    (splitKernelConjugation r s l) (fun _ => rfl)
  change mulEquivHaarChar (splitKernelIntersectionConjugation r s H hsH l) /
    mulEquivHaarChar (splitKernelConjugation r s l) = 1
  rw [he, div_self (mulEquivHaarChar_pos _).ne']

end Langlands.Induction
