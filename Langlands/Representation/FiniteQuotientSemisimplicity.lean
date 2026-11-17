import Langlands.Representation.FiniteQuotientProjection
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Algebra.CharP.Invertible

/-! # Semisimplicity from a normal subgroup of invertible finite index -/

noncomputable section

universe uk uG uV

namespace Langlands.FiniteQuotientAveraging

open Representation

variable {k : Type uk} {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V]

section Projection

variable [CommRing k] [Module k V] (ρ : Representation k G V)

/-- Complementary subrepresentations have complementary underlying submodules. -/
theorem isCompl_toSubmodule {U W : Subrepresentation ρ} (h : IsCompl U W) :
    IsCompl U.toSubmodule W.toSubmodule :=
  ⟨disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule h.inf_eq_bot),
    codisjoint_iff.mpr (congrArg Subrepresentation.toSubmodule h.sup_eq_top)⟩

/-- The projection along complementary subrepresentations is equivariant. -/
def projectionOfIsCompl (U W : Subrepresentation ρ) (h : IsCompl U W) :
    IntertwiningMap ρ ρ where
  toLinearMap := U.toSubmodule.projection W.toSubmodule (isCompl_toSubmodule ρ h)
  isIntertwining' g := by
    let P := U.toSubmodule.projection W.toSubmodule (isCompl_toSubmodule ρ h)
    have hid : IsIdempotentElem P :=
      Submodule.isIdempotentElem_projection (isCompl_toSubmodule ρ h)
    have hc : Commute P (ρ g) := (LinearMap.IsIdempotentElem.commute_iff hid).mpr (by
      simp only [P, Submodule.range_projection, Submodule.ker_projection]
      exact ⟨U.apply_mem_toSubmodule g, W.apply_mem_toSubmodule g⟩)
    exact hc.eq

/-- The equivariant projection has the expected image and fixes the first summand. -/
theorem projectionOfIsCompl_isProj (U W : Subrepresentation ρ) (h : IsCompl U W) :
    LinearMap.IsProj U.toSubmodule (projectionOfIsCompl ρ U W h).toLinearMap :=
  ⟨Submodule.projection_apply_mem (isCompl_toSubmodule ρ h),
    fun _ hv => Submodule.projection_apply_of_mem_left (isCompl_toSubmodule ρ h) hv⟩

/-- An equivariant projection gives a complementary subrepresentation via its kernel. -/
theorem isCompl_ker_of_isProj (U : Subrepresentation ρ) (q : IntertwiningMap ρ ρ)
    (hq : LinearMap.IsProj U.toSubmodule q.toLinearMap) :
    IsCompl U q.ker := by
  constructor
  · apply disjoint_iff.mpr
    apply Subrepresentation.toSubmodule_injective
    exact hq.isCompl.inf_eq_bot
  · apply codisjoint_iff.mpr
    apply Subrepresentation.toSubmodule_injective
    exact hq.isCompl.sup_eq_top

end Projection

section Semisimplicity

variable [Field k] [Module k V] (ρ : Representation k G V)
  (N : Subgroup G) [N.Normal]

/-- Semisimplicity extends from a normal subgroup when the quotient is finite
and its order is invertible in the coefficient field. -/
theorem isSemisimpleRepresentation_of_normalRestriction
    [Fintype (G ⧸ N)] [Invertible (Fintype.card (G ⧸ N) : k)]
    (hN : IsSemisimpleRepresentation (ρ.comp N.subtype)) :
    ρ.IsSemisimpleRepresentation := by
  let := hN
  refine ⟨fun U => ?_⟩
  let UN : Subrepresentation (ρ.comp N.subtype) :=
    ⟨U.toSubmodule, fun n => U.apply_mem_toSubmodule n⟩
  obtain ⟨W, hW⟩ := exists_isCompl UN
  let p := projectionOfIsCompl (ρ.comp N.subtype) UN W hW
  let q := intertwinerAverage ρ ρ N p
  have hp : LinearMap.IsProj U.toSubmodule p.toLinearMap :=
    projectionOfIsCompl_isProj (ρ.comp N.subtype) UN W hW
  exact ⟨q.ker, isCompl_ker_of_isProj ρ U q (intertwinerAverage_isProj ρ N U p hp)⟩

/-- In characteristic `p`, a normal subgroup with finite quotient of order prime
to `p` detects semisimplicity in the sufficient direction. -/
theorem isSemisimpleRepresentation_of_primeToNormalQuotient
    [Finite (G ⧸ N)] (p : ℕ) [CharP k p]
    (hcard : ¬ p ∣ Nat.card (G ⧸ N))
    (hN : IsSemisimpleRepresentation (ρ.comp N.subtype)) :
    ρ.IsSemisimpleRepresentation := by
  let := Fintype.ofFinite (G ⧸ N)
  have hcard' : ¬ p ∣ Fintype.card (G ⧸ N) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  let : Invertible (Fintype.card (G ⧸ N) : k) :=
    invertibleOfNonzero ((CharP.cast_eq_zero_iff k p _).not.mpr hcard')
  exact isSemisimpleRepresentation_of_normalRestriction ρ N hN

end Semisimplicity

end Langlands.FiniteQuotientAveraging
