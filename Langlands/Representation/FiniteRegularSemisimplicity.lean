import Langlands.Representation.FiniteQuotientSemisimplicity
import Mathlib.RepresentationTheory.Tannaka
import Mathlib.RepresentationTheory.Maschke

/-! # The order obstruction to semisimplicity of a finite regular representation -/

noncomputable section

universe u v w

namespace Langlands.FiniteQuotientAveraging

open Representation

/-- The fixed vectors form a subrepresentation with trivial action. -/
def fixedSubrepresentation {k : Type u} [CommRing k] {G : Type v} [Group G]
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    Subrepresentation ρ where
  toSubmodule := ρ.invariants
  apply_mem_toSubmodule g x hx := by
    change ∀ h, ρ h (ρ g x) = ρ g x
    rw [hx g]
    exact hx

section FiniteRegular

variable (k G : Type u) [Field k] [Group G] [Finite G]

local notation "reg" => TannakaDuality.FiniteGroup.leftRegular (k := k) (G := G)

omit [Finite G] in
private theorem regular_translate_single [DecidableEq G] (g : G) :
    reg g (Pi.single (1 : G) (1 : k)) = Pi.single g (1 : k) := by
  classical
  funext t
  by_cases ht : t = g
  · subst t
    simp [TannakaDuality.FiniteGroup.leftRegular_apply]
  · have hgt : g⁻¹ * t ≠ 1 := by
      intro h
      exact ht (inv_mul_eq_one.mp h).symm
    simp [TannakaDuality.FiniteGroup.leftRegular_apply, ht, hgt]

/-- A finite regular representation can be semisimple only when the group order
is nonzero in the coefficient field. -/
theorem card_ne_zero_of_regular_isSemisimple
    (hss : IsSemisimpleRepresentation reg) : (Nat.card G : k) ≠ 0 := by
  classical
  let := Fintype.ofFinite G
  let := hss
  intro hcard
  let U := fixedSubrepresentation reg
  obtain ⟨W, hW⟩ := exists_isCompl U
  let P := projectionOfIsCompl reg U W hW
  have hP : LinearMap.IsProj U.toSubmodule P.toLinearMap :=
    projectionOfIsCompl_isProj reg U W hW
  have hsingle (g : G) : P (Pi.single g (1 : k)) = P (Pi.single (1 : G) (1 : k)) := by
    rw [← regular_translate_single k G g, P.isIntertwining _ _ g]
    exact hP.1 _ g
  have hones : ∑ g : G, Pi.single g (1 : k) = fun _ : G => (1 : k) := by
    funext t
    simp
  have hone_mem : (fun _ : G => (1 : k)) ∈ U.toSubmodule := by
    intro g
    rfl
  have h := congrArg P hones
  simp only [map_sum, hsingle, Finset.sum_const, Finset.card_univ] at h
  rw [← Nat.cast_smul_eq_nsmul k, ← Nat.card_eq_fintype_card, hcard, zero_smul] at h
  have hfix : P (fun _ : G => (1 : k)) = fun _ : G => (1 : k) :=
    hP.2 _ hone_mem
  rw [hfix] at h
  exact zero_ne_one (congrFun h (1 : G))

/-- Maschke's criterion already follows by testing the finite regular representation. -/
theorem regular_isSemisimple_iff_card_ne_zero :
    IsSemisimpleRepresentation reg ↔ (Nat.card G : k) ≠ 0 := by
  constructor
  · exact card_ne_zero_of_regular_isSemisimple k G
  · intro hcard
    let : NeZero (Nat.card G : k) := ⟨hcard⟩
    infer_instance

/-- In characteristic `p`, the finite regular representation is semisimple exactly
when `p` does not divide the group order. -/
theorem regular_isSemisimple_iff_not_dvd (p : ℕ) [CharP k p] :
    IsSemisimpleRepresentation reg ↔ ¬ p ∣ Nat.card G :=
  (regular_isSemisimple_iff_card_ne_zero k G).trans
    (CharP.cast_eq_zero_iff k p (Nat.card G)).not

end FiniteRegular

end Langlands.FiniteQuotientAveraging
