import Langlands.Representation.Archimedean.RealStandardCompactProjection

/-! # Compact projection fixes the correct restrictions on smaller subgroups -/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open GramFormula OrthogonalFinitePolynomial PrincipalSeriesExtension
open RealStandardCompactAverage RealInducedBlockBound RealInducedStandardBound

private abbrev G (n : ℕ) := Langlands.GeneralLinear n ℝ

variable {n : ℕ}

private theorem signFilters_eqOn_subgroup (ds : List RealBlock) (H : Subgroup (G n))
    (hH : ∀ i : Fin n, Unitary.toUnits (signReflection n i) ∈ H)
    (F : C(G n, ℂ))
    (hSign : ∀ (i : Fin n) x, x ∈ H →
      F (Unitary.toUnits (signReflection n i) * x) = realPositionCharacter ds i (-1) * F x)
    (I : List (Fin n)) :
    Set.EqOn (signFilters ds I F) F H := by
  induction I with
  | nil => exact Set.eqOn_refl _ _
  | cons i I ih =>
    intro x hx
    rw [signFilters_cons, signFilter_apply, ih hx, ih (H.mul_mem (hH i) hx), hSign i x hx]
    rcases RealStrictCharacterLanglandsQuotient.realPositionCharacter_neg_one ds i with hc | hc
    all_goals rw [hc]; ring

private theorem highModesList_eqOn_subgroup (H : Subgroup (G n)) (S : List (Slot n))
    {F F' : C(G n, ℂ)} (hEq : Set.EqOn F' F H)
    (hRot : ∀ s ∈ S, ∀ θ, blockRotation n s.p θ ∈ H)
    (hZero : ∀ s ∈ S, ∀ j ∈ lowModes s.M, ∀ x ∈ H,
      blockFourierCoefficient n s.p j F x = 0) :
    Set.EqOn (highModesList S F') F H := by
  induction S with
  | nil => exact hEq
  | cons s S ih =>
    have htail := ih (fun t ht => hRot t (List.mem_cons_of_mem s ht))
      (fun t ht => hZero t (List.mem_cons_of_mem s ht))
    intro x hx
    rw [highModesList_cons, highModes_apply_at, htail hx]
    have hzero' (j : ℤ) (hj : j ∈ lowModes s.M) :
        blockFourierCoefficient n s.p j (highModesList S F') x = 0 := by
      rw [← hZero s List.mem_cons_self j hj x hx]
      unfold blockFourierCoefficient
      exact intervalIntegral.integral_congr fun θ _ => congrArg (fun z : ℂ => z * _)
        (htail (H.mul_mem (hRot s List.mem_cons_self θ) hx))
    rw [Finset.sum_eq_zero hzero', mul_zero, sub_zero]

/-- The standard compact projection fixes the restriction of a polynomial to
a compact subgroup containing the sign and rotation groups if the restriction
already has the required sign and low-mode conditions there. -/
def RealStandardCompactProjectionOnSubgroupStatement : Prop :=
  ∀ {n : ℕ} {ds : List RealBlock} (hr : realRank ds = n)
    (H : Subgroup (Langlands.GeneralLinear n ℝ)),
    H ≤ unitaryCompact ℝ n →
    (∀ i : Fin n, Unitary.toUnits (signReflection n i) ∈ H) →
    (∀ s ∈ slots ds n, ∀ θ, blockRotation n s.p θ ∈ H) →
    ∀ φ : polynomialFunctions n,
      (∀ (i : Fin n) x, x ∈ H →
        extension 0 φ (Unitary.toUnits (signReflection n i) * x) =
          realPositionCharacter ds i (-1) * extension 0 φ x) →
      (∀ s ∈ slots ds n, ∀ j ∈ lowModes s.M, ∀ x ∈ H,
        blockFourierCoefficient n s.p j (extension 0 φ) x = 0) →
      Set.EqOn (compactProjection hr φ).val (extension 0 φ) H

theorem realStandardCompactProjectionOnSubgroup :
    RealStandardCompactProjectionOnSubgroupStatement := by
  intro n ds hr H hH hSignMem hRot φ hSign hZero
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_polynomialFunctions φ.2
  let F : C(G n, ℂ) := ⟨extension 0 φ, (contMDiff_extension 0 hP).continuous⟩
  have hFilter : Set.EqOn (filteredPolynomial ds φ) F H :=
    highModesList_eqOn_subgroup H (slots ds n)
      (signFilters_eqOn_subgroup ds H hSignMem F hSign (List.ofFn id)) hRot hZero
  intro x hx
  have hk := hH hx
  rw [compactProjection_apply ds hr, ← RealReverseTransfer.toUnits_mk hk, extension_unitary]
  rw [RealReverseTransfer.toUnits_mk hk]
  exact hFilter hx

end Langlands.Archimedean
