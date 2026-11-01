import Langlands.AlgebraicGeometry.Modules.PrincipalGenerationOpenLiftStatement
import Langlands.AlgebraicGeometry.Modules.LineBundleSectionClearingProof
import Langlands.AlgebraicGeometry.Modules.PositiveSectionPowerGenerationLocusProof
import Langlands.AlgebraicGeometry.Picard.LineBundleDescent

/-! # Principal generation-open lifting on quasi-compact quasi-separated schemes -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.SchemeModule

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard
open LineBundleDescent

variable {X : Scheme.{u}}

/-- If `q` is a frame on `U` and `a` is `r` times `q` there, the generation open
of `a`, intersected with `U`, is exactly the basic open of `r`. -/
theorem inf_trivializationOpen_eq_basicOpen_of_res_eq_smul
    (N : X.Modules) (q a : GlobalSections N) (U : X.Opens)
    (hq : TrivializesOn N q U) (r : Γ(X, U))
    (ha : N.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a =
      r • N.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op q) :
    U ⊓ trivializationOpen N a = X.basicOpen r := by
  have hres (V : X.Opens) (hV : V ≤ U) :
      N.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op a =
        X.presheaf.map (homOfLE hV).op r •
          N.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op q := by
    rw [← map_map_apply N (show U ≤ ⊤ from le_top) hV, ha,
      Scheme.Modules.map_smul, map_map_apply]
  apply le_antisymm
  · let V := U ⊓ trivializationOpen N a
    have hV : V ≤ U := inf_le_left
    have hqV := (trivializesOn_iff_bijective N q U).mp hq V hV
    have haV := (trivializesOn_iff_bijective N a V).mp
      ((maximalTrivialization X N a V).mpr inf_le_right) V le_rfl
    obtain ⟨d, hd⟩ := haV.2 ((sectionHom N q).app V (1 : Γ(X, V)))
    change Γ(X, V) at d
    let c : Γ(X, V) := X.presheaf.map (homOfLE hV).op r
    have hmul : d * c = 1 := by
      apply hqV.1
      rw [← sectionHom_app_of_eq_smul N q a c (hres V hV)]
      exact hd
    have hc : IsUnit c := IsUnit.of_mul_eq_one_right d hmul
    have hb : X.basicOpen c = V := X.basicOpen_of_isUnit hc
    change V ≤ X.basicOpen r
    rw [show X.basicOpen c = V ⊓ X.basicOpen r from
      Scheme.basicOpen_res X r (homOfLE hV).op] at hb
    exact (inf_eq_left.mp hb)
  · have hB : X.basicOpen r ≤ U := X.basicOpen_le r
    have hqB : TrivializesOn N q (X.basicOpen r) :=
      (maximalTrivialization X N q _).mpr
        (hB.trans ((maximalTrivialization X N q U).mp hq))
    have haB : TrivializesOn N a (X.basicOpen r) :=
      trivializesOn_of_eq_smul N q a hqB
        (X.presheaf.map (homOfLE hB).op r)
        (X.toRingedSpace.isUnit_res_basicOpen r) (hres _ hB)
    exact le_inf hB ((maximalTrivialization X N a _).mp haB)

/-- Every nonnegative power of a section generates on that section's generation open,
including the zeroth power. -/
theorem trivializesOn_sectionPow_generationOpen (M : LineBundle X)
    (s : GlobalSections M.obj) (n : ℕ) :
    TrivializesOn (tensorPow M.obj n) (sectionPow M.obj s n)
      (trivializationOpen M.obj s) := by
  apply (maximalTrivialization X _ _ _).mpr
  cases n with
  | zero => rw [trivializationOpen_sectionPow_zero]; exact le_top
  | succ n => rw [trivializationOpen_sectionPow_succ]

/-- A denominator-cleared section produces the desired principal generation open
after one more tensor multiplication by `s`. -/
theorem principalGenerationOpenLift_of_clearedSection
    (M : LineBundle X) (s : GlobalSections M.obj)
    (r : Γ(X, trivializationOpen M.obj s)) (n : ℕ)
    (a : GlobalSections (tensorPow M.obj n))
    (ha : (tensorPow M.obj n).presheaf.map
        (homOfLE (show trivializationOpen M.obj s ≤ ⊤ from le_top)).op a =
      r • (tensorPow M.obj n).presheaf.map
        (homOfLE (show trivializationOpen M.obj s ≤ ⊤ from le_top)).op
          (sectionPow M.obj s n)) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ t : GlobalSections (tensorPow M.obj k),
      trivializationOpen (tensorPow M.obj k) t = X.basicOpen r := by
  refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n),
    tensorSection M.obj (tensorPow M.obj n) s a, ?_⟩
  change trivializationOpen (tensorObj M.obj (tensorPow M.obj n))
    (tensorSection M.obj (tensorPow M.obj n) s a) = X.basicOpen r
  rw [tensorSectionGenerationLocus X M
    ⟨tensorPow M.obj n, tensorPow_isLocallyFreeRankOne X M n⟩ s a]
  exact inf_trivializationOpen_eq_basicOpen_of_res_eq_smul
    (tensorPow M.obj n) (sectionPow M.obj s n) a (trivializationOpen M.obj s)
    (trivializesOn_sectionPow_generationOpen M s n) r ha

/-- Every principal open of a regular function on the generation open of a line-bundle
section is the whole generation open of a section of some positive tensor power. -/
theorem principalGenerationOpenLift : PrincipalGenerationOpenLiftStatement.{u} := by
  intro X _ _ M s r
  obtain ⟨n, a, ha⟩ := lineBundleSectionClearing X M s r
  exact principalGenerationOpenLift_of_clearedSection M s r n a ha

end Langlands.SchemeModule
