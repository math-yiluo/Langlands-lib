import Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionAmpleExistenceDescentProof
import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingProof

/-! # Finite affine section covers in one positive degree -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard

/-- A finite, nonempty family of sections of one positive power of `L`, whose
whole generation opens are affine and cover the source. -/
structure FiniteAffinePowerSectionCover {X : Scheme.{u}} (L : LineBundle X) where
  degree : ℕ
  degree_pos : 0 < degree
  dimension : ℕ
  sections : Fin (dimension + 1) → L.powSections degree
  covers : ∀ x : X, ∃ i, x ∈ L.sectionOpen (sections i)
  affine : ∀ i, IsAffineOpen (L.sectionOpen (sections i))

/-- An ample line bundle admits a finite affine section cover in one positive
power. The index family is nonempty even if the scheme is empty. -/
theorem LineBundle.IsAmple.nonempty_finiteAffinePowerSectionCover
    {X : Scheme.{u}} {L : LineBundle X} (hL : L.IsAmple) :
    Nonempty (FiniteAffinePowerSectionCover L) := by
  classical
  let : CompactSpace X := hL.compactSpace
  choose n hn s hx ha using hL.exists_section
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (L.sectionOpen (s x) : Set X))
    (fun x ↦ (L.sectionOpen (s x)).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let d : Option t → ℕ := Option.elim' 1 (fun i ↦ n i)
  let a : ∀ i : Option t, L.powSections (d i) := fun i ↦
    match i with
    | none => 0
    | some j => s j
  have hd : ∀ i, 1 ≤ d i := by
    intro i
    cases i with
    | none => exact le_rfl
    | some j => exact hn j
  have ha' : ∀ i, IsAffineOpen (L.sectionOpen (a i)) := by
    intro i
    cases i with
    | none =>
      change IsAffineOpen (trivializationOpen (tensorPow L.obj 1) 0)
      rw [trivializationOpen_zero
        ⟨tensorPow L.obj 1, tensorPow_isLocallyFreeRankOne X L 1⟩]
      exact isAffineOpen_bot X
    | some j => exact ha j
  obtain ⟨m, hm, b, hb⟩ := exists_common_degree L d hd a
  let e : Option t ≃ Fin (Fintype.card t + 1) :=
    Fintype.equivFinOfCardEq (by simp)
  refine ⟨⟨m, hm, Fintype.card t, fun i ↦ b (e.symm i), ?_, ?_⟩⟩
  · intro x
    have hx' := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨j, hj, hxj⟩ := hx'
    refine ⟨e (some ⟨j, hj⟩), ?_⟩
    rw [Equiv.symm_apply_apply, hb]
    exact hxj
  · intro i
    rw [hb]
    exact ha' _

/-- A chosen finite affine section cover in one positive degree of an ample
line bundle. -/
def LineBundle.IsAmple.finiteAffinePowerSectionCover
    {X : Scheme.{u}} {L : LineBundle X} (hL : L.IsAmple) :
    FiniteAffinePowerSectionCover L :=
  hL.nonempty_finiteAffinePowerSectionCover.some

end Langlands.AlgebraicGeometry.Picard
