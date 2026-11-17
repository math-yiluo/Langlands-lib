import Langlands.AlgebraicGeometry.Picard.FiniteLocallyFreeDeterminant
import Langlands.AlgebraicGeometry.Modules.AffineBasisFrames

/-! # Clopen rank loci from actual finite local frames -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules} {I : Type u} [Fintype I]
    {T U : X.Opens}

/-- Restrict an actual finite free frame to any smaller open. -/
def subopenFrame
    (e : SheafOfModules.free (R := X.ringCatSheaf.over T) I ≅ M.over T)
    (h : U ≤ T) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U :=
  affineBasisFrame M U I (localSectionBasis e (Over.mk (homOfLE h)))
    (fun W _ => by
      let b : Module.Basis I Γ(X, W.left) Γ(M, W.left) :=
        localSectionBasis e (Over.mk (homOfLE (W.hom.le.trans h)))
      refine ⟨b, fun i => ?_⟩
      exact (localSectionBasis_restrict e
        (Over.homMk W.hom :
          Over.mk (homOfLE (W.hom.le.trans h)) ⟶ Over.mk (homOfLE h)) i).symm)

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard.FiniteLocalFrames

open Langlands.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules} (a : FiniteLocalFrames M)

/-- Two finite free charts meeting at a point have the same rank. -/
theorem rank_eq_of_mem {i j : a.I} {x : X}
    (hi : x ∈ a.opens i) (hj : x ∈ a.opens j) : a.rank i = a.rank j := by
  let W := a.opens i ⊓ a.opens j
  let : Nontrivial Γ(X, W) :=
    (X.presheaf.germ W x ⟨hi, hj⟩).hom.domain_nontrivial
  exact Langlands.LinearAlgebra.FiniteBasisDeterminant.rank_eq
    (VariableDeterminantFrames.basis a.frame i (U := W) inf_le_left)
    (VariableDeterminantFrames.basis a.frame j (U := W) inf_le_right)

/-- The open union of the actual free charts of a specified finite rank. -/
def rankOpen (n : ℕ) : X.Opens :=
  ⨆ i : {i : a.I // a.rank i = n}, a.opens i.val

theorem mem_rankOpen {n : ℕ} {x : X} :
    x ∈ a.rankOpen n ↔ ∃ i : a.I, a.rank i = n ∧ x ∈ a.opens i := by
  simp only [rankOpen, TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.property, hi⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨⟨i, hi⟩, hx⟩

theorem rankOpen_disjoint {n m : ℕ} (hnm : n ≠ m) :
    Disjoint (a.rankOpen n) (a.rankOpen m) := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  obtain ⟨i, hi, hxi⟩ := a.mem_rankOpen.mp hx.1
  obtain ⟨j, hj, hxj⟩ := a.mem_rankOpen.mp hx.2
  exact False.elim (hnm (hi.symm.trans ((a.rank_eq_of_mem hxi hxj).trans hj)))

theorem iSup_rankOpen : (⨆ n, a.rankOpen n) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  have hx : x ∈ ⨆ i, a.opens i := by rw [a.covers]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨a.rank i, a.mem_rankOpen.mpr ⟨i, rfl, hi⟩⟩

/-- The complement of one rank locus is the open union of all the other ranks. -/
theorem rankOpen_compl (n : ℕ) :
    (a.rankOpen n : Set X)ᶜ =
      ((⨆ m : {m : ℕ // m ≠ n}, a.rankOpen m.val : X.Opens) : Set X) := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ ⨆ m, a.rankOpen m := by rw [a.iSup_rankOpen]; trivial
    obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    have hmn : m ≠ n := by
      intro he
      exact hx (he ▸ hm)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨m, hmn⟩, hm⟩
  · intro hx hn
    obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact (a.rankOpen_disjoint m.property).le_bot ⟨hm, hn⟩

theorem rankOpen_isClopen (n : ℕ) : IsClopen (a.rankOpen n : Set X) := by
  refine ⟨isOpen_compl_iff.mp ?_, (a.rankOpen n).isOpen⟩
  rw [a.rankOpen_compl]
  exact TopologicalSpace.Opens.isOpen _

/-- On one rank locus the actual pulled-back module has a constant-rank
frame cover, using only the original charts of that rank. -/
def rankFrames (n : ℕ) :
    FiniteLocalFrames ((Scheme.Modules.pullback (a.rankOpen n).ι).obj M) where
  I := {i : a.I // a.rank i = n}
  opens i := (a.rankOpen n).ι ⁻¹ᵁ a.opens i.val
  covers := by
    apply top_le_iff.mp
    rintro ⟨x, hx⟩ _
    obtain ⟨i, hi, hxi⟩ := a.mem_rankOpen.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩
  rank _ := n
  frame i := by
    have hi : a.rank i.val = n := i.property
    exact eqToIso (congrArg
      (fun k : ℕ => SheafOfModules.free
        (R := (a.rankOpen n).toScheme.ringCatSheaf.over
          ((a.rankOpen n).ι ⁻¹ᵁ a.opens i.val)) (ULift.{u} (Fin k))) hi.symm) ≪≫
      (a.pullback (a.rankOpen n).ι).frame i.val

/-- A constant-rank finite frame cover can be refined by affine actual frames,
with a fixed standard finite index. -/
theorem exists_affineCover_of_rank_eq (n : ℕ) (hn : ∀ i, a.rank i = n) :
    ∃ (J : Type u) (U : J → X.affineOpens),
      (⨆ j, (U j).1) = ⊤ ∧ Nonempty
        (∀ j, SheafOfModules.free (R := X.ringCatSheaf.over (U j).1)
          (ULift.{u} (Fin n)) ≅ M.over (U j).1) := by
  classical
  have hpoint : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ Nonempty
      (SheafOfModules.free (R := X.ringCatSheaf.over U.1) (ULift.{u} (Fin n)) ≅
        M.over U.1) := by
    intro x
    have hx : x ∈ ⨆ i, a.opens i := by rw [a.covers]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨U, hU, hxU, hUi⟩ := exists_isAffineOpen_mem_and_subset hi
    let E : SheafOfModules.free (R := X.ringCatSheaf.over (a.opens i))
        (ULift.{u} (Fin n)) ≅ M.over (a.opens i) := hn i ▸ a.frame i
    exact ⟨⟨U, hU⟩, hxU, ⟨subopenFrame E hUi⟩⟩
  choose U hx e using hpoint
  refine ⟨X, U, ?_, ⟨fun x => (e x).some⟩⟩
  apply top_le_iff.mp
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩

/-- Every clopen rank locus has an affine cover with one fixed frame index for
the actual pulled-back module. -/
theorem exists_affineCover_rankOpen (n : ℕ) :
    ∃ (J : Type u) (U : J → (a.rankOpen n).toScheme.affineOpens),
      (⨆ j, (U j).1) = ⊤ ∧ Nonempty
        (∀ j, SheafOfModules.free (R := (a.rankOpen n).toScheme.ringCatSheaf.over (U j).1)
          (ULift.{u} (Fin n)) ≅
            ((Scheme.Modules.pullback (a.rankOpen n).ι).obj M).over (U j).1) :=
  (a.rankFrames n).exists_affineCover_of_rank_eq n (fun _ => rfl)

end Langlands.AlgebraicGeometry.Picard.FiniteLocalFrames
