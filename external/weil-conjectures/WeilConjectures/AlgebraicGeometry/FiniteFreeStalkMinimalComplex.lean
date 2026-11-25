/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkUnitCancellation

/-! # Minimal finite free complexes over a scheme stalk

Source: Stacks Project, Tag 00MT, and blueprint lemma-coherent-base-change-invertible-sheaves--3,
proof step 4. (blueprint: lem-pc-finite-free-stalk-minimal-complex)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A bounded finite free complex over a stalk has a minimal homotopy representative.

Source: Stacks Project, Tag 00MT (`lemma-add-trivial-complex`), and blueprint
lemma-coherent-base-change-invertible-sheaves--3, proof step 4.
(blueprint: lem-pc-finite-free-stalk-minimal-complex).

Proof: Choose a finite free rank for each term and use strong induction on the
sum of the chosen ranks in degrees 0 through d. If every residue differential is
zero, take the original complex and its identity homotopy equivalence. Otherwise
apply exists_stalk_unit_cancellation: it removes one basis vector in each of two
adjacent degrees inside the support and preserves all other ranks. Thus no rank
increases and the rank at the source degree strictly decreases, so the finite
rank sum strictly decreases. Apply the induction hypothesis to the complementary
complex, then compose its homotopy equivalence with the cancellation equivalence.
The support bounds, finite freeness and vanishing differentials are inherited
from the induction hypothesis. At rank sum zero the cancellation branch is
impossible because it would give a smaller natural number. No cohomology
hypothesis or preferred remaining rank is used. -/
theorem exists_stalk_minimal_complex {Y : Scheme.{u}} (y : Y)
    (P : CochainComplex (Spec (Y.presheaf.stalk y)).Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free
        (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin s)))) :
    ∃ Q : CochainComplex (Spec (Y.presheaf.stalk y)).Modules ℤ,
      Nonempty (HomotopyEquiv P Q) ∧ Q.IsStrictlyGE 0 ∧ Q.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ s : ℕ, Nonempty
        (Q.X n ≅ SheafOfModules.free
          (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin s)))) ∧
      ∀ a b : ℤ,
        (((Modules.pullback (Spec.map (Y.residue y))).mapHomologicalComplex _).obj
          Q).d a b = 0 := by
  classical
  choose n hn using hfree
  generalize hN : (∑ k ∈ Finset.range (d + 1), n (k : ℤ)) = N
  induction N using Nat.strong_induction_on generalizing P n with
  | h N ih =>
    by_cases hz : ∀ a b : ℤ,
        (((Modules.pullback (Spec.map (Y.residue y))).mapHomologicalComplex _).obj
          P).d a b = 0
    · exact ⟨P, ⟨HomotopyEquiv.refl P⟩, hge, hle, (fun j ↦ ⟨n j, hn j⟩), hz⟩
    · obtain ⟨P', n', i, hi, ⟨e⟩, hge', hle', hn', hni, hni1, hrest⟩ :=
        exists_stalk_unit_cancellation y P d hge hle n hn hz
      have hleRank : ∀ k : ℕ, n' (k : ℤ) ≤ n (k : ℤ) := by
        intro k
        by_cases hk : (k : ℤ) = (i : ℤ)
        · rw [hk]
          omega
        · by_cases hk1 : (k : ℤ) = (i : ℤ) + 1
          · rw [hk1]
            omega
          · rw [hrest (k : ℤ) hk hk1]
      have hlt : (∑ k ∈ Finset.range (d + 1), n' (k : ℤ)) < N := by
        rw [← hN]
        apply Finset.sum_lt_sum
        · intro k _
          exact hleRank k
        · exact ⟨i, Finset.mem_range.mpr (by omega), by omega⟩
      obtain ⟨Q, ⟨e'⟩, hQge, hQle, hQfree, hQzero⟩ :=
        ih _ hlt P' hge' hle' n' hn' rfl
      exact ⟨Q, ⟨e.trans e'⟩, hQge, hQle, hQfree, hQzero⟩

end AlgebraicGeometry.Scheme.Modules
