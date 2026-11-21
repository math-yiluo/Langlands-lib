import Langlands.Representation.Archimedean.RealStandardUnitarityDescent
import Langlands.Representation.Archimedean.RealStandardIrreducibilityInStages

/-! # Infinitesimal unitarity of consecutive Hermitian factors -/

noncomputable section

open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean InductionStages

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual standard module is equivalent to the actual module of its
Hermitian-dual blocks, with both intertwining identities. -/
def HasRealStandardHermitianDualEquiv (ds : List RealBlock) : Prop :=
  let n := realRank ds
  let es := ds.map realHermitianDualBlock
  ∃ E : KFin n ds ≃ₗ[ℂ] KFin n es,
    IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds E.toLinearMap

theorem HasRealStandardHermitianDualEquiv.append {A B : List RealBlock}
    (hA : HasRealStandardHermitianDualEquiv A) (hB : HasRealStandardHermitianDualEquiv B) :
    HasRealStandardHermitianDualEquiv (A ++ B) := by
  obtain ⟨L, hL⟩ := hA
  obtain ⟨R, hR⟩ := hB
  let s : Fin 2 → ℕ := ![realRank A, realRank B]
  obtain ⟨E, hE, -, -⟩ := realTwoBlockEquiv s rfl (realRank_map_hermitianDual A)
    rfl (realRank_map_hermitianDual B) L R hL hR
  let P (n : ℕ) (es : List RealBlock) : Prop :=
    ∃ I : KFin n (A ++ B) ≃ₗ[ℂ] KFin n es,
      IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) (A ++ B)
        I.toLinearMap
  have hn : realRank (A ++ B) = ∑ i, s i := by
    rw [realRank_append', Fin.sum_univ_two]
    rfl
  change P (realRank (A ++ B)) ((A ++ B).map realHermitianDualBlock)
  rw [hn, List.map_append]
  exact ⟨E, hE⟩

private theorem hermitianDualEquiv_flatten (groups : List (List RealBlock))
    (h : ∀ x ∈ groups, HasRealStandardHermitianDualEquiv x) :
    HasRealStandardHermitianDualEquiv groups.flatten := by
  induction groups with
  | nil =>
    refine ⟨LinearEquiv.refl ℂ _, isRealStandardIntertwiner_iff.mpr ⟨?_, ?_⟩⟩
    · intro k f
      rfl
    · intro X f
      rfl
  | cons A groups ih =>
    exact (h A List.mem_cons_self).append (ih fun B hB => h B (List.mem_cons_of_mem A hB))

/-- A finite consecutive grouping into Hermitian factors inherits
infinitesimal unitarity from the irreducible ambient standard module. -/
def RealStandardFactorUnitarityStatement : Prop :=
  ∀ (groups : List (List RealBlock)) (n : ℕ), realRank groups.flatten = n →
    (∀ A ∈ groups, HasRealStandardHermitianDualEquiv A) →
    IsIrreducibleGKModule (realStandardRep n groups.flatten) (realStandardLie n groups.flatten) →
    IsRealUnitarizableGKModule n (realStandardRep n groups.flatten)
      (realStandardLie n groups.flatten) →
    ∀ A ∈ groups, IsRealUnitarizableGKModule (realRank A) (realStandardRep (realRank A) A)
      (realStandardLie (realRank A) A)

theorem realStandardFactorUnitarity : RealStandardFactorUnitarityStatement := by
  intro groups
  induction groups with
  | nil =>
    intro n hn hE hI hU A hA
    exact (List.not_mem_nil hA).elim
  | cons A groups ih =>
    intro n hn hE hI hU
    let B := groups.flatten
    have hAB : realRank (A ++ B) = n := hn
    have hTail (C : List RealBlock) (hC : C ∈ groups) : HasRealStandardHermitianDualEquiv C :=
      hE C (List.mem_cons_of_mem A hC)
    obtain ⟨L, hL⟩ := hE A List.mem_cons_self
    obtain ⟨R, hR⟩ := hermitianDualEquiv_flatten groups hTail
    have hI₀ := realStandardIrreducibilityInStages n [] A B hAB hI
    let Irred (ds : List RealBlock) : Prop :=
      IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds)
    have hI' : Irred (A ++ B ++ []) := by
      rw [List.append_nil]
      exact hI
    have hI₁ := realStandardIrreducibilityInStages n A B []
      (by simpa only [List.append_nil] using hAB) hI'
    have hsum : realRank A + realRank B = n := (realRank_append' A B).symm.trans hAB
    obtain ⟨hU₀, hU₁⟩ := realStandardUnitarityDescent A B n hsum L R hL hR hI₀ hI₁ hI hU
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · exact hU₀
    · exact ih (realRank B) rfl hTail hI₁ hU₁ C hC

end Langlands.Archimedean
