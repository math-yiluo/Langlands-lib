import Langlands.Representation.Archimedean.ComplexLinkedLanglandsQuotientNotLargeProof
import Langlands.Representation.Archimedean.ComplexStandardIrreducibleCriterionProof
import Langlands.Representation.Archimedean.ComplexStandardPermutationProof
import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof
import Langlands.Representation.Archimedean.ComplexTemperedSortedReduction

/-! # The irreducibility criterion in arbitrary order and its descent to sublists -/

noncomputable section

open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean
open ComplexLinkedLanglandsQuotientDuality (tr bilin_envelopingAction pairing_lie)

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem unlinked_of_ordered_irreducible {n : ℕ} {ds : List ComplexCharacterData}
    (hlen : ds.length = n) (hord : IsComplexLanglandsOrdered ds)
    (hirr : IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds)) :
    IsComplexUnlinked ds := by
  by_contra hlink
  let ds' := ds.map complexCharacterDataInv
  have hχ (i : ℕ) (z : ℂˣ) : complexPositionCharacter ds i z * complexPositionCharacter ds' i z = 1 := by
    rw [mul_comm]
    exact complexPositionCharacter_map_inv_mul ds i z
  obtain ⟨Q, hQK, hQX, hQnd⟩ := complexStandardDuality n ds ds' hχ
  obtain ⟨S, hSgk, hS₀, u, huS, hu₀⟩ := complexDualSubmoduleAnnihilator_of_growth
    HolomorphicGrowth.complexStandardHolomorphicGrowth
    (complexLinkedSmallGrowthReduction (complexStandardUnlinkedSwapReduction complexGLTwoUnlinkedIrreducible))
    n ds ds' hlen hord hlink hχ
  let V := kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)
  let W : Submodule ℂ V :=
    { carrier := {f | ∀ s ∈ S, Q f s = 0}
      add_mem' := fun {f f'} hf hf' s hs => by rw [map_add, LinearMap.add_apply, hf s hs, hf' s hs, add_zero]
      zero_mem' := fun s _ => by rw [map_zero, LinearMap.zero_apply]
      smul_mem' := fun c f hf s hs => by rw [map_smul, LinearMap.smul_apply, hf s hs, smul_zero] }
  have hW : IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) W := by
    refine ⟨fun k f hf s hs => ?_, fun X f hf s hs => ?_⟩
    · have hs' : complexStandardRep n ds' k⁻¹ s ∈ S := hSgk.1 k⁻¹ s hs
      have he := hQK ⟨Unitary.toUnits k, k.2⟩ f (complexStandardRep n ds' k⁻¹ s)
        (complexStandardRep n ds k f).2 (complexStandardRep n ds' k (complexStandardRep n ds' k⁻¹ s)).2
      have hComp : complexStandardRep n ds' k (complexStandardRep n ds' k⁻¹ s) = s := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      change Q (complexStandardRep n ds k f) (complexStandardRep n ds' k (complexStandardRep n ds' k⁻¹ s)) = _ at he
      rw [hComp] at he
      exact he.trans (hf _ hs')
    · have h := pairing_lie Q hQX X f s
      rw [hf _ (hSgk.2 X s hs), add_zero] at h
      exact h
  have hProper : W ≠ ⊤ := by
    obtain ⟨s, hs, hs₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS₀
    obtain ⟨f, hf⟩ := hQnd s hs₀
    intro h
    have hfW : f ∈ W := h ▸ Submodule.mem_top
    exact hf (hfW s hs)
  have hBot := (hirr.2 W hW.1 hW.2).resolve_right hProper
  have hTranspose (f : V) (s : kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n)) :=
    bilin_envelopingAction (complexStandardLie n ds) (complexStandardLie n ds') Q
      (fun X f h => pairing_lie Q hQX X f h) u f s
  have hZero (f : V) : envelopingAction (complexStandardLie n ds) (tr u) f = 0 := by
    have h : envelopingAction (complexStandardLie n ds) (tr u) f ∈ W := by
      intro s hs
      rw [← hTranspose f s, huS s hs, map_zero]
    exact (Submodule.mem_bot ℂ).mp (hBot ▸ h)
  apply hu₀
  refine LinearMap.ext fun s => ?_
  rw [LinearMap.zero_apply]
  by_contra hne
  obtain ⟨f, hf⟩ := hQnd _ hne
  exact hf (by rw [hTranspose f s, hZero, map_zero, LinearMap.zero_apply])

/-- Pairwise unlinkage is invariant under reordering the inducing list. -/
theorem isComplexUnlinked_perm {ds es : List ComplexCharacterData} (h : ds.Perm es) :
    IsComplexUnlinked ds ↔ IsComplexUnlinked es :=
  h.pairwise_iff ComplexTemperedSorted.not_linked_symm

/-- The compact-finite standard module of a complex character list is irreducible exactly
when its inducing characters are pairwise unlinked, in any supplied order. -/
def ComplexStandardIrreducibilityUnlinkedStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData), ds.length = n →
    (IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds) ↔ IsComplexUnlinked ds)

set_option maxHeartbeats 1150000 in
theorem complexStandardIrreducibilityUnlinked : ComplexStandardIrreducibilityUnlinkedStatement := by
  intro n ds hn
  let es := ds.mergeSort complexLanglandsLE
  have hperm : es.Perm ds := List.mergeSort_perm _ _
  have hlen := hperm.length_eq.trans hn
  have hord : IsComplexLanglandsOrdered es := isComplexLanglandsOrdered_mergeSort ds
  constructor
  · intro hirr
    obtain ⟨T, hT, hInt⟩ := complexStandardPermutation n ds es hn hperm hirr
    have hI := isIrreducibleGKModule_of_injective hirr hInt hT.1 (complexStandardNontrivial n es hlen)
    exact (isComplexUnlinked_perm hperm).mp (unlinked_of_ordered_irreducible hlen hord hI)
  · intro h
    have h' := (isComplexUnlinked_perm hperm).mpr h
    exact complexStandardIrreducible_of_perm n ds es hlen hperm h'
      (complexStandardIrreducibleCriterion n es hlen hord h')

/-- Every retained sublist of an irreducible complex inducing list is again irreducible
at its own rank. -/
theorem complexStandardIrreducible_of_sublist {n : ℕ} {ds es : List ComplexCharacterData}
    (hlen : ds.length = n) (hsub : es.Sublist ds)
    (hirr : IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds)) :
    IsIrreducibleGKModule (complexStandardRep es.length es) (complexStandardLie es.length es) :=
  (complexStandardIrreducibilityUnlinked es.length es rfl).mpr
    (((complexStandardIrreducibilityUnlinked n ds hlen).mp hirr).sublist hsub)

end Langlands.Archimedean
