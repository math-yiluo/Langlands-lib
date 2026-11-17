import Langlands.Representation.Archimedean.ComplexTransposePairingClassification
import Langlands.Representation.Archimedean.ComplexStandardIrreducibleCriterionReduction
import Langlands.Representation.Archimedean.ComplexTemperedSortedReduction
import Langlands.Representation.Archimedean.ComplexStandardOppositeOrderHomReduction
import Langlands.Representation.Archimedean.ComplexStandardJacquetExponentProof
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientProof
import Langlands.Representation.Archimedean.ComplexStandardDualityProof
import Langlands.Representation.Archimedean.TransposePairingStatement

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uV

open scoped TensorProduct Matrix

namespace Langlands.Archimedean.ComplexTransposePairingReduction

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean ComplexTransposeStandardDuality

/-- Two lists sorted by the same real exponent can be aligned by injective unlinked swaps. -/
lemma injectiveIntertwiner_sorted_perm (n : ℕ) :
    ∀ (xs ys : List ComplexCharacterData), xs.Perm ys →
      xs.Pairwise (fun d e => d.exponent.re ≤ e.exponent.re) →
      ys.Pairwise (fun d e => d.exponent.re ≤ e.exponent.re) →
      ∀ pre : List ComplexCharacterData, (pre ++ xs).length = n →
        ComplexInjectiveIntertwinerExists n (pre ++ xs) (pre ++ ys) := by
  intro xs
  induction xs with
  | nil =>
    intro ys hp _ _ pre _
    have : ys = [] := List.perm_nil.mp hp.symm
    subst ys
    exact ComplexInjectiveIntertwinerExists.refl n _
  | cons a xs ih =>
    intro ys hp hxs hys pre hn
    have ha : a ∈ ys := hp.mem_iff.mp List.mem_cons_self
    obtain ⟨left, right, rfl⟩ := List.mem_iff_append.mp ha
    have hp' : xs.Perm (left ++ right) :=
      List.Perm.cons_inv (hp.trans List.perm_middle)
    have hxs' := (List.pairwise_cons.mp hxs).2
    have hys' : (left ++ right).Pairwise (fun d e => d.exponent.re ≤ e.exponent.re) := by
      rcases List.pairwise_append.mp hys with ⟨hl, har, hlr⟩
      exact List.pairwise_append.mpr ⟨hl, (List.pairwise_cons.mp har).2,
        fun d hd e he => hlr d hd e (List.mem_cons_of_mem a he)⟩
    have htie : ∀ b ∈ left, a.exponent.re = b.exponent.re := by
      intro b hb
      have hba : b.exponent.re ≤ a.exponent.re :=
        (List.pairwise_append.mp hys).2.2 b hb a List.mem_cons_self
      have hab : a.exponent.re ≤ b.exponent.re := by
        have hmem : b ∈ a :: xs := hp.mem_iff.mpr (List.mem_append_left _ hb)
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact le_rfl
        · exact (List.pairwise_cons.mp hxs).1 b hmem
      exact le_antisymm hab hba
    have hn' : ((pre ++ [a]) ++ xs).length = n := by simpa using hn
    have hrec := ih (left ++ right) hp' hxs' hys' (pre ++ [a]) hn'
    have hnmove : (pre ++ a :: left ++ right).length = n := by
      have hlen := hp'.length_eq
      simp only [List.length_append, List.length_cons] at hn hlen ⊢
      omega
    have hmove := complexInjectiveIntertwinerExists_moveToEnd
      (complexStandardUnlinkedSwapReduction complexGLTwoUnlinkedIrreducible) n a left pre right
      hnmove (fun b hb => ComplexTemperedSorted.not_linked_of_re_eq (htie b hb))
    simp only [List.append_assoc, List.cons_append] at hrec hmove ⊢
    exact hrec.trans hmove

lemma oppositeOrderHom : ComplexStandardOppositeOrderHomStatement :=
  complexStandardOppositeOrderHomReduction
    (complexStandardHomExponentJacquetReduction complexStandardJacquetExponent)
    ComplexStandardHomTransposeProof.complexStandardHomTranspose

/-- Every irreducible admissible module has a matched quotient and embedding for one
Langlands-ordered list. -/
lemma exists_matched_standard (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hgk : IsComplexGKModule n ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (hadm : IsAdmissibleGKModule ρ) :
    ∃ ds : List ComplexCharacterData, ds.length = n ∧ IsComplexLanglandsOrdered ds ∧
      ∃ (A : Standard n ds →ₗ[ℂ] V) (J : V →ₗ[ℂ] Standard n ds.reverse),
        A ≠ 0 ∧ IsComplexStandardIntertwining n ρ π ds A ∧ J ≠ 0 ∧
        (∀ k v, J (ρ k v) = complexStandardRep n ds.reverse k (J v)) ∧
        ∀ X v, J (π X v) = complexStandardLie n ds.reverse X (J v) := by
  obtain ⟨ds, hds, hord, A, hA0, hA⟩ := complexLanglandsQuotient n V ρ π hgk hirr hadm
  obtain ⟨cs, hcs, hcord, J, hJ0, hJ⟩ :=
    complexLanglandsSubrepresentation n V ρ π hgk hirr hadm
  have hsurj := surjective_of_isComplexStandardIntertwining n hirr hA hA0
  have hT0 : J.comp A ≠ 0 := by
    intro h0
    apply hJ0
    ext v : 1
    obtain ⟨f, rfl⟩ := hsurj v
    exact LinearMap.congr_fun h0 f
  have hT : IsComplexStandardIntertwining n (complexStandardRep n cs)
      (complexStandardLie n cs) ds (J.comp A) :=
    hA.comp J hJ.map_rep hJ.map_lie_one_tmul
  have hperm := oppositeOrderHom n ds cs (J.comp A) hds hcs hord hcord hT0 hT
  have hrev : ds.reverse.Pairwise (fun d e => d.exponent.re ≤ e.exponent.re) := by
    simpa only [List.pairwise_reverse, IsComplexLanglandsOrdered] using hord
  have hpcs : cs.Perm ds.reverse := hperm.symm.trans (List.reverse_perm ds).symm
  have ht := injectiveIntertwiner_sorted_perm n cs ds.reverse hpcs hcord hrev []
    (by simpa using hcs)
  simp only [List.nil_append] at ht
  obtain ⟨T, hTi, hT⟩ := ht
  refine ⟨ds, hds, hord, A, T.comp J, hA0, hA, ?_, ?_, ?_⟩
  · intro h0
    apply hJ0
    ext v : 1
    apply hTi
    simpa using LinearMap.congr_fun h0 v
  · intro k v
    change T (J (ρ k v)) = _
    rw [hJ.map_rep, hT.map_rep]
    rfl
  · intro X v
    change T (J (π X v)) = _
    have hJX : J (π X v) = complexStandardLie n cs X (J v) := by
      induction X using TensorProduct.inductionOn with
      | tmul c X =>
        have ht : (c ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) =
            c • (1 ⊗ₜ[ℝ] X) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [ht, map_smul, LinearMap.smul_apply, map_smul, map_smul,
          LinearMap.smul_apply, hJ.map_lie_one_tmul]
      | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY]
    rw [hJX, hT.map_lie]
    rfl

/-- The unique-head classification input alone implies complex transpose-pairing existence. -/
def ComplexTransposePairingOfLanglandsStatement : Prop :=
  ComplexStandardLanglandsQuotientStatement → ComplexTransposePairingStatement.{uV}

theorem complexTransposePairing_of_langlands : ComplexTransposePairingOfLanglandsStatement.{uV} := by
  intro hHead r V _ _ ρ π hgk hirr hadm
  obtain ⟨ds, hds, hord, A, J, hA0, hA, hJ0, hJK, hJL⟩ :=
    exists_matched_standard (r + 1) V ρ π hgk hirr hadm
  obtain ⟨R, hR, hRtop, hRmax⟩ := hHead (r + 1) ds hds hord
  exact ComplexTransposePairingClassification.hasNonzeroTransposeGKPairing_of_matched_standard
    hds hgk hirr hadm A hA0 hA J hJ0 hJK hJL R hR hRtop hRmax

end Langlands.Archimedean.ComplexTransposePairingReduction
