import Langlands.Automorphic.ArchimedeanStandardAdmissibleProof
import Langlands.Representation.Archimedean.CompactConstituentSpecialization
import Langlands.Representation.Archimedean.ComplexSwapDeformation

/-! # Constituents of reordered complex standard modules -/

noncomputable section

open scoped Matrix TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean ComplexExponentDeformation
open ConstituentCompression (IsOperatorConstituent)

/-- The compact operators and the Lie operators in real matrix directions of a complex
standard module, indexed by their disjoint union. -/
def complexStandardOperators (n : ℕ) (ds : List ComplexCharacterData) :
    Matrix.unitaryGroup (Fin n) ℂ ⊕ Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (KF n ds) :=
  Sum.elim (fun k => complexStandardRep n ds k) (fun X => complexStandardLie n ds (1 ⊗ₜ X))

variable {n : ℕ} {J : Type*} [AddCommGroup J] [Module ℂ J] [Nontrivial J]
  (ρJ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) J)
  (LJ : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ J)
  (hirr : ∀ U : Submodule ℂ J, (∀ k x, x ∈ U → ρJ k x ∈ U) →
    (∀ X x, x ∈ U → LJ X x ∈ U) → U = ⊥ ∨ U = ⊤)

include hirr

private theorem complexStandardConstituent_swap (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (hn : (pre ++ d :: e :: post).length = n)
    (hJ : IsOperatorConstituent (complexStandardOperators n (pre ++ e :: d :: post))
      (Sum.elim (fun k => ρJ k) LJ)) :
    IsOperatorConstituent (complexStandardOperators n (pre ++ d :: e :: post))
      (Sum.elim (fun k => ρJ k) LJ) := by
  obtain ⟨D, D', hiso⟩ := exists_affine_swap n pre post d e hn
  let es := pre ++ e :: d :: post
  let ds := pre ++ d :: e :: post
  have hgk := isComplexGKModule_complexStandardModule n es
  exact ConstituentCompression.isOperatorConstituent_of_compact_affine_isomorphisms
    (complexStandardRep n es) (complexStandardRep n ds) ρJ hgk.1 hgk.2.1
    (complexStandardAdmissible n es) (fun X => complexStandardLie n es (1 ⊗ₜ X)) D
    (fun X => complexStandardLie n ds (1 ⊗ₜ X)) D' LJ (swapParameters_infinite d e) hiso hirr hJ

private theorem complexStandardConstituent_perm_append {ds es : List ComplexCharacterData}
    (hperm : ds.Perm es) (pre : List ComplexCharacterData) (hn : (pre ++ ds).length = n)
    (hJ : IsOperatorConstituent (complexStandardOperators n (pre ++ ds))
      (Sum.elim (fun k => ρJ k) LJ)) :
    IsOperatorConstituent (complexStandardOperators n (pre ++ es))
      (Sum.elim (fun k => ρJ k) LJ) := by
  induction hperm generalizing pre with
  | nil => exact hJ
  | @cons d ds es _ ih =>
    have e₁ : pre ++ d :: ds = (pre ++ [d]) ++ ds := by simp
    have e₂ : pre ++ d :: es = (pre ++ [d]) ++ es := by simp
    rw [e₁] at hn hJ
    rw [e₂]
    exact ih (pre ++ [d]) hn hJ
  | swap d e post =>
    exact complexStandardConstituent_swap ρJ LJ hirr pre post d e
      ((ComplexPermutation.length_swap pre post d e).symm.trans hn) hJ
  | @trans ds es fs hde _ ihde ihef =>
    have hn' : (pre ++ es).length = n :=
      ((hde.append_left pre).length_eq.symm).trans hn
    exact ihef pre hn' (ihde pre hn hJ)

/-- A nonzero simple constituent of a complex standard module is a constituent of every
standard module with the same list of characters up to permutation. -/
theorem complexStandardConstituent_of_perm {ds es : List ComplexCharacterData}
    (hn : ds.length = n) (hperm : ds.Perm es)
    (hJ : IsOperatorConstituent (complexStandardOperators n ds) (Sum.elim (fun k => ρJ k) LJ)) :
    IsOperatorConstituent (complexStandardOperators n es) (Sum.elim (fun k => ρJ k) LJ) :=
  complexStandardConstituent_perm_append ρJ LJ hirr hperm [] hn hJ

end Langlands.Archimedean
