import Langlands.Algebra.UniversalEnvelopingFiltration
import Langlands.Algebra.SymmetricPowerMaps
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange

/-! # Symmetric words in the actual universal enveloping algebra -/

noncomputable section
universe u v
set_option autoImplicit false
open scoped TensorProduct BigOperators

namespace Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

section Words

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The ordered product of the genuine Lie generators in a list. -/
def word (l : List L) : U := (l.map (UniversalEnvelopingAlgebra.ι R)).prod

@[simp] theorem word_nil : word R L [] = 1 := rfl

@[simp] theorem word_cons (x : L) (l : List L) :
    word R L (x :: l) = UniversalEnvelopingAlgebra.ι R x * word R L l := rfl

theorem word_mem_degreeFiltration (l : List L) :
    word R L l ∈ degreeFiltration R L l.length := by
  induction l with
  | nil => exact Submodule.one_le.mp le_rfl
  | cons x l ih =>
    simpa only [word_cons, List.length_cons, Nat.add_comm] using
      mul_mem_degreeFiltration R L
        (show UniversalEnvelopingAlgebra.ι R x ∈ degreeFiltration R L 1 by
          simpa using generator_mem_degreeOne R L x) ih

/-- Permuting a word changes it only in strictly lower degree. -/
theorem word_sub_word_mem_of_perm {l l' : List L} (h : l.Perm l') :
    word R L l - word R L l' ∈ degreeFiltration R L (l.length - 1) := by
  induction h with
  | nil => simp
  | @cons x l l' h ih =>
    cases l with
    | nil =>
      have hl' : l' = [] := List.length_eq_zero_iff.mp h.length_eq.symm
      subst l'
      simp
    | cons y l =>
      simp only [List.length_cons, Nat.add_sub_cancel] at ih ⊢
      have hm := mul_mem_degreeFiltration R L
        (show UniversalEnvelopingAlgebra.ι R x ∈ degreeFiltration R L 1 by
          simpa using generator_mem_degreeOne R L x) ih
      simpa only [word_cons, mul_sub, Nat.add_comm] using hm
  | swap x y l =>
    have hc := commutator_mem_degreeOne R L
      (generator_mem_degreeOne R L y) (generator_mem_degreeOne R L x)
    have hm := mul_mem_degreeFiltration R L
      (show UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x -
          UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y ∈
          degreeFiltration R L 1 by simpa using hc)
      (word_mem_degreeFiltration R L l)
    have hn : l.length + 1 + 1 - 1 = 1 + l.length := by omega
    simpa only [word_cons, List.length_cons, hn, sub_mul, mul_assoc] using hm
  | @trans l l' l'' h h' ih ih' =>
    rw [← h.length_eq] at ih'
    simpa only [sub_add_sub_cancel] using
      (degreeFiltration R L (l.length - 1)).add_mem ih ih'

/-- Algebra maps compatible with a linear map on the actual generators
carry each ordered list word to its image word. -/
theorem map_word {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (f : U →ₐ[R] UniversalEnvelopingAlgebra R L') (h : L →ₗ[R] L')
    (hgen : ∀ x, f (UniversalEnvelopingAlgebra.ι R x) =
      UniversalEnvelopingAlgebra.ι R (h x)) (l : List L) :
    f (word R L l) = word R L' (l.map h) := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [word_cons, map_mul, hgen, ih, List.map_cons]

end Words

section Symmetrization

variable (R : Type) (L : Type v) [Field R]
  [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The multilinear ordered product of `d` genuine Lie generators. -/
def orderedWord (d : ℕ) : MultilinearMap R (fun _ : Fin d => L) U :=
  (MultilinearMap.mkPiAlgebraFin R d U).compLinearMap
    (fun _ => (UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap)

@[simp] theorem orderedWord_apply {d : ℕ} (x : Fin d → L) :
    orderedWord R L d x = word R L (List.ofFn x) := by
  simp only [orderedWord, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebraFin_apply, word, List.map_ofFn, Function.comp_def]
  rfl

theorem orderedWord_mem_degreeFiltration {d : ℕ} (x : Fin d → L) :
    orderedWord R L d x ∈ degreeFiltration R L d := by
  simpa using word_mem_degreeFiltration R L (List.ofFn x)

/-- The normalized permutation average of the multilinear generator word. -/
def symmetricWord (d : ℕ) : MultilinearMap R (fun _ : Fin d => L) U :=
  (Fintype.card (Equiv.Perm (Fin d)) : R)⁻¹ •
    ∑ e : Equiv.Perm (Fin d), (orderedWord R L d).domDomCongr e

theorem symmetricWord_apply {d : ℕ} (x : Fin d → L) :
    symmetricWord R L d x = (Fintype.card (Equiv.Perm (Fin d)) : R)⁻¹ •
      ∑ e : Equiv.Perm (Fin d), orderedWord R L d (x ∘ e) := by
  simp only [symmetricWord, smul_apply, sum_apply, MultilinearMap.domDomCongr_apply,
    Function.comp_def]

theorem symmetricWord_perm {d : ℕ} (e : Equiv.Perm (Fin d)) (x : Fin d → L) :
    symmetricWord R L d (x ∘ e) = symmetricWord R L d x := by
  rw [symmetricWord_apply, symmetricWord_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft e)
    (fun p => orderedWord R L d ((x ∘ e) ∘ p))
    (fun p => orderedWord R L d (x ∘ p)) (fun _ => rfl)

/-- Actual symmetric tensor powers map linearly to the genuine enveloping algebra. -/
def symmetrize (d : ℕ) : Sym[R]^d L →ₗ[R] U :=
  Langlands.Algebra.SymmetricTensors.lift (symmetricWord R L d)
    (symmetricWord_perm R L)

@[simp] theorem symmetrize_tprod {d : ℕ} (x : Fin d → L) :
    symmetrize R L d (SymmetricPower.tprod R x) = symmetricWord R L d x :=
  Langlands.Algebra.SymmetricTensors.lift_tprod _ _ _

theorem symmetricWord_mem_degreeFiltration {d : ℕ} (x : Fin d → L) :
    symmetricWord R L d x ∈ degreeFiltration R L d := by
  rw [symmetricWord_apply]
  exact (degreeFiltration R L d).smul_mem _
    (Submodule.sum_mem _ fun e _ => orderedWord_mem_degreeFiltration R L (x ∘ e))

theorem symmetrize_mem_degreeFiltration {d : ℕ} (a : Sym[R]^d L) :
    symmetrize R L d a ∈ degreeFiltration R L d := by
  have h : Submodule.span R (Set.range (SymmetricPower.tprod R (ι := Fin d) (M := L))) ≤
      (degreeFiltration R L d).comap (symmetrize R L d) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    simpa using symmetricWord_mem_degreeFiltration R L x
  rw [SymmetricPower.span_tprod_eq_top] at h
  exact h Submodule.mem_top

theorem map_orderedWord {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (f : U →ₐ[R] UniversalEnvelopingAlgebra R L') (h : L →ₗ[R] L')
    (hgen : ∀ x, f (UniversalEnvelopingAlgebra.ι R x) =
      UniversalEnvelopingAlgebra.ι R (h x)) {d : ℕ} (x : Fin d → L) :
    f (orderedWord R L d x) = orderedWord R L' d (fun i => h (x i)) := by
  simpa [Function.comp_def] using map_word R L f h hgen (List.ofFn x)

theorem map_symmetricWord {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (f : U →ₐ[R] UniversalEnvelopingAlgebra R L') (h : L →ₗ[R] L')
    (hgen : ∀ x, f (UniversalEnvelopingAlgebra.ι R x) =
      UniversalEnvelopingAlgebra.ι R (h x)) {d : ℕ} (x : Fin d → L) :
    f (symmetricWord R L d x) = symmetricWord R L' d (fun i => h (x i)) := by
  simp only [symmetricWord_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact map_orderedWord R L f h hgen (x ∘ e)

theorem map_symmetrize {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (f : U →ₐ[R] UniversalEnvelopingAlgebra R L') (h : L →ₗ[R] L')
    (hgen : ∀ x, f (UniversalEnvelopingAlgebra.ι R x) =
      UniversalEnvelopingAlgebra.ι R (h x)) {d : ℕ} (a : Sym[R]^d L) :
    f (symmetrize R L d a) = symmetrize R L' d
      (Langlands.Algebra.SymmetricTensors.map h a) := by
  have heq : f.toLinearMap.comp (symmetrize R L d) =
      (symmetrize R L' d).comp (Langlands.Algebra.SymmetricTensors.map h) := by
    apply Langlands.Algebra.SymmetricTensors.linearMap_ext
    intro x
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      Langlands.Algebra.SymmetricTensors.map_tprod, symmetrize_tprod] using
      map_symmetricWord R L f h hgen x
  exact congrArg (fun t => t a) heq

variable [CharZero R]

theorem symmetricWord_sub_orderedWord_mem {d : ℕ} (x : Fin d → L) :
    symmetricWord R L d x - orderedWord R L d x ∈
      degreeFiltration R L (d - 1) := by
  have hc : (Fintype.card (Equiv.Perm (Fin d)) : R) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have heq : symmetricWord R L d x - orderedWord R L d x =
      (Fintype.card (Equiv.Perm (Fin d)) : R)⁻¹ •
        ∑ e : Equiv.Perm (Fin d),
          (orderedWord R L d (x ∘ e) - orderedWord R L d x) := by
    rw [symmetricWord_apply, Finset.sum_sub_distrib, smul_sub]
    simp only [Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul R, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [heq]
  apply (degreeFiltration R L (d - 1)).smul_mem
  apply Submodule.sum_mem
  intro e _
  simpa using word_sub_word_mem_of_perm R L (e.ofFn_comp_perm x)

end Symmetrization

end Langlands.Algebra.UniversalEnveloping
