import Langlands.Algebra.SymmetricAlgebraEnvelopingSymmetrization

/-! # Filtered surjectivity of whole symmetric-algebra symmetrization -/

noncomputable section
universe v
set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type) (L : Type v) [Field R] [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "S" => SymmetricAlgebra R L

/-- Span of ordered enveloping words with a specified length bound. -/
def envelopingWordSpan (d : ℕ) : Submodule R U :=
  Submodule.span R {a | ∃ l : List L, l.length ≤ d ∧ word R L l = a}

/-- Span of actual symmetric-algebra monomials with a specified length bound. -/
def symmetricDegreeFiltration (d : ℕ) : Submodule R S :=
  Submodule.span R {a | ∃ l : List L,
    l.length ≤ d ∧ (l.map (SymmetricAlgebra.ι R L)).prod = a}

theorem envelopingWordSpan_mono : Monotone (envelopingWordSpan R L) := by
  intro d e h
  apply Submodule.span_mono
  rintro a ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

theorem symmetricDegreeFiltration_mono : Monotone (symmetricDegreeFiltration R L) := by
  intro d e h
  apply Submodule.span_mono
  rintro a ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

theorem word_mem_envelopingWordSpan (l : List L) {d : ℕ} (hl : l.length ≤ d) :
    word R L l ∈ envelopingWordSpan R L d :=
  Submodule.subset_span ⟨l, hl, rfl⟩

theorem prod_mem_symmetricDegreeFiltration (l : List L) {d : ℕ} (hl : l.length ≤ d) :
    (l.map (SymmetricAlgebra.ι R L)).prod ∈ symmetricDegreeFiltration R L d :=
  Submodule.subset_span ⟨l, hl, rfl⟩

private theorem envelopingWordSpan_mul_generator {d : ℕ} {a : U}
    (ha : a ∈ envelopingWordSpan R L d) (x : L) :
    a * UniversalEnvelopingAlgebra.ι R x ∈ envelopingWordSpan R L (d + 1) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    have heq : word R L l * UniversalEnvelopingAlgebra.ι R x = word R L (l ++ [x]) := by
      simp [word]
    rw [heq]
    exact word_mem_envelopingWordSpan R L _ (by simpa using Nat.add_le_add_right hl 1)
  | zero => simp
  | add a b ha hb iha ihb =>
    simpa only [add_mul] using (envelopingWordSpan R L (d + 1)).add_mem iha ihb
  | smul r a ha ih =>
    simpa only [smul_mul_assoc] using (envelopingWordSpan R L (d + 1)).smul_mem r ih

/-- The genuine submodule-power filtration is exactly the span of length-bounded words. -/
theorem degreeFiltration_eq_envelopingWordSpan (d : ℕ) :
    degreeFiltration R L d = envelopingWordSpan R L d := by
  apply le_antisymm
  · intro a ha
    induction ha using Submodule.pow_induction_on_right' with
    | algebraMap r =>
      simpa only [word_nil, Algebra.smul_def, mul_one] using
        (envelopingWordSpan R L 0).smul_mem r
          (word_mem_envelopingWordSpan R L [] (by simp))
    | add a b i ha hb iha ihb => exact (envelopingWordSpan R L i).add_mem iha ihb
    | mul_mem i a ha ih m hm =>
      obtain ⟨c, hc, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
      obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hc
      obtain ⟨x, rfl⟩ := hb
      rw [mul_add]
      apply (envelopingWordSpan R L (i + 1)).add_mem
      · rw [← Algebra.commutes r a, ← Algebra.smul_def]
        exact (envelopingWordSpan R L (i + 1)).smul_mem r
          (envelopingWordSpan_mono R L (Nat.le_succ i) ih)
      · exact envelopingWordSpan_mul_generator R L ih x
  · apply Submodule.span_le.mpr
    rintro a ⟨l, hl, rfl⟩
    exact degreeFiltration_mono R L hl (word_mem_degreeFiltration R L l)

/-- Whole symmetrization respects the actual length-bound filtration. -/
theorem symmetricAlgebraSymmetrize_mem_degreeFiltration {d : ℕ} {P : S}
    (hP : P ∈ symmetricDegreeFiltration R L d) :
    symmetricAlgebraSymmetrize R L P ∈ degreeFiltration R L d := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    exact degreeFiltration_mono R L hl (symmetricAlgebraSymmetrize_prod_mem R L l)
  | zero => simp
  | add P Q hP hQ ihP ihQ =>
    simpa only [map_add] using (degreeFiltration R L d).add_mem ihP ihQ
  | smul r P hP ih =>
    simpa only [map_smul] using (degreeFiltration R L d).smul_mem r ih

/-- Whole symmetrization restricted to matching degree bounds. -/
def symmetricAlgebraSymmetrizeDegree (d : ℕ) :
    symmetricDegreeFiltration R L d →ₗ[R] degreeFiltration R L d :=
  ((symmetricAlgebraSymmetrize R L).comp
    (symmetricDegreeFiltration R L d).subtype).codRestrict
      (degreeFiltration R L d)
      (fun P => symmetricAlgebraSymmetrize_mem_degreeFiltration R L P.property)

@[simp] theorem symmetricAlgebraSymmetrizeDegree_coe (d : ℕ)
    (P : symmetricDegreeFiltration R L d) :
    (symmetricAlgebraSymmetrizeDegree R L d P : U) =
      symmetricAlgebraSymmetrize R L P.val := rfl

/-- In characteristic zero every genuine degree piece is the image of its
corresponding symmetric monomial span. -/
theorem map_symmetricDegreeFiltration [CharZero R] (d : ℕ) :
    Submodule.map (symmetricAlgebraSymmetrize R L) (symmetricDegreeFiltration R L d) =
      degreeFiltration R L d := by
  apply le_antisymm
  · rintro a ⟨P, hP, rfl⟩
    exact symmetricAlgebraSymmetrize_mem_degreeFiltration R L hP
  · induction d using Nat.strong_induction_on with
    | h d ih =>
      rw [degreeFiltration_eq_envelopingWordSpan]
      apply Submodule.span_le.mpr
      rintro a ⟨l, hl, rfl⟩
      have hsym :
          symmetricAlgebraSymmetrize R L ((l.map (SymmetricAlgebra.ι R L)).prod) ∈
            Submodule.map (symmetricAlgebraSymmetrize R L)
              (symmetricDegreeFiltration R L d) :=
        Submodule.mem_map.mpr
          ⟨_, prod_mem_symmetricDegreeFiltration R L l hl, rfl⟩
      cases l with
      | nil => simpa using hsym
      | cons x t =>
        have ht : t.length < d := lt_of_lt_of_le (by simp) hl
        have hdiff :
            symmetricAlgebraSymmetrize R L
                (((x :: t).map (SymmetricAlgebra.ι R L)).prod) -
              word R L (x :: t) ∈ degreeFiltration R L t.length := by
          simpa only [List.length_cons, Nat.add_sub_cancel] using
            symmetricAlgebraSymmetrize_prod_sub_word_mem R L (x :: t)
        have hdiff' := Submodule.map_mono
          (f := symmetricAlgebraSymmetrize R L)
          (symmetricDegreeFiltration_mono R L (Nat.le_of_lt ht)) (ih _ ht hdiff)
        have hword :=
          (Submodule.map (symmetricAlgebraSymmetrize R L)
            (symmetricDegreeFiltration R L d)).sub_mem hsym hdiff'
        rw [sub_sub_cancel] at hword
        exact hword

/-- The restricted map is onto the entire genuine filtration piece. -/
theorem symmetricAlgebraSymmetrizeDegree_surjective [CharZero R] (d : ℕ) :
    Function.Surjective (symmetricAlgebraSymmetrizeDegree R L d) := by
  intro a
  have ha := (map_symmetricDegreeFiltration R L d).ge a.property
  obtain ⟨P, hP, heq⟩ := ha
  exact ⟨⟨P, hP⟩, Subtype.ext heq⟩

/-- Whole normalized symmetrization is surjective in characteristic zero. -/
theorem symmetricAlgebraSymmetrize_surjective [CharZero R] :
    Function.Surjective (symmetricAlgebraSymmetrize R L) := by
  intro a
  obtain ⟨d, hd⟩ := exists_mem_degreeFiltration R L a
  rw [← map_symmetricDegreeFiltration R L d] at hd
  obtain ⟨P, _, hP⟩ := hd
  exact ⟨P, hP⟩

end Langlands.Algebra.UniversalEnveloping
