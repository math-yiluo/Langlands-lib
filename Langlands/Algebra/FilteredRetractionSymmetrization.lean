import Langlands.Algebra.SeparatedEnvelopingSymmetrization
import Langlands.Algebra.SymmetrizationProductComparison

/-! # Filtered symmetrization after removing prescribed Lie directions -/

noncomputable section
universe v w
set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type) (L : Type v) [Field R] [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "S" => SymmetricAlgebra R L

/-- Products of bounded enveloping coefficients with one prescribed generator
on the right, together with bounded coefficients themselves. -/
def rightGeneratorRemainder (M : Submodule R L) (d : ℕ) : Submodule R U :=
  degreeFiltration R L d ⊔
    degreeFiltration R L d * M.map (UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap

theorem rightGeneratorRemainder_mono (M : Submodule R L) :
    Monotone (rightGeneratorRemainder R L M) := by
  intro d e h
  exact sup_le_sup (degreeFiltration_mono R L h)
    (mul_le_mul' (degreeFiltration_mono R L h) le_rfl)

/-- Multiplication adds the bounds on genuine symmetric monomial spans. -/
theorem mul_mem_symmetricDegreeFiltration {p q : ℕ} {P Q : S}
    (hP : P ∈ symmetricDegreeFiltration R L p)
    (hQ : Q ∈ symmetricDegreeFiltration R L q) :
    P * Q ∈ symmetricDegreeFiltration R L (p + q) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨m, hm, rfl⟩ := hQ
      have h := prod_mem_symmetricDegreeFiltration R L (l ++ m)
        (show (l ++ m).length ≤ p + q by simpa using Nat.add_le_add hl hm)
      simpa only [List.map_append, List.prod_append] using h
    | zero => simp
    | add Q T hQ hT ihQ ihT =>
      simpa only [mul_add] using
        (symmetricDegreeFiltration R L (p + q)).add_mem ihQ ihT
    | smul r Q hQ ih =>
      simpa only [mul_smul_comm] using
        (symmetricDegreeFiltration R L (p + q)).smul_mem r ih
  | zero => simp
  | add P T hP hT ihP ihT =>
    simpa only [add_mul] using
      (symmetricDegreeFiltration R L (p + q)).add_mem ihP ihT
  | smul r P hP ih =>
    simpa only [smul_mul_assoc] using
      (symmetricDegreeFiltration R L (p + q)).smul_mem r ih

/-- A linear-induced symmetric map preserves every length bound. -/
theorem symmetricLinearLift_mem_symmetricDegreeFiltration (f : L →ₗ[R] L)
    {d : ℕ} {P : S} (hP : P ∈ symmetricDegreeFiltration R L d) :
    symmetricLinearLift R L f P ∈ symmetricDegreeFiltration R L d := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    have heq : symmetricLinearLift R L f ((l.map (SymmetricAlgebra.ι R L)).prod) =
        ((l.map f).map (SymmetricAlgebra.ι R L)).prod := by
      simp only [map_list_prod, List.map_map, Function.comp_def,
        symmetricLinearLift_ι]
    rw [heq]
    exact prod_mem_symmetricDegreeFiltration R L _ (by simpa using hl)
  | zero => simp
  | add P Q hP hQ ihP ihQ =>
    simpa only [map_add] using (symmetricDegreeFiltration R L d).add_mem ihP ihQ
  | smul r P hP ih =>
    simpa only [map_smul] using (symmetricDegreeFiltration R L d).smul_mem r ih

private theorem generator_mul_mem_symmetricProduct (M : Submodule R L)
    {d : ℕ} {P : S}
    (hP : P ∈ symmetricDegreeFiltration R L d * M.map (SymmetricAlgebra.ι R L))
    (X : L) :
    SymmetricAlgebra.ι R L X * P ∈
      symmetricDegreeFiltration R L (d + 1) * M.map (SymmetricAlgebra.ι R L) := by
  refine Submodule.mul_induction_on hP ?_ ?_
  · intro Q hQ Y hY
    have hX : SymmetricAlgebra.ι R L X ∈ symmetricDegreeFiltration R L 1 := by
      simpa using prod_mem_symmetricDegreeFiltration R L [X] (by simp)
    have hmul := mul_mem_symmetricDegreeFiltration R L hX hQ
    rw [Nat.add_comm 1 d] at hmul
    simpa only [mul_assoc] using Submodule.mul_mem_mul hmul hY
  · intro P Q hP hQ
    simpa only [mul_add] using
      (symmetricDegreeFiltration R L (d + 1) *
        M.map (SymmetricAlgebra.ι R L)).add_mem hP hQ

private theorem monomial_sub_symmetricLinearLift_mem (M : Submodule R L)
    (f : L →ₗ[R] L) (hf : ∀ X, X - f X ∈ M) (l : List L) :
    (l.map (SymmetricAlgebra.ι R L)).prod -
      symmetricLinearLift R L f ((l.map (SymmetricAlgebra.ι R L)).prod) ∈
        symmetricDegreeFiltration R L (l.length - 1) *
          M.map (SymmetricAlgebra.ι R L) := by
  induction l with
  | nil => simp
  | cons X l ih =>
    have htail :
        symmetricLinearLift R L f ((l.map (SymmetricAlgebra.ι R L)).prod) ∈
          symmetricDegreeFiltration R L l.length :=
      symmetricLinearLift_mem_symmetricDegreeFiltration R L f
        (prod_mem_symmetricDegreeFiltration R L l le_rfl)
    have hgen : SymmetricAlgebra.ι R L (X - f X) ∈
        M.map (SymmetricAlgebra.ι R L) := ⟨X - f X, hf X, rfl⟩
    have hsecond := Submodule.mul_mem_mul htail hgen
    have hfirst : SymmetricAlgebra.ι R L X *
        ((l.map (SymmetricAlgebra.ι R L)).prod -
          symmetricLinearLift R L f ((l.map (SymmetricAlgebra.ι R L)).prod)) ∈
        symmetricDegreeFiltration R L l.length * M.map (SymmetricAlgebra.ι R L) := by
      cases l with
      | nil => simp
      | cons Y l =>
        simpa only [List.length_cons, Nat.add_sub_cancel] using
          generator_mul_mem_symmetricProduct R L M ih X
    have heq :
        ((X :: l).map (SymmetricAlgebra.ι R L)).prod -
          symmetricLinearLift R L f (((X :: l).map (SymmetricAlgebra.ι R L)).prod) =
        SymmetricAlgebra.ι R L X *
          ((l.map (SymmetricAlgebra.ι R L)).prod -
            symmetricLinearLift R L f ((l.map (SymmetricAlgebra.ι R L)).prod)) +
        symmetricLinearLift R L f ((l.map (SymmetricAlgebra.ι R L)).prod) *
          SymmetricAlgebra.ι R L (X - f X) := by
      simp only [List.map_cons, List.prod_cons, map_mul, symmetricLinearLift_ι, map_sub]
      ring
    rw [heq]
    simpa only [List.length_cons, Nat.add_sub_cancel] using
      (symmetricDegreeFiltration R L l.length * M.map (SymmetricAlgebra.ι R L)).add_mem
        hfirst hsecond

/-- Removing Lie directions changes a bounded symmetric tensor by a sum of
one prescribed factor times a coefficient of one lower degree. -/
theorem sub_symmetricLinearLift_mem_symmetricProduct (M : Submodule R L)
    (f : L →ₗ[R] L) (hf : ∀ X, X - f X ∈ M)
    {d : ℕ} {P : S} (hP : P ∈ symmetricDegreeFiltration R L d) :
    P - symmetricLinearLift R L f P ∈
      symmetricDegreeFiltration R L (d - 1) * M.map (SymmetricAlgebra.ι R L) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    exact mul_le_mul' (symmetricDegreeFiltration_mono R L
      (Nat.sub_le_sub_right hl 1)) le_rfl
      (monomial_sub_symmetricLinearLift_mem R L M f hf l)
  | zero => simp
  | add P Q hP hQ ihP ihQ =>
    simpa only [map_add, add_sub_add_comm] using
      (symmetricDegreeFiltration R L (d - 1) *
        M.map (SymmetricAlgebra.ι R L)).add_mem ihP ihQ
  | smul r P hP ih =>
    simpa only [map_smul, smul_sub] using
      (symmetricDegreeFiltration R L (d - 1) *
        M.map (SymmetricAlgebra.ι R L)).smul_mem r ih

variable [CharZero R]

/-- Symmetrizing one prescribed factor moves it to the right with only the
strict product-comparison error. -/
theorem symmetricAlgebraSymmetrize_mem_rightGeneratorRemainder
    (M : Submodule R L) {d : ℕ} {P : S}
    (hP : P ∈ symmetricDegreeFiltration R L d * M.map (SymmetricAlgebra.ι R L)) :
    symmetricAlgebraSymmetrize R L P ∈ rightGeneratorRemainder R L M d := by
  refine Submodule.mul_induction_on hP ?_ ?_
  · intro Q hQ Y hY
    obtain ⟨X, hX, rfl⟩ := hY
    have hgen : SymmetricAlgebra.ι R L X ∈ symmetricDegreeFiltration R L 1 := by
      simpa using prod_mem_symmetricDegreeFiltration R L [X] (by simp)
    have herr := symmetricAlgebraSymmetrize_mul_sub_mem R L hQ hgen
    simp only [Nat.add_sub_cancel, symmetricAlgebraSymmetrize_ι] at herr
    have hmain : symmetricAlgebraSymmetrize R L Q *
        UniversalEnvelopingAlgebra.ι R X ∈ rightGeneratorRemainder R L M d :=
      (show degreeFiltration R L d *
          M.map (UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap ≤
          rightGeneratorRemainder R L M d from le_sup_right) (Submodule.mul_mem_mul
        (symmetricAlgebraSymmetrize_mem_degreeFiltration R L hQ) ⟨X, hX, rfl⟩)
    have hlow : degreeFiltration R L d ≤ rightGeneratorRemainder R L M d :=
      le_sup_left
    simpa only [sub_add_cancel] using
      (rightGeneratorRemainder R L M d).add_mem (hlow herr) hmain
  · intro P Q hP hQ
    simpa only [map_add] using (rightGeneratorRemainder R L M d).add_mem hP hQ

/-- Actual symmetrization and a linear-induced removal of directions agree
modulo lower-degree coefficients and lower-degree coefficients times one
prescribed generator on the right. -/
theorem symmetricAlgebraSymmetrize_sub_retraction_mem
    (M : Submodule R L) (f : L →ₗ[R] L) (hf : ∀ X, X - f X ∈ M)
    {d : ℕ} {P : S} (hP : P ∈ symmetricDegreeFiltration R L d) :
    symmetricAlgebraSymmetrize R L P -
      symmetricAlgebraSymmetrize R L (symmetricLinearLift R L f P) ∈
        rightGeneratorRemainder R L M (d - 1) := by
  rw [← map_sub]
  exact symmetricAlgebraSymmetrize_mem_rightGeneratorRemainder R L M
    (sub_symmetricLinearLift_mem_symmetricProduct R L M f hf hP)

/-- Multiplying a whole coefficient and a fixed complementary tensor is
compatible with restriction, with a strict lower-degree right-generator error. -/
theorem symmetricAlgebraSymmetrize_mul_sub_retraction_mem
    (M : Submodule R L) (f : L →ₗ[R] L) (hf : ∀ X, X - f X ∈ M)
    {p q : ℕ} {P Q : S}
    (hP : P ∈ symmetricDegreeFiltration R L p)
    (hQ : Q ∈ symmetricDegreeFiltration R L q)
    (hQfixed : symmetricLinearLift R L f Q = Q) :
    symmetricAlgebraSymmetrize R L P * symmetricAlgebraSymmetrize R L Q -
      symmetricAlgebraSymmetrize R L (symmetricLinearLift R L f P * Q) ∈
        rightGeneratorRemainder R L M (p + q - 1) := by
  have hrestrict := symmetricAlgebraSymmetrize_sub_retraction_mem R L M f hf
    (mul_mem_symmetricDegreeFiltration R L hP hQ)
  have hlift : symmetricLinearLift R L f (P * Q) =
      symmetricLinearLift R L f P * Q := by
    rw [map_mul, hQfixed]
  rw [hlift] at hrestrict
  have hproduct := symmetricAlgebraSymmetrize_mul_sub_mem R L hP hQ
  have hlow : degreeFiltration R L (p + q - 1) ≤
      rightGeneratorRemainder R L M (p + q - 1) := le_sup_left
  simpa only [sub_sub_sub_cancel_left] using
    (rightGeneratorRemainder R L M (p + q - 1)).sub_mem hrestrict (hlow hproduct)

section Module

variable {V : Type w} [AddCommGroup V] [Module R V]
  [Module (UniversalEnvelopingAlgebra R L) V]
  [IsScalarTower R (UniversalEnvelopingAlgebra R L) V]

omit [CharZero R] in
/-- A right-generator error acts in the lower filtered module span whenever
the prescribed Lie generators preserve the generating subspace. -/
theorem rightGeneratorRemainder_smul_mem (M : Submodule R L) (W : Submodule R V)
    (hW : ∀ X ∈ M, ∀ w ∈ W, UniversalEnvelopingAlgebra.ι R X • w ∈ W)
    {d : ℕ} {a : U} (ha : a ∈ rightGeneratorRemainder R L M d)
    {w : V} (hw : w ∈ W) :
    a • w ∈ degreeFiltration R L d • W := by
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp ha
  rw [add_smul]
  apply (degreeFiltration R L d • W).add_mem (Submodule.smul_mem_smul hb hw)
  refine Submodule.mul_induction_on hc ?_ ?_
  · intro b hb c hc
    obtain ⟨X, hX, rfl⟩ := hc
    rw [mul_smul]
    exact Submodule.smul_mem_smul hb (hW X hX w hw)
  · intro a b ha hb
    simpa only [add_smul] using (degreeFiltration R L d • W).add_mem ha hb

end Module

end Langlands.Algebra.UniversalEnveloping
