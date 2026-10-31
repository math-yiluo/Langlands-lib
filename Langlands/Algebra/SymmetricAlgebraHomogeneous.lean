import Langlands.Algebra.FilteredSymmetricAlgebraSymmetrization
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Canonical homogeneous components of the genuine symmetric algebra -/

noncomputable section
universe uR uM uN
set_option autoImplicit false

namespace Langlands.Algebra.SymmetricGrading

variable (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]

local notation "S" => SymmetricAlgebra R M

/-- Record the degree of every generator by an auxiliary polynomial variable. -/
def degreePolynomial : S →ₐ[R] Polynomial S :=
  SymmetricAlgebra.lift
    (((Polynomial.monomial 1 : S →ₗ[S] Polynomial S).restrictScalars R).comp
      (SymmetricAlgebra.ι R M))

@[simp]
theorem degreePolynomial_ι (x : M) :
    degreePolynomial R M (SymmetricAlgebra.ι R M x) =
      Polynomial.monomial 1 (SymmetricAlgebra.ι R M x) := by
  simp [degreePolynomial]

/-- The canonical degree-`d` projection, with values in the original symmetric algebra. -/
def component (d : ℕ) : S →ₗ[R] S :=
  ((Polynomial.lcoeff S d).restrictScalars R).comp (degreePolynomial R M).toLinearMap

@[simp]
theorem component_apply (d : ℕ) (P : S) :
    component R M d P = (degreePolynomial R M P).coeff d := rfl

/-- The actual span of symmetric monomials of exactly the indicated length. -/
def homogeneousSpan (d : ℕ) : Submodule R S :=
  Submodule.span R {P | ∃ l : List M,
    l.length = d ∧ (l.map (SymmetricAlgebra.ι R M)).prod = P}

theorem prod_mem_homogeneousSpan (l : List M) :
    (l.map (SymmetricAlgebra.ι R M)).prod ∈ homogeneousSpan R M l.length :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

theorem degreePolynomial_prod (l : List M) :
    degreePolynomial R M ((l.map (SymmetricAlgebra.ι R M)).prod) =
      Polynomial.monomial l.length ((l.map (SymmetricAlgebra.ι R M)).prod) := by
  induction l with
  | nil => simp [degreePolynomial, Polynomial.monomial_zero_left]
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, degreePolynomial_ι, ih,
      Polynomial.monomial_mul_monomial, List.length_cons, Nat.add_comm 1]

theorem component_prod (d : ℕ) (l : List M) :
    component R M d ((l.map (SymmetricAlgebra.ι R M)).prod) =
      if l.length = d then (l.map (SymmetricAlgebra.ι R M)).prod else 0 := by
  simp only [component_apply, degreePolynomial_prod, Polynomial.coeff_monomial]

theorem component_algebraMap (d : ℕ) (r : R) :
    component R M d (algebraMap R S r) = if 0 = d then algebraMap R S r else 0 := by
  simp [component_apply, Polynomial.algebraMap_apply, Polynomial.coeff_C, eq_comm]

theorem component_ι (d : ℕ) (x : M) :
    component R M d (SymmetricAlgebra.ι R M x) =
      if 1 = d then SymmetricAlgebra.ι R M x else 0 := by
  simp only [component_apply, degreePolynomial_ι, Polynomial.coeff_monomial]

theorem algebraMap_mem_homogeneousSpan_zero (r : R) :
    algebraMap R S r ∈ homogeneousSpan R M 0 := by
  simpa [Algebra.smul_def] using
    (homogeneousSpan R M 0).smul_mem r (prod_mem_homogeneousSpan R M [])

theorem mul_mem_homogeneousSpan {p q : ℕ} {P Q : S}
    (hP : P ∈ homogeneousSpan R M p) (hQ : Q ∈ homogeneousSpan R M q) :
    P * Q ∈ homogeneousSpan R M (p + q) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨m, hm, rfl⟩ := hQ
      simpa only [List.map_append, List.prod_append, List.length_append, hl, hm] using
        prod_mem_homogeneousSpan R M (l ++ m)
    | zero => simp
    | add Q T hQ hT ihQ ihT =>
      simpa only [mul_add] using (homogeneousSpan R M (p + q)).add_mem ihQ ihT
    | smul r Q hQ ih =>
      simpa only [mul_smul_comm] using (homogeneousSpan R M (p + q)).smul_mem r ih
  | zero => simp
  | add P T hP hT ihP ihT =>
    simpa only [add_mul] using (homogeneousSpan R M (p + q)).add_mem ihP ihT
  | smul r P hP ih =>
    simpa only [smul_mul_assoc] using (homogeneousSpan R M (p + q)).smul_mem r ih

/-- Degree components obey the ordinary finite convolution formula. -/
theorem component_mul (d : ℕ) (P Q : S) :
    component R M d (P * Q) =
      ∑ a ∈ Finset.antidiagonal d, component R M a.1 P * component R M a.2 Q := by
  simp only [component_apply, map_mul, Polynomial.coeff_mul]

/-- Every component belongs to the genuine monomial span of its degree. -/
theorem component_mem_homogeneousSpan (d : ℕ) (P : S) :
    component R M d P ∈ homogeneousSpan R M d := by
  induction P using SymmetricAlgebra.induction generalizing d with
  | algebraMap r =>
    rw [component_algebraMap]
    split_ifs with h
    · subst d
      exact algebraMap_mem_homogeneousSpan_zero R M r
    · exact Submodule.zero_mem _
  | ι x =>
    rw [component_ι]
    split_ifs with h
    · subst d
      simpa using prod_mem_homogeneousSpan R M [x]
    · exact Submodule.zero_mem _
  | mul P Q ihP ihQ =>
    rw [component_mul]
    apply Submodule.sum_mem
    intro a ha
    have heq := Finset.mem_antidiagonal.mp ha
    rw [← heq]
    exact mul_mem_homogeneousSpan R M (ihP a.1) (ihQ a.2)
  | add P Q ihP ihQ =>
    simpa only [map_add] using (homogeneousSpan R M d).add_mem (ihP d) (ihQ d)

/-- On an actual homogeneous span the projection has the expected Kronecker formula. -/
theorem component_of_mem_homogeneousSpan (d : ℕ) {e : ℕ} {P : S}
    (hP : P ∈ homogeneousSpan R M e) :
    component R M d P = if e = d then P else 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    simp only [component_prod, hl]
  | zero => simp
  | add P Q hP hQ ihP ihQ =>
    rw [map_add, ihP, ihQ]
    split_ifs <;> simp
  | smul r P hP ih =>
    rw [map_smul, ih]
    split_ifs <;> simp

theorem mem_homogeneousSpan_iff (d : ℕ) (P : S) :
    P ∈ homogeneousSpan R M d ↔ component R M d P = P := by
  constructor
  · intro h
    simpa using component_of_mem_homogeneousSpan R M d h
  · intro h
    rw [← h]
    exact component_mem_homogeneousSpan R M d P

theorem component_component (d e : ℕ) (P : S) :
    component R M d (component R M e P) = if e = d then component R M e P else 0 :=
  component_of_mem_homogeneousSpan R M d (component_mem_homogeneousSpan R M e P)

/-- Evaluating the auxiliary variable at one recovers the original tensor. -/
theorem degreePolynomial_eval_one (P : S) :
    (degreePolynomial R M P).eval 1 = P := by
  induction P using SymmetricAlgebra.induction with
  | algebraMap r => simp [Polynomial.algebraMap_apply]
  | ι x => simp
  | mul P Q ihP ihQ => simp [ihP, ihQ]
  | add P Q ihP ihQ => simp [ihP, ihQ]

/-- The canonical decomposition is a finite sum in the original symmetric algebra. -/
theorem sum_components (P : S) :
    ∑ d ∈ (degreePolynomial R M P).support, component R M d P = P := by
  simpa only [Polynomial.eval_eq_sum, Polynomial.sum_def, one_pow, mul_one,
    component_apply] using degreePolynomial_eval_one R M P

variable {N : Type uN} [AddCommGroup N] [Module R N]

/-- Every symmetric-algebra map induced by a linear map commutes with degree projection. -/
theorem component_lift (f : M →ₗ[R] N) (d : ℕ) (P : S) :
    component R N d
        (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp f) P) =
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp f) (component R M d P) := by
  let h := SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp f)
  have hnat :
      (degreePolynomial R N).comp h =
        (Polynomial.mapAlgHom h).comp (degreePolynomial R M) := by
    apply SymmetricAlgebra.algHom_ext
    ext x
    simp [h, degreePolynomial]
  have heq := AlgHom.congr_fun hnat P
  simpa only [AlgHom.comp_apply, component_apply, Polynomial.coeff_mapAlgHom_apply] using
    congrArg (fun p : Polynomial (SymmetricAlgebra R N) => p.coeff d) heq

end Langlands.Algebra.SymmetricGrading

namespace Langlands.Algebra.UniversalEnveloping

open SymmetricGrading

variable (R : Type) (L : Type uM) [Field R] [LieRing L] [LieAlgebra R L]

theorem homogeneousSpan_le_symmetricDegreeFiltration (d : ℕ) :
    homogeneousSpan R L d ≤ symmetricDegreeFiltration R L d := by
  apply Submodule.span_le.mpr
  rintro P ⟨l, hl, rfl⟩
  exact prod_mem_symmetricDegreeFiltration R L l hl.le

theorem component_eq_zero_of_mem_symmetricDegreeFiltration {d e : ℕ}
    {P : SymmetricAlgebra R L} (hP : P ∈ symmetricDegreeFiltration R L d) (he : d < e) :
    component R L e P = 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    simp only [component_prod, show l.length ≠ e from by omega, ↓reduceIte]
  | zero => exact map_zero _
  | add P Q hP hQ ihP ihQ => simp only [map_add, ihP, ihQ, add_zero]
  | smul r P hP ih => simp only [map_smul, ih, smul_zero]

/-- The published length-bound filtration is exactly detected by canonical components. -/
theorem mem_symmetricDegreeFiltration_iff_components (d : ℕ) (P : SymmetricAlgebra R L) :
    P ∈ symmetricDegreeFiltration R L d ↔ ∀ e, d < e → component R L e P = 0 := by
  constructor
  · intro hP e he
    exact component_eq_zero_of_mem_symmetricDegreeFiltration R L hP he
  · intro hP
    rw [← sum_components R L P]
    apply Submodule.sum_mem
    intro e he
    by_cases hed : e ≤ d
    · exact symmetricDegreeFiltration_mono R L hed
        (homogeneousSpan_le_symmetricDegreeFiltration R L e
          (component_mem_homogeneousSpan R L e P))
    · rw [hP e (by omega)]
      exact Submodule.zero_mem _

/-- An element in degree at most `d` is the sum of components with indices `0,...,d`. -/
theorem sum_range_components_of_mem_symmetricDegreeFiltration {d : ℕ}
    {P : SymmetricAlgebra R L} (hP : P ∈ symmetricDegreeFiltration R L d) :
    ∑ e ∈ Finset.range (d + 1), component R L e P = P := by
  have hs : (degreePolynomial R L P).support ⊆ Finset.range (d + 1) := by
    intro e he
    apply Finset.mem_range.mpr
    have hne := Polynomial.mem_support_iff.mp he
    by_contra h
    exact hne (component_eq_zero_of_mem_symmetricDegreeFiltration R L hP (by omega))
  calc
    ∑ e ∈ Finset.range (d + 1), component R L e P =
        ∑ e ∈ (degreePolynomial R L P).support, component R L e P := by
      apply (Finset.sum_subset hs _).symm
      intro e he hes
      exact Polynomial.notMem_support_iff.mp hes
    _ = P := sum_components R L P

end Langlands.Algebra.UniversalEnveloping
