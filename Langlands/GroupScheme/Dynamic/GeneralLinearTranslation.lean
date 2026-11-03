import Langlands.GroupScheme.Dynamic.GeneralLinear
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Right translation on the polynomial ring of the coordinates of `GL_n`

For an invertible matrix `g` over a commutative ring `S`, right translation `F ↦ (x ↦ F(x g))`
is an `S`-algebra endomorphism of the polynomial ring `S[x_{ij}, y_{ij}]` in the matrix entries
`x_{ij}` and the entries `y_{ij}` of the inverse matrix. It preserves the total degree, so it acts
on the free module of polynomials of total degree at most `d`. In the basis of monomials this
gives a homomorphism `GL_n(S) → GL_{N_d}(S)`. For weights `e : n → ℤ`, give `x_{ij}` the weight
`e j` and `y_{ij}` the weight `-e i`. Block parabolic matrices for `e` go to block parabolic
matrices for the weights of the monomials, block unipotent matrices for `-e` go to block unipotent
matrices for the negated weights, and the diagonal matrix `diag(t ^ e i)` multiplies each monomial
by `t` to the power of its weight.
-/

noncomputable section

open Matrix MvPolynomial

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The coordinates are two copies of `n × n`. -/
def coordinateEquiv : Coordinate n ≃ (n × n) ⊕ (n × n) where
  toFun
    | .entry i j => Sum.inl (i, j)
    | .inverseEntry i j => Sum.inr (i, j)
  invFun
    | Sum.inl p => .entry p.1 p.2
    | Sum.inr p => .inverseEntry p.1 p.2
  left_inv v := by cases v <;> rfl
  right_inv p := by rcases p with ⟨i, j⟩ | ⟨i, j⟩ <;> rfl

instance : Fintype (Coordinate n) := Fintype.ofEquiv _ coordinateEquiv.symm

instance : DecidableEq (Coordinate n) := coordinateEquiv.decidableEq

section Translation

variable {S : Type*} [CommRing S]

/-- The images of the variables under right translation by `g`: `x_{ij} ↦ ∑ₗ x_{il} g_{lj}` and
`y_{ij} ↦ ∑ₗ (g⁻¹)_{il} y_{lj}`. -/
def translationImage (g : GL n S) : Coordinate n → MvPolynomial (Coordinate n) S
  | .entry i j => ∑ l, X (.entry i l) * C ((g : Matrix n n S) l j)
  | .inverseEntry i j => ∑ l, C (((g⁻¹ : GL n S) : Matrix n n S) i l) * X (.inverseEntry l j)

/-- Right translation by `g` on the polynomial ring of the coordinates. -/
def translate (g : GL n S) :
    MvPolynomial (Coordinate n) S →ₐ[S] MvPolynomial (Coordinate n) S :=
  aeval (translationImage g)

theorem translate_X (g : GL n S) (v : Coordinate n) :
    translate g (X v) = translationImage g v :=
  aeval_X _ _

/-- Evaluating a right translate at `x` is evaluating at `x g`. -/
theorem aeval_values_translate {R : Type*} [CommRing R] [Algebra S R] (x : GL n R)
    (g : GL n S) (F : MvPolynomial (Coordinate n) S) :
    aeval (values x) (translate g F) =
      aeval (values (x * Matrix.GeneralLinearGroup.map (algebraMap S R) g)) F := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [AlgHom.comp_apply, translate_X, aeval_X]
  cases v with
  | entry i j =>
    simp only [translationImage, map_sum, map_mul, aeval_X, aeval_C, values, Units.val_mul,
      Matrix.mul_apply, Matrix.GeneralLinearGroup.map_apply]
  | inverseEntry i j =>
    simp only [translationImage, map_sum, map_mul, aeval_X, aeval_C, values]
    rw [_root_.mul_inv_rev, ← Matrix.GeneralLinearGroup.map_inv, Units.val_mul, Matrix.mul_apply]
    rfl

theorem translate_one : translate (1 : GL n S) = AlgHom.id S _ := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [translate_X, AlgHom.id_apply]
  cases v with
  | entry i j =>
    simp only [translationImage, Units.val_one, Matrix.one_apply, apply_ite C, map_one, map_zero,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  | inverseEntry i j =>
    simp only [translationImage, inv_one, Units.val_one, Matrix.one_apply, apply_ite C, map_one,
      map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem translate_mul (g h : GL n S) :
    translate (g * h) = (translate g).comp (translate h) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [AlgHom.comp_apply, translate_X, translate_X]
  cases v with
  | entry i j =>
    simp only [translationImage, map_sum, map_mul, translate_X, algHom_C, Units.val_mul,
      Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  | inverseEntry i j =>
    simp only [translationImage, map_sum, map_mul, translate_X, algHom_C, _root_.mul_inv_rev,
      Units.val_mul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

theorem isHomogeneous_translationImage (g : GL n S) (v : Coordinate n) :
    (translationImage g v).IsHomogeneous 1 := by
  cases v with
  | entry i j =>
    exact IsHomogeneous.sum _ _ _ fun l _ => (isHomogeneous_X S _).mul (isHomogeneous_C _ _)
  | inverseEntry i j =>
    exact IsHomogeneous.sum _ _ _ fun l _ => (isHomogeneous_C _ _).mul (isHomogeneous_X S _)

/-- Right translation preserves homogeneity and degree. -/
theorem isHomogeneous_translate {F : MvPolynomial (Coordinate n) S} {d : ℕ}
    (hF : F.IsHomogeneous d) (g : GL n S) : (translate g F).IsHomogeneous d := by
  have := hF.aeval (translationImage g) (n := 1) (isHomogeneous_translationImage g)
  rw [one_mul] at this
  exact this

/-- Right translation preserves the total degree bound. -/
theorem totalDegree_translate_monomial_le (g : GL n S) (m : Coordinate n →₀ ℕ) :
    (translate g (monomial m 1)).totalDegree ≤ m.degree :=
  (isHomogeneous_translate (isHomogeneous_monomial (1 : S) rfl) g).totalDegree_le

end Translation

section Exponents

variable (n) in
/-- The exponents of the monomials of total degree at most `d`. -/
abbrev Exponent (d : ℕ) : Type := {m : Coordinate n →₀ ℕ // m.degree ≤ d}

instance (d : ℕ) : Fintype (Exponent n d) := (Finsupp.finite_of_degree_le d).fintype

variable {S : Type*} [CommRing S] {d : ℕ}

omit [DecidableEq n] in
/-- A polynomial of total degree at most `d` is the sum of its monomials of degree at most `d`. -/
theorem eq_sum_exponent {F : MvPolynomial (Coordinate n) S} (hF : F.totalDegree ≤ d) :
    F = ∑ m : Exponent n d, monomial m.1 (F.coeff m.1) := by
  conv_lhs => rw [F.as_sum]
  symm
  refine (Finset.sum_map Finset.univ (Function.Embedding.subtype _)
    (fun m => monomial m (F.coeff m))).symm.trans ?_
  refine (Finset.sum_subset (fun m hm => ?_) (fun m _ hm => ?_)).symm
  · rw [Finset.mem_map]
    refine ⟨⟨m, ?_⟩, Finset.mem_univ _, rfl⟩
    exact (le_totalDegree hm).trans hF
  · rw [notMem_support_iff.1 hm, map_zero]

omit [Fintype n] [DecidableEq n] in
theorem coeff_eq_zero_of_totalDegree_le {F : MvPolynomial (Coordinate n) S}
    (hF : F.totalDegree ≤ d) {m : Coordinate n →₀ ℕ} (hm : ¬ m.degree ≤ d) : F.coeff m = 0 := by
  by_contra h
  exact hm ((le_totalDegree (mem_support_iff.2 h)).trans hF)

variable (d) in
/-- The matrix of right translation by `g` on the polynomials of total degree at most `d`, in the
basis of monomials: the `(m', m)` entry is the coefficient of `X^{m'}` in the translate of
`X^m`. -/
def translationMatrix (g : GL n S) : Matrix (Exponent n d) (Exponent n d) S :=
  Matrix.of fun m' m => (translate g (monomial m.1 1)).coeff m'.1

theorem translationMatrix_apply (g : GL n S) (m' m : Exponent n d) :
    translationMatrix d g m' m = (translate g (monomial m.1 1)).coeff m'.1 :=
  rfl

/-- The coefficients of a translate are the translation matrix applied to the coefficients. -/
theorem coeff_translate {F : MvPolynomial (Coordinate n) S} (hF : F.totalDegree ≤ d)
    (g : GL n S) (m' : Exponent n d) :
    (translate g F).coeff m'.1 =
      (translationMatrix d g *ᵥ fun m : Exponent n d => F.coeff m.1) m' := by
  conv_lhs => rw [eq_sum_exponent hF]
  simp only [map_sum, coeff_sum, mulVec, dotProduct, translationMatrix_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show monomial m.1 (F.coeff m.1) = F.coeff m.1 • monomial m.1 (1 : S) by
    rw [smul_monomial, smul_eq_mul, mul_one], map_smul, coeff_smul, smul_eq_mul, mul_comm]

theorem translationMatrix_mul (g h : GL n S) :
    translationMatrix d (g * h) = translationMatrix d g * translationMatrix d h := by
  ext m'' m
  rw [translationMatrix_apply, translate_mul, AlgHom.comp_apply,
    coeff_translate ((isHomogeneous_translate (isHomogeneous_monomial (1 : S) rfl) h).totalDegree_le.trans m.2)]
  rfl

theorem translationMatrix_one : translationMatrix d (1 : GL n S) = 1 := by
  ext m' m
  rw [translationMatrix_apply, translate_one, AlgHom.id_apply, coeff_monomial, Matrix.one_apply]
  simp only [Subtype.ext_iff, eq_comm]

variable (d S) in
/-- The representation of `GL_n(S)` on the polynomials of total degree at most `d`. -/
def translationHom : GL n S →* GL (Exponent n d) S where
  toFun g :=
    { val := translationMatrix d g
      inv := translationMatrix d g⁻¹
      val_inv := by rw [← translationMatrix_mul, mul_inv_cancel, translationMatrix_one]
      inv_val := by rw [← translationMatrix_mul, inv_mul_cancel, translationMatrix_one] }
  map_one' := Units.ext translationMatrix_one
  map_mul' g h := Units.ext (translationMatrix_mul g h)

theorem coe_translationHom (g : GL n S) :
    (translationHom S d g : Matrix (Exponent n d) (Exponent n d) S) = translationMatrix d g :=
  rfl

end Exponents

section Weights

variable (e : n → ℤ)

/-- The weight of a coordinate: `x_{ij}` has weight `e j` and `y_{ij}` has weight `-e i`. -/
def coordinateWeight : Coordinate n → ℤ
  | .entry _ j => e j
  | .inverseEntry i _ => -e i

/-- The weight of a monomial. -/
def monomialWeight (m : Coordinate n →₀ ℕ) : ℤ :=
  Finsupp.weight (coordinateWeight e) m

omit [Fintype n] [DecidableEq n] in
theorem monomialWeight_add (m m' : Coordinate n →₀ ℕ) :
    monomialWeight e (m + m') = monomialWeight e m + monomialWeight e m' :=
  map_add _ _ _

omit [Fintype n] [DecidableEq n] in
theorem monomialWeight_single (v : Coordinate n) (k : ℕ) :
    monomialWeight e (Finsupp.single v k) = k * coordinateWeight e v := by
  rw [monomialWeight, Finsupp.weight_apply, Finsupp.sum_single_index (by simp), nsmul_eq_mul]

omit [Fintype n] [DecidableEq n] in
theorem coordinateWeight_neg (v : Coordinate n) : coordinateWeight (-e) v = -coordinateWeight e v :=
  by cases v <;> rfl

variable {S : Type*} [CommRing S]

/-- Polynomials all of whose monomials have weight at least `c`. -/
def weightGE (c : ℤ) : Submodule S (MvPolynomial (Coordinate n) S) :=
  restrictSupport S {m | c ≤ monomialWeight e m}

/-- Polynomials all of whose monomials have weight less than `c`. -/
def weightLT (c : ℤ) : Submodule S (MvPolynomial (Coordinate n) S) :=
  restrictSupport S {m | monomialWeight e m < c}

/-- Polynomials all of whose monomials have weight at most `c`. -/
def weightLE (c : ℤ) : Submodule S (MvPolynomial (Coordinate n) S) :=
  restrictSupport S {m | monomialWeight e m ≤ c}

omit [Fintype n] [DecidableEq n] in
open scoped Pointwise in
theorem mul_mem_restrictSupport {s t u : Set (Coordinate n →₀ ℕ)} (hu : s + t ⊆ u)
    {F G : MvPolynomial (Coordinate n) S} (hF : F ∈ restrictSupport S s)
    (hG : G ∈ restrictSupport S t) : F * G ∈ restrictSupport S u := by
  refine restrictSupport_mono S hu ?_
  rw [restrictSupport_add]
  exact Submodule.mul_mem_mul hF hG

omit [Fintype n] [DecidableEq n] in
theorem mul_mem_weightGE {c c' : ℤ} {F G : MvPolynomial (Coordinate n) S}
    (hF : F ∈ weightGE (S := S) e c) (hG : G ∈ weightGE e c') :
    F * G ∈ weightGE e (c + c') := by
  refine mul_mem_restrictSupport ?_ hF hG
  rintro _ ⟨a, ha, b, hb, rfl⟩
  change c + c' ≤ monomialWeight e (a + b)
  rw [monomialWeight_add]
  exact add_le_add ha hb

omit [Fintype n] [DecidableEq n] in
theorem mul_mem_weightLT_of_le {c c' : ℤ} {F G : MvPolynomial (Coordinate n) S}
    (hF : F ∈ weightLE (S := S) e c) (hG : G ∈ weightLT e c') :
    F * G ∈ weightLT e (c + c') := by
  refine mul_mem_restrictSupport ?_ hF hG
  rintro _ ⟨a, ha, b, hb, rfl⟩
  change monomialWeight e (a + b) < c + c'
  rw [monomialWeight_add]
  exact add_lt_add_of_le_of_lt ha hb

omit [Fintype n] [DecidableEq n] in
theorem mul_mem_weightLT_of_lt {c c' : ℤ} {F G : MvPolynomial (Coordinate n) S}
    (hF : F ∈ weightLT (S := S) e c) (hG : G ∈ weightLE e c') :
    F * G ∈ weightLT e (c + c') := by
  refine mul_mem_restrictSupport ?_ hF hG
  rintro _ ⟨a, ha, b, hb, rfl⟩
  change monomialWeight e (a + b) < c + c'
  rw [monomialWeight_add]
  exact add_lt_add_of_lt_of_le ha hb

omit [Fintype n] [DecidableEq n] in
theorem weightLT_le_weightLE (c : ℤ) : weightLT (S := S) e c ≤ weightLE e c :=
  restrictSupport_mono S fun _ h => Set.mem_ofPred.2 (le_of_lt (Set.mem_ofPred.1 h))

omit [Fintype n] [DecidableEq n] in
theorem monomial_mem_weightGE (m : Coordinate n →₀ ℕ) (s : S) :
    monomial m s ∈ weightGE e (monomialWeight e m) :=
  (monomial_mem_restrictSupport S).2 (Or.inl (Set.mem_ofPred.2 le_rfl))

omit [Fintype n] [DecidableEq n] in
theorem monomial_mem_weightLE (m : Coordinate n →₀ ℕ) (s : S) :
    monomial m s ∈ weightLE e (monomialWeight e m) :=
  (monomial_mem_restrictSupport S).2 (Or.inl (Set.mem_ofPred.2 le_rfl))

omit [Fintype n] [DecidableEq n] in
theorem one_mem_weightGE : (1 : MvPolynomial (Coordinate n) S) ∈ weightGE e 0 := by
  have := monomial_mem_weightGE e (S := S) 0 1
  rwa [monomialWeight, map_zero, ← one_def] at this

omit [Fintype n] [DecidableEq n] in
/-- A product over a finite set of polynomials of weight at least `c i` has weight at least
`∑ c i`. -/
theorem prod_mem_weightGE {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (F : ι → MvPolynomial (Coordinate n) S) (hF : ∀ i ∈ s, F i ∈ weightGE e (c i)) :
    ∏ i ∈ s, F i ∈ weightGE e (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_weightGE e
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_weightGE e (hF a (Finset.mem_insert_self a s))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

omit [Fintype n] [DecidableEq n] in
theorem pow_mem_weightGE {c : ℤ} {F : MvPolynomial (Coordinate n) S} (hF : F ∈ weightGE e c)
    (k : ℕ) : F ^ k ∈ weightGE e (k * c) := by
  induction k with
  | zero => simpa using one_mem_weightGE e
  | succ k ih =>
    rw [pow_succ]
    have := mul_mem_weightGE e ih hF
    rwa [show (k : ℤ) * c + c = ((k + 1 : ℕ) : ℤ) * c by push_cast; ring] at this

omit [Fintype n] [DecidableEq n] in
/-- If the images of all variables have weight at least the weight of the variable, then the
image of every monomial has weight at least the weight of the monomial. -/
theorem aeval_monomial_mem_weightGE (φ : Coordinate n → MvPolynomial (Coordinate n) S)
    (hφ : ∀ v, φ v ∈ weightGE e (coordinateWeight e v)) (m : Coordinate n →₀ ℕ) :
    aeval φ (monomial m (1 : S)) ∈ weightGE e (monomialWeight e m) := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod]
  have h := prod_mem_weightGE e m.support (fun v => m v * coordinateWeight e v)
    (fun v => φ v ^ m v) fun v _ => pow_mem_weightGE e (hφ v) (m v)
  rwa [show ∑ v ∈ m.support, (m v : ℤ) * coordinateWeight e v = monomialWeight e m by
    rw [monomialWeight, Finsupp.weight_apply, Finsupp.sum]
    simp only [nsmul_eq_mul]] at h

/-- `F` is `X^m` plus terms of weight less than that of `m`. -/
def IsUnipotentAt (m : Coordinate n →₀ ℕ) (F : MvPolynomial (Coordinate n) S) : Prop :=
  F - monomial m 1 ∈ weightLT e (monomialWeight e m)

omit [Fintype n] [DecidableEq n] in
theorem isUnipotentAt_mul {m m' : Coordinate n →₀ ℕ} {F G : MvPolynomial (Coordinate n) S}
    (hF : IsUnipotentAt e m F) (hG : IsUnipotentAt e m' G) :
    IsUnipotentAt e (m + m') (F * G) := by
  unfold IsUnipotentAt at *
  set L := F - monomial m 1 with hL
  set L' := G - monomial m' 1 with hL'
  have h : F * G - monomial (m + m') 1 =
      monomial m 1 * L' + L * monomial m' 1 + L * L' := by
    rw [hL, hL', show monomial (m + m') (1 : S) = monomial m 1 * monomial m' 1 by
      rw [monomial_mul_monomial, one_mul]]
    ring
  rw [h, monomialWeight_add]
  refine add_mem (add_mem (mul_mem_weightLT_of_le e (monomial_mem_weightLE e m 1) hG)
    (mul_mem_weightLT_of_lt e hF (monomial_mem_weightLE e m' 1))) ?_
  exact mul_mem_weightLT_of_lt e hF (weightLT_le_weightLE e _ hG)

omit [Fintype n] [DecidableEq n] in
theorem isUnipotentAt_zero_one : IsUnipotentAt (S := S) e 0 1 := by
  unfold IsUnipotentAt
  rw [← C_apply, map_one, sub_self]
  exact zero_mem _

omit [Fintype n] [DecidableEq n] in
theorem isUnipotentAt_prod {ι : Type*} (s : Finset ι) (m : ι → Coordinate n →₀ ℕ)
    (F : ι → MvPolynomial (Coordinate n) S) (hF : ∀ i ∈ s, IsUnipotentAt e (m i) (F i)) :
    IsUnipotentAt e (∑ i ∈ s, m i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isUnipotentAt_zero_one e
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact isUnipotentAt_mul e (hF a (Finset.mem_insert_self a s))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

omit [Fintype n] [DecidableEq n] in
theorem isUnipotentAt_pow {v : Coordinate n} {F : MvPolynomial (Coordinate n) S}
    (hF : IsUnipotentAt e (Finsupp.single v 1) F) (k : ℕ) :
    IsUnipotentAt e (Finsupp.single v k) (F ^ k) := by
  induction k with
  | zero => simpa using isUnipotentAt_zero_one e
  | succ k ih =>
    rw [pow_succ, show Finsupp.single v (k + 1) = Finsupp.single v k + Finsupp.single v 1 by
      rw [Finsupp.single_add]]
    exact isUnipotentAt_mul e ih hF

omit [Fintype n] [DecidableEq n] in
/-- If the image of each variable `v` is `v` plus terms of smaller weight, then the image of each
monomial is that monomial plus terms of smaller weight. -/
theorem isUnipotentAt_aeval_monomial (φ : Coordinate n → MvPolynomial (Coordinate n) S)
    (hφ : ∀ v, IsUnipotentAt e (Finsupp.single v 1) (φ v)) (m : Coordinate n →₀ ℕ) :
    IsUnipotentAt e m (aeval φ (monomial m (1 : S))) := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod]
  have h := isUnipotentAt_prod e m.support (fun v => Finsupp.single v (m v))
    (fun v => φ v ^ m v) fun v _ => isUnipotentAt_pow e (hφ v) (m v)
  rwa [show ∑ v ∈ m.support, Finsupp.single v (m v) = m from Finsupp.sum_single m] at h

end Weights

section Representation

variable (e : n → ℤ) {S : Type*} [CommRing S]

omit [Fintype n] [DecidableEq n] in
theorem coeff_eq_zero_of_mem_restrictSupport {s : Set (Coordinate n →₀ ℕ)}
    {F : MvPolynomial (Coordinate n) S} (hF : F ∈ restrictSupport S s)
    {m : Coordinate n →₀ ℕ} (hm : m ∉ s) : F.coeff m = 0 :=
  notMem_support_iff.1 fun h => hm (hF (Finset.mem_coe.2 h))

omit [Fintype n] [DecidableEq n] in
theorem monomialWeight_single_one (v : Coordinate n) :
    monomialWeight e (Finsupp.single v 1) = coordinateWeight e v := by
  rw [monomialWeight_single, Nat.cast_one, one_mul]

omit [Fintype n] [DecidableEq n] in
theorem C_mul_X_mem_restrictSupport {s : Set (Coordinate n →₀ ℕ)} (v : Coordinate n) {c : S}
    (h : c ≠ 0 → Finsupp.single v 1 ∈ s) : C c * X v ∈ restrictSupport S s := by
  rw [C_mul_X_eq_monomial, monomial_mem_restrictSupport]
  by_cases hc : c = 0
  · exact Or.inr hc
  · exact Or.inl (h hc)

omit [Fintype n] [DecidableEq n] in
theorem X_mul_C_mem_restrictSupport {s : Set (Coordinate n →₀ ℕ)} (v : Coordinate n) {c : S}
    (h : c ≠ 0 → Finsupp.single v 1 ∈ s) : X v * C c ∈ restrictSupport S s := by
  rw [mul_comm]
  exact C_mul_X_mem_restrictSupport v h

/-- For a block parabolic `g`, the translate of each coordinate has weight at least the weight
of the coordinate. -/
theorem translationImage_mem_weightGE {g : GL n S} (hg : g ∈ blockParabolicSubgroup S e)
    (v : Coordinate n) : translationImage g v ∈ weightGE e (coordinateWeight e v) := by
  cases v with
  | entry i j =>
    refine Submodule.sum_mem _ fun l _ => X_mul_C_mem_restrictSupport _ fun hc => ?_
    change coordinateWeight e (.entry i j) ≤ monomialWeight e _
    rw [monomialWeight_single_one]
    exact not_lt.1 fun hlt => hc ((mem_blockParabolicSubgroup S e).1 hg l j hlt)
  | inverseEntry i j =>
    have hg' := (blockParabolicSubgroup S e).inv_mem hg
    refine Submodule.sum_mem _ fun l _ => C_mul_X_mem_restrictSupport _ fun hc => ?_
    change coordinateWeight e (.inverseEntry i j) ≤ monomialWeight e _
    rw [monomialWeight_single_one]
    exact neg_le_neg (not_lt.1 fun hlt => hc ((mem_blockParabolicSubgroup S e).1 hg' i l hlt))

/-- Translation by a block parabolic matrix for `e` is block parabolic for the monomial
weights. -/
theorem translationHom_mem_blockParabolicSubgroup {g : GL n S}
    (hg : g ∈ blockParabolicSubgroup S e) (d : ℕ) :
    translationHom S d g ∈
      blockParabolicSubgroup S (fun m : Exponent n d => monomialWeight e m.1) := by
  rw [mem_blockParabolicSubgroup]
  intro m' m hlt
  rw [coe_translationHom, translationMatrix_apply]
  exact coeff_eq_zero_of_mem_restrictSupport
    (aeval_monomial_mem_weightGE e _ (translationImage_mem_weightGE e hg) m.1) (not_le.2 hlt)

/-- For a block unipotent `g` for the negated weights, the translate of each coordinate is the
coordinate plus terms of smaller weight. -/
theorem translationImage_isUnipotentAt {g : GL n S} (hg : g ∈ blockUnipotentSubgroup S (-e))
    (v : Coordinate n) : IsUnipotentAt e (Finsupp.single v 1) (translationImage g v) := by
  unfold IsUnipotentAt
  rw [monomialWeight_single_one, show monomial (Finsupp.single v 1) (1 : S) = X v from rfl]
  cases v with
  | entry i j =>
    have hX : (X (.entry i j) : MvPolynomial (Coordinate n) S) =
        ∑ l, X (.entry i l) * C ((1 : Matrix n n S) l j) := by
      simp only [Matrix.one_apply, apply_ite C, map_one, map_zero, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [translationImage, hX, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [← mul_sub, ← map_sub]
    refine X_mul_C_mem_restrictSupport _ fun hc => ?_
    change monomialWeight e _ < coordinateWeight e (.entry i j)
    rw [monomialWeight_single_one]
    exact not_le.1 fun hle => hc (by
      rw [(mem_blockUnipotentSubgroup S (-e)).1 hg l j (neg_le_neg hle), sub_self])
  | inverseEntry i j =>
    have hg' := (blockUnipotentSubgroup S (-e)).inv_mem hg
    have hX : (X (.inverseEntry i j) : MvPolynomial (Coordinate n) S) =
        ∑ l, C ((1 : Matrix n n S) i l) * X (.inverseEntry l j) := by
      simp only [Matrix.one_apply, apply_ite C, map_one, map_zero, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [translationImage, hX, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [← sub_mul, ← map_sub]
    refine C_mul_X_mem_restrictSupport _ fun hc => ?_
    change monomialWeight e _ < coordinateWeight e (.inverseEntry i j)
    rw [monomialWeight_single_one]
    exact not_le.1 fun hle => hc (by
      rw [(mem_blockUnipotentSubgroup S (-e)).1 hg' i l hle, sub_self])

omit [Fintype n] in
theorem coeff_eq_of_isUnipotentAt {m : Coordinate n →₀ ℕ} {F : MvPolynomial (Coordinate n) S}
    (hF : IsUnipotentAt e m F) {m' : Coordinate n →₀ ℕ}
    (hm' : monomialWeight e m ≤ monomialWeight e m') :
    F.coeff m' = if m = m' then 1 else 0 := by
  have h := coeff_eq_zero_of_mem_restrictSupport (s := {m'' | monomialWeight e m'' <
    monomialWeight e m}) hF (m := m') (not_lt.2 hm')
  rwa [coeff_sub, sub_eq_zero, coeff_monomial] at h

/-- Translation by a block unipotent matrix for `-e` is block unipotent for the negated monomial
weights. -/
theorem translationHom_mem_blockUnipotentSubgroup {g : GL n S}
    (hg : g ∈ blockUnipotentSubgroup S (-e)) (d : ℕ) :
    translationHom S d g ∈
      blockUnipotentSubgroup S (-fun m : Exponent n d => monomialWeight e m.1) := by
  rw [mem_blockUnipotentSubgroup]
  intro m' m hle
  rw [coe_translationHom, translationMatrix_apply, Matrix.one_apply, translate,
    coeff_eq_of_isUnipotentAt e
      (isUnipotentAt_aeval_monomial e _ (translationImage_isUnipotentAt e hg) m.1)
      (neg_le_neg_iff.1 hle)]
  by_cases hm : m' = m
  · rw [ite_eq_left (congrArg Subtype.val hm.symm), ite_eq_left hm]
  · rw [ite_eq_right fun h => hm (Subtype.ext h.symm), ite_eq_right hm]

/-- The translate of a coordinate by `diag(t ^ e i)` is the coordinate times `t` to its
weight. -/
theorem translationImage_diagonalUnits (t : Sˣ) (v : Coordinate n) :
    translationImage (diagonalUnits S e t) v = C ((t ^ coordinateWeight e v : Sˣ) : S) * X v := by
  cases v with
  | entry i j =>
    simp only [translationImage, coe_diagonalUnits, Matrix.diagonal_apply, apply_ite C, map_zero,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [mul_comm]
    rfl
  | inverseEntry i j =>
    rw [translationImage, ← map_inv, coe_diagonalUnits]
    simp only [Matrix.diagonal_apply, apply_ite C, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, inv_zpow']
    rfl

/-- Translation by `diag(t ^ e i)` multiplies each monomial by `t` to its weight. -/
theorem translate_diagonalUnits_monomial (t : Sˣ) (m : Coordinate n →₀ ℕ) (c : S) :
    translate (diagonalUnits S e t) (monomial m c) =
      monomial m (c * ((t ^ monomialWeight e m : Sˣ) : S)) := by
  induction m using Finsupp.induction generalizing c with
  | zero =>
    rw [monomialWeight, map_zero, zpow_zero, Units.val_one, mul_one, ← C_apply, algHom_C]
    rfl
  | single_add v k m _ _ ih =>
    rw [monomial_single_add, map_mul, map_pow, translate_X, translationImage_diagonalUnits, ih,
      mul_pow, ← map_pow, mul_assoc, ← monomial_single_add, C_mul_monomial, monomialWeight_add,
      monomialWeight_single, zpow_add, Units.val_mul, mul_comm (k : ℤ), zpow_mul, zpow_natCast,
      Units.val_pow_eq_pow_val]
    ring_nf

end Representation

end Langlands.GroupScheme.GeneralLinear
