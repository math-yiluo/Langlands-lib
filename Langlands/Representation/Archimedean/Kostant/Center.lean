import Langlands.Representation.Archimedean.Kostant.AssocSymbol
import Langlands.Representation.Archimedean.Kostant.Newton
import Langlands.Representation.Archimedean.Kostant.Coordinates

/-!
# Central elements of `U(∏ᵢ 𝔤𝔩_{n i})` with prescribed symbols

Let `L = ∏ᵢ 𝔤𝔩_{n i}(K)` with the units `E i p q`. In `U(L)` put `(E^0)_{pq} = δ_{pq}` and
`(E^{k+1})_{pq} = ∑_r (E^k)_{pr} E_{rq}` blockwise. For `x ∈ L`,
`[x, (E^k)_{pq}] = ∑_a x_{ap} (E^k)_{aq} - ∑_b x_{qb} (E^k)_{pb}` (Gelfand), so the traces
`C_{i,k} = ∑_p (E^k)_{pp}` are central; their degree-`k` symbols are `tr(Xᵢ^k)`, `Xᵢ` the
generic matrix of block `i`. The recursion `Z_0 = 1`,
`Z_k = -(1/k) ∑_{j<k} Z_j C_{i,k-j}` gives central elements of `U_k` whose symbols are, by
Newton's identities, the coefficients `χ_{n i - k}` of the characteristic polynomial of `Xᵢ`.
-/

noncomputable section

set_option autoImplicit false

-- Entries of tuples of matrices are applied through the `Matrix` definition.
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.Kostant

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping MvPolynomial

/-! ## Commuting with generators -/

section Central

variable (K : Type*) [CommRing K] (L : Type*) [LieRing L] [LieAlgebra K L]

theorem mem_center_of_commute {z : UniversalEnvelopingAlgebra K L}
    (hz : ∀ x : L, UniversalEnvelopingAlgebra.ι K x * z = z * UniversalEnvelopingAlgebra.ι K x) :
    z ∈ Subalgebra.center K (UniversalEnvelopingAlgebra K L) := by
  rw [Subalgebra.mem_center_iff]
  intro g
  obtain ⟨d, hd⟩ := exists_mem_degreeFiltration K L g
  have hg := degreeFiltration_le_wordSpan K L d hd
  clear hd
  induction hg using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, -, rfl⟩ := hu
    induction l with
    | nil => simp
    | cons x l ih => rw [word_cons, mul_assoc, ih, ← mul_assoc, hz, mul_assoc]
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul, mul_add, hu, hv]
  | smul c u _ hu => rw [smul_mul_assoc, mul_smul_comm, hu]

end Central

/-! ## The product of matrix algebras -/

variable (K : Type*) [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → ℕ)

/-- The Lie algebra `∏ᵢ 𝔤𝔩_{n i}(K)`. -/
abbrev GLProd := ∀ i, Matrix (Fin (n i)) (Fin (n i)) K

/-- The basis of matrix units of `∏ᵢ 𝔤𝔩_{n i}(K)`. -/
def glBasis : Module.Basis (Coord n) K (GLProd K n) :=
  Pi.basis fun i => Matrix.stdBasis K (Fin (n i)) (Fin (n i))

/-- The matrix unit `E i p q`. -/
def unit (i : ι) (p q : Fin (n i)) : GLProd K n := Pi.single i (Matrix.single p q 1)

theorem glBasis_apply (c : Coord n) : glBasis K n c = unit K n c.1 c.2.1 c.2.2 := by
  obtain ⟨i, p, q⟩ := c
  simp [glBasis, unit, Matrix.stdBasis_eq_single]

omit [Fintype ι] in
theorem unit_apply (i : ι) (p q : Fin (n i)) (c : Coord n) :
    unit K n i p q c.1 c.2.1 c.2.2 = if c = ⟨i, p, q⟩ then 1 else 0 := by
  obtain ⟨j, a, b⟩ := c
  by_cases h : j = i
  · subst h
    simp only [unit, Pi.single_eq_same, Matrix.single, Matrix.of_apply, Sigma.mk.injEq,
      heq_eq_eq, true_and, Prod.mk.injEq]
    by_cases h1 : p = a <;> by_cases h2 : q = b <;> simp_all [eq_comm]
  · have : (⟨j, a, b⟩ : Coord n) ≠ ⟨i, p, q⟩ := fun h' => h (congrArg Sigma.fst h')
    simp only [unit, Pi.single_eq_of_ne h, Matrix.zero_apply, ite_eq_right this]

theorem glBasis_repr (x : GLProd K n) (c : Coord n) :
    (glBasis K n).repr x c = x c.1 c.2.1 c.2.2 := by
  refine Module.Basis.repr_apply_eq (glBasis K n) (fun x c => x c.1 c.2.1 c.2.2)
    (fun _ _ => rfl) (fun _ _ => rfl) ?_ x c
  intro c'
  funext c
  rw [glBasis_apply, unit_apply, Finsupp.single_apply]
  by_cases h : c = c' <;> simp [h, Ne.symm]

omit [Fintype ι] in
theorem lie_unit (x : GLProd K n) (i : ι) (r q : Fin (n i)) :
    ⁅x, unit K n i r q⁆ = ∑ a, x i a r • unit K n i a q - ∑ b, x i q b • unit K n i r b := by
  rw [Ring.lie_def]
  ext j a' c'
  simp only [Pi.sub_apply, Pi.mul_apply, Finset.sum_apply, Pi.smul_apply, unit]
  by_cases h : j = i
  · subst h
    simp only [Pi.single_eq_same, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.single, Matrix.of_apply, smul_eq_mul, ite_and, mul_ite, mul_one,
      mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    by_cases h1 : q = c' <;> by_cases h2 : r = a' <;> simp [h1, h2, eq_comm]
  · simp [Pi.single_eq_of_ne h]

variable [CharZero K]

local notation "U" => UniversalEnvelopingAlgebra K (GLProd K n)

/-- The generator `E i p q` of `U`. -/
def gen (i : ι) (p q : Fin (n i)) : U := UniversalEnvelopingAlgebra.ι K (unit K n i p q)

omit [Fintype ι] [CharZero K] in
theorem gen_mem (i : ι) (p q : Fin (n i)) : gen K n i p q ∈ degreeFiltration K (GLProd K n) 1 := by
  rw [degreeFiltration_one]
  exact generator_mem_degreeOne K _ (unit K n i p q)

omit [Fintype ι] [CharZero K] in
theorem comm_gen (x : GLProd K n) (i : ι) (r q : Fin (n i)) :
    UniversalEnvelopingAlgebra.ι K x * gen K n i r q - gen K n i r q * UniversalEnvelopingAlgebra.ι K x =
      ∑ a, x i a r • gen K n i a q - ∑ b, x i q b • gen K n i r b := by
  have h := (UniversalEnvelopingAlgebra.ι K (L := GLProd K n)).map_lie x (unit K n i r q)
  rw [Ring.lie_def (UniversalEnvelopingAlgebra.ι K x), lie_unit] at h
  rw [gen, ← h]
  simp [gen, map_sub, map_sum, map_smul]

/-- The matrix of generators of block `i`, with entries in `U`. -/
def genMat (i : ι) : Matrix (Fin (n i)) (Fin (n i)) U := Matrix.of fun p q => gen K n i p q

/-- The entries `(E^k)_{pq}` of the powers of the generator matrix of block `i`. -/
def pw (i : ι) (k : ℕ) (p q : Fin (n i)) : U := (genMat K n i ^ k) p q

omit [Fintype ι] [CharZero K] in
theorem pw_succ (i : ι) (k : ℕ) (p q : Fin (n i)) :
    pw K n i (k + 1) p q = ∑ r, pw K n i k p r * gen K n i r q := by
  rw [pw, pow_succ, Matrix.mul_apply]
  rfl

/-- The commutator with `x`, entrywise on matrices over `U`. -/
def adMat (x : GLProd K n) {m : Type*} (A : Matrix m m U) : Matrix m m U :=
  A.map fun u => UniversalEnvelopingAlgebra.ι K x * u - u * UniversalEnvelopingAlgebra.ι K x

omit [Fintype ι] [DecidableEq ι] [CharZero K] in
theorem adMat_mul (x : GLProd K n) {m : Type*} [Fintype m] (A B : Matrix m m U) :
    adMat K n x (A * B) = adMat K n x A * B + A * adMat K n x B := by
  ext p q
  simp only [adMat, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  noncomm_ring

/-- The scalar matrix `(x i)ᵀ` inside the matrices over `U`. -/
def scal (x : GLProd K n) (i : ι) : Matrix (Fin (n i)) (Fin (n i)) U :=
  (x i).transpose.map (algebraMap K U)

omit [Fintype ι] [CharZero K] in
theorem adMat_genMat (x : GLProd K n) (i : ι) :
    adMat K n x (genMat K n i) = scal K n x i * genMat K n i - genMat K n i * scal K n x i := by
  ext p q
  simp only [adMat, genMat, scal, Matrix.map_apply, Matrix.of_apply, Matrix.sub_apply,
    Matrix.mul_apply, Matrix.transpose_apply, comm_gen]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Algebra.smul_def]
  first | rfl | exact Algebra.commutes _ _

omit [Fintype ι] [CharZero K] in
theorem adMat_pow (x : GLProd K n) (i : ι) (k : ℕ) :
    adMat K n x (genMat K n i ^ k) =
      scal K n x i * genMat K n i ^ k - genMat K n i ^ k * scal K n x i := by
  induction k with
  | zero =>
    ext p q
    simp only [adMat, pow_zero, Matrix.map_apply, Matrix.one_apply, mul_one, one_mul,
      Matrix.sub_apply]
    split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ, adMat_mul, ih, adMat_genMat]
    noncomm_ring

/-- Gelfand's elements `C_{i,k} = ∑_p (E^k)_{pp}`. -/
def gel (i : ι) (k : ℕ) : U := ∑ p, pw K n i k p p

omit [Fintype ι] [CharZero K] in
theorem gel_mem_center (i : ι) (k : ℕ) : gel K n i k ∈ Subalgebra.center K U := by
  refine mem_center_of_commute K (GLProd K n) fun x => ?_
  rw [← sub_eq_zero, gel, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have h : ∀ p, UniversalEnvelopingAlgebra.ι K x * pw K n i k p p -
      pw K n i k p p * UniversalEnvelopingAlgebra.ι K x =
        (scal K n x i * genMat K n i ^ k - genMat K n i ^ k * scal K n x i) p p := by
    intro p
    rw [← adMat_pow]
    rfl
  simp only [h, Matrix.sub_apply, Matrix.mul_apply, Finset.sum_sub_distrib, scal,
    Matrix.map_apply, Matrix.transpose_apply]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_
  rw [Algebra.commutes]

omit [Fintype ι] [CharZero K] in
theorem pw_mem (i : ι) : ∀ (k : ℕ) (p q : Fin (n i)),
    pw K n i k p q ∈ degreeFiltration K (GLProd K n) k := by
  intro k
  induction k with
  | zero =>
    intro p q
    simp only [pw, pow_zero, Matrix.one_apply]
    split_ifs
    · exact Submodule.one_le.mp (by simp)
    · exact Submodule.zero_mem _
  | succ k ih =>
    intro p q
    rw [pw_succ]
    exact Submodule.sum_mem _ fun r _ => mul_mem_degreeFiltration K _ (ih p r) (gen_mem K n i r q)

omit [Fintype ι] [CharZero K] in
theorem gel_mem (i : ι) (k : ℕ) : gel K n i k ∈ degreeFiltration K (GLProd K n) k :=
  Submodule.sum_mem _ fun p _ => pw_mem K n i k p p

/-! ## Symbols -/

/-- The symbol data of `∏ᵢ 𝔤𝔩_{n i}(K)`. -/
abbrev glSymbol := AssocSymbol.symbolData (glBasis K n)

theorem glSymbol_ξ_unit (i : ι) (p q : Fin (n i)) :
    (glSymbol K n).ξ (unit K n i p q) = X ⟨i, p, q⟩ := by
  have h := AssocSymbol.symbolData_ξ_basis (glBasis K n) ⟨i, p, q⟩
  rwa [glBasis_apply] at h

theorem symbol_pw (i : ι) : ∀ (k : ℕ) (p q : Fin (n i)),
    (glSymbol K n).symbol k (pw K n i k p q) = (blockMatrix n K i ^ k) p q := by
  intro k
  induction k with
  | zero =>
    intro p q
    simp only [pw, pow_zero, Matrix.one_apply]
    split_ifs
    · have h := (glSymbol K n).symbol_zero_algebraMap 1
      rw [(algebraMap K U).map_one, (algebraMap K _).map_one] at h
      exact h
    · simp
  | succ k ih =>
    intro p q
    rw [pw_succ, map_sum, pow_succ, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [(glSymbol K n).symbol_mul (pw_mem K n i k p r) (gen_mem K n i r q), ih, gen,
      SymbolData.symbol_one_ι, glSymbol_ξ_unit]
    rfl

theorem symbol_gel (i : ι) (k : ℕ) :
    (glSymbol K n).symbol k (gel K n i k) = Matrix.trace (blockMatrix n K i ^ k) := by
  simp only [gel, map_sum, symbol_pw, Matrix.trace, Matrix.diag]

/-- The central elements `Z_{i,k}` with `Z_0 = 1`, `Z_k = -(1/k) ∑_{j<k} Z_j C_{i,k-j}`. -/
def zk (i : ι) (k : ℕ) : U :=
  if _h : k = 0 then 1 else
    -((k : K)⁻¹) • ∑ j : Fin k, zk i j * gel K n i (k - j)
termination_by k
decreasing_by exact j.isLt

omit [Fintype ι] [CharZero K] in
theorem zk_zero (i : ι) : zk K n i 0 = 1 := by rw [zk]; simp

omit [Fintype ι] [CharZero K] in
theorem zk_pos (i : ι) {k : ℕ} (hk : k ≠ 0) :
    zk K n i k = -((k : K)⁻¹) • ∑ j : Fin k, zk K n i j * gel K n i (k - j) := by
  rw [zk, dite_eq_right hk]

omit [Fintype ι] [CharZero K] in
theorem zk_mem_center (i : ι) (k : ℕ) : zk K n i k ∈ Subalgebra.center K U := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [zk_zero]; exact Subalgebra.one_mem _
    · rw [zk_pos K n i hk.ne']
      refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun j _ => ?_) _
      exact Subalgebra.mul_mem _ (ih j j.isLt) (gel_mem_center K n i _)

omit [Fintype ι] [CharZero K] in
theorem zk_mem (i : ι) (k : ℕ) : zk K n i k ∈ degreeFiltration K (GLProd K n) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [zk_zero]; exact Submodule.one_le.mp (by simp)
    · rw [zk_pos K n i hk.ne']
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => ?_)
      have := mul_mem_degreeFiltration K _ (ih j j.isLt) (gel_mem K n i (k - j))
      rwa [show (j : ℕ) + (k - j) = k by omega] at this

/-- The symbol of `Z_{i,k}` is the coefficient of `t^{n i - k}` of the characteristic
polynomial of the generic block. -/
theorem symbol_zk (i : ι) (k : ℕ) (hk : k ≤ n i) :
    (glSymbol K n).symbol k (zk K n i k) = (blockMatrix n K i).charpoly.coeff (n i - k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [zk_zero]
      have h1 := (glSymbol K n).symbol_zero_algebraMap 1
      rw [(algebraMap K U).map_one, (algebraMap K _).map_one] at h1
      rw [h1, Nat.sub_zero]
      have := (Matrix.charpoly_monic (blockMatrix n K i)).coeff_natDegree
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
      exact this.symm
    · rw [zk_pos K n i hpos.ne', map_smul, map_sum]
      have hterm : ∀ j : Fin k, (glSymbol K n).symbol k (zk K n i j * gel K n i (k - j)) =
          (blockMatrix n K i).charpoly.coeff (n i - j) *
            Matrix.trace (blockMatrix n K i ^ (k - j)) := by
        intro j
        have h := (glSymbol K n).symbol_mul (zk_mem K n i j) (gel_mem K n i (k - j))
        rw [show (j : ℕ) + (k - j) = k by omega] at h
        rw [h, ih j j.isLt (by omega), symbol_gel]
      simp only [hterm]
      rw [Fin.sum_univ_eq_sum_range (fun j => (blockMatrix n K i).charpoly.coeff (n i - j) *
        Matrix.trace (blockMatrix n K i ^ (k - j)))]
      have hN := newton_identity (blockMatrix n K i) k (by rwa [Fintype.card_fin])
      rw [Fintype.card_fin] at hN
      have hsum : ∑ j ∈ Finset.range k, (blockMatrix n K i).charpoly.coeff (n i - j) *
          Matrix.trace (blockMatrix n K i ^ (k - j)) =
            -((k : MvPolynomial (Coord n) K) * (blockMatrix n K i).charpoly.coeff (n i - k)) := by
        linear_combination hN
      have hcast : ((k : ℕ) : MvPolynomial (Coord n) K) = ((k : ℕ) : K) • (1 : MvPolynomial _ K) := by
        rw [Algebra.smul_def, mul_one, map_natCast]
      rw [hsum, smul_neg, neg_smul, neg_neg, ← smul_mul_assoc, hcast, smul_smul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hpos.ne'), one_smul, one_mul]

end Langlands.Archimedean.Kostant
