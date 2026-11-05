import Langlands.GroupScheme.GeneralLinear
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.Idempotents
import Mathlib.Data.Nat.Choose.Sum
import Langlands.BruhatTits.RationalPoints.CentralNormKernel.ExponentialPolynomial

/-! # Laurent polynomials along a family of orthogonal idempotent matrices -/

noncomputable section

universe u

open Polynomial Langlands.GroupScheme.GeneralLinear

namespace Langlands.BruhatTits.RationalPoints.CentralNormKernel

section Orthogonal

variable {ι S A : Type*} [Fintype ι] [CommRing S] [Ring A] [Algebra S A]

theorem sum_smul_mul_sum_smul {e : ι → A} (he : OrthogonalIdempotents e) (t t' : ι → S) :
    (∑ i, t i • e i) * (∑ i, t' i • e i) = ∑ i, (t i * t' i) • e i := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · rw [smul_mul_smul_comm, (he.idem i).eq]
  · intro j _ hji
    rw [smul_mul_smul_comm, he.ortho hji.symm, smul_zero]
  · simp

end Orthogonal

section Diagonal

variable {K : Type u} [Field K] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

/-- The matrix `∑ t i • E i` over a `K`-algebra. -/
def diagMatrix (E : Fin r → Matrix n n K) {S : Type*} [CommRing S] [Algebra K S]
    (t : Fin r → S) : Matrix n n S :=
  ∑ i, t i • (algebraMap K S).mapMatrix (E i)

variable {E : Fin r → Matrix n n K} (hE : CompleteOrthogonalIdempotents E)
include hE

theorem diagMatrix_mul {S : Type*} [CommRing S] [Algebra K S] (t t' : Fin r → S) :
    diagMatrix E t * diagMatrix E t' = diagMatrix E (t * t') := by
  have he := (CompleteOrthogonalIdempotents.map ((algebraMap K S).mapMatrix) hE).toOrthogonalIdempotents
  exact sum_smul_mul_sum_smul (A := Matrix n n S) he t t'

theorem diagMatrix_one {S : Type*} [CommRing S] [Algebra K S] :
    diagMatrix E (fun _ => (1 : S)) = 1 := by
  have he := (CompleteOrthogonalIdempotents.map ((algebraMap K S).mapMatrix) hE).complete
  simp only [diagMatrix, one_smul]
  exact he

/-- The invertible matrix `∑ t i • E i` for units `t i`, as a monoid homomorphism. -/
def diagHom (S : Type*) [CommRing S] [Algebra K S] : (Fin r → Sˣ) →* GL n S where
  toFun t :=
    { val := diagMatrix E fun i => (t i : S)
      inv := diagMatrix E fun i => (((t i)⁻¹ : Sˣ) : S)
      val_inv := by
        rw [diagMatrix_mul hE, ← diagMatrix_one hE (S := S)]
        congr 1
        funext i
        simp
      inv_val := by
        rw [diagMatrix_mul hE, ← diagMatrix_one hE (S := S)]
        congr 1
        funext i
        simp }
  map_one' := by
    apply Units.ext
    exact diagMatrix_one hE
  map_mul' t t' := by
    apply Units.ext
    change diagMatrix E (fun i => ((t i * t' i : Sˣ) : S)) = diagMatrix E _ * diagMatrix E _
    rw [diagMatrix_mul hE]
    congr 1

theorem diagHom_val (S : Type*) [CommRing S] [Algebra K S] (t : Fin r → Sˣ) :
    ((diagHom hE S t : GL n S) : Matrix n n S) = diagMatrix E fun i => (t i : S) := rfl

theorem map_diagHom {S S' : Type*} [CommRing S] [Algebra K S] [CommRing S'] [Algebra K S']
    (f : S →ₐ[K] S') (t : Fin r → Sˣ) :
    Matrix.GeneralLinearGroup.map f.toRingHom (diagHom hE S t) =
      diagHom hE S' (fun i => Units.map (f : S →* S') (t i)) := by
  apply Units.ext
  ext a b
  simp only [Matrix.GeneralLinearGroup.map_apply, diagHom_val, diagMatrix, Matrix.sum_apply,
    Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, map_sum, map_mul,
    Units.coe_map, MonoidHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]

end Diagonal

section Laurent

variable {K : Type u} [Field K] {r : ℕ}

variable (K r) in
/-- Laurent polynomials in `r` variables. -/
abbrev Laurent := AddMonoidAlgebra K (Fin r → ℤ)

/-- The character `a ↦ ∏ t i ^ a i` of the exponent lattice. -/
def charHom (t : Fin r → Kˣ) : Multiplicative (Fin r → ℤ) →* Kˣ where
  toFun a := ∏ i, t i ^ (Multiplicative.toAdd a i)
  map_one' := by simp
  map_mul' a b := by simp [zpow_add, Finset.prod_mul_distrib]

theorem charHom_pow (t : Fin r → Kˣ) (k : ℕ) (a : Multiplicative (Fin r → ℤ)) :
    charHom (t ^ k) a = charHom t a ^ k := by
  simp only [charHom, MonoidHom.coe_mk, OneHom.coe_mk, Pi.pow_apply, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

/-- Evaluation of Laurent polynomials at units. -/
def evalLaurent (t : Fin r → Kˣ) : Laurent K r →ₐ[K] K :=
  AddMonoidAlgebra.lift K K (Fin r → ℤ) ((Units.coeHom K).comp (charHom t))

/-- The generic unit `X i`. -/
def genericUnit (i : Fin r) : (Laurent K r)ˣ :=
  (AddMonoidAlgebra.of K (Fin r → ℤ)).toHomUnits (Multiplicative.ofAdd (Pi.single i 1))

theorem evalLaurent_genericUnit (t : Fin r → Kˣ) (i : Fin r) :
    Units.map (evalLaurent t : Laurent K r →* K) (genericUnit i) = t i := by
  classical
  apply Units.ext
  simp only [genericUnit, Units.coe_map, MonoidHom.coe_toHomUnits, MonoidHom.coe_coe, evalLaurent,
    AddMonoidAlgebra.lift_of, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply]
  simp [charHom, Pi.single_apply]

theorem evalLaurent_eq_sum (t : Fin r → Kˣ) (ℓ : Laurent K r) {S : Finset (Fin r → ℤ)}
    (hS : ℓ.coeff.support ⊆ S) :
    evalLaurent t ℓ = ∑ a ∈ S, ℓ.coeff a * (charHom t (Multiplicative.ofAdd a) : K) := by
  rw [evalLaurent, AddMonoidAlgebra.lift_apply, Finsupp.sum]
  refine Finset.sum_subset hS (fun a _ ha => ?_) |>.trans (Finset.sum_congr rfl fun a _ => ?_)
  · rw [Finsupp.notMem_support_iff.1 ha, zero_smul]
  · rfl

end Laurent

section Grouping

variable {K : Type u} [Field K] {A : Type*}

/-- Vandermonde independence over the distinct elements of a finite set. -/
theorem eq_zero_of_finset_sum_mul_pow_eq_zero (V : Finset K) (d : K → K)
    (h : ∀ k : ℕ, ∑ v ∈ V, d v * v ^ k = 0) : ∀ v ∈ V, d v = 0 := by
  intro v hv
  have := eq_zero_of_sum_mul_pow_eq_zero (ι := V) (ν := fun x : V => (x : K))
    Subtype.val_injective (c := fun x => d x)
    (fun k => by rw [Finset.sum_coe_sort V (fun x => d x * x ^ k)]; exact h k)
  exact this ⟨v, hv⟩

/-- Independence of exponential polynomials over the distinct nonzero elements of a finite set,
in characteristic zero. -/
theorem eq_zero_of_finset_sum_pow_mul_eval_eq_zero [CharZero K] (V : Finset K) (R : K → K[X])
    (hV0 : ∀ v ∈ V, v ≠ 0) (h : ∀ k : ℕ, ∑ v ∈ V, v ^ k * (R v).eval (k : K) = 0) :
    ∀ v ∈ V, R v = 0 := by
  intro v hv
  have := eq_zero_of_sum_pow_mul_eval_eq_zero (ι := V) (ν := fun x : V => (x : K))
    Subtype.val_injective (fun x => hV0 x x.2) (Q := fun x => R x)
    (fun k => by rw [Finset.sum_coe_sort V (fun x => x ^ k * (R x).eval (k : K))]; exact h k)
  exact this ⟨v, hv⟩

/-- Grouping a vanishing exponential sum by the values of `g a ^ q`, for a power map `x ↦ x ^ q`
that is injective, gives the vanishing of the sum at `g`. -/
theorem sum_mul_eq_zero_of_pow {S : Finset A} {c g : A → K} {q : ℕ}
    (hq : ∀ x y : K, x ^ q = y ^ q → x = y)
    (h : ∀ k : ℕ, ∑ a ∈ S, c a * (g a ^ q) ^ k = 0) : ∑ a ∈ S, c a * g a = 0 := by
  classical
  set V := S.image fun a => g a ^ q with hVdef
  let d : K → K := fun v => ∑ a ∈ S with g a ^ q = v, c a
  have hsum : ∀ k : ℕ, ∑ a ∈ S, c a * (g a ^ q) ^ k = ∑ v ∈ V, d v * v ^ k := by
    intro k
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun a => g a ^ q) (t := V)
      (fun a ha => Finset.mem_image_of_mem _ ha)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.1 ha).2]
  have hd : ∀ v ∈ V, d v = 0 :=
    eq_zero_of_finset_sum_mul_pow_eq_zero V d fun k => (hsum k).symm.trans (h k)
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := S.image g)
    (fun a ha => Finset.mem_image_of_mem _ ha)]
  refine Finset.sum_eq_zero fun w hw => ?_
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 hw
  have hfilter : (S.filter fun a => g a = g a₀) = S.filter fun a => g a ^ q = g a₀ ^ q := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [h2]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hq _ _ h2⟩
  calc ∑ a ∈ S with g a = g a₀, c a * g a = (∑ a ∈ S with g a = g a₀, c a) * g a₀ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [(Finset.mem_filter.1 ha).2]
    _ = d (g a₀ ^ q) * g a₀ := by rw [hfilter]
    _ = 0 := by rw [hd _ (Finset.mem_image_of_mem _ ha₀), zero_mul]

end Grouping

section Closure

variable {K : Type u} [Field K] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
  {E : Fin r → Matrix n n K} (hE : CompleteOrthogonalIdempotents E)
include hE

/-- The generic point `∑ X i • E i` of the block-scalar torus, over Laurent polynomials. -/
def laurentPoint : GL n (Laurent K r) := diagHom hE (Laurent K r) genericUnit

theorem evalLaurent_comp_classify (t : Fin r → Kˣ) :
    (evalLaurent t).comp (classify (R := K) (laurentPoint hE)) =
      classify (R := K) (diagHom hE K t) := by
  rw [← classify_map, laurentPoint, map_diagHom]
  congr 2
  funext i
  exact evalLaurent_genericUnit t i

/-- **Closure under `q`-th roots (positive characteristic form).** If every power of the
block-scalar point with eigenvalues `lam ^ q` kills an ideal of the coordinate ring of `GL_n`,
and `x ↦ x ^ q` is injective, then the point with eigenvalues `lam` kills it. -/
theorem classify_diagHom_eq_zero_of_pow {I : Ideal (CoordinateRing n K)} {lam : Fin r → Kˣ}
    {q : ℕ} (hq : ∀ x y : K, x ^ q = y ^ q → x = y)
    (h : ∀ k : ℕ, ∀ f ∈ I, classify (R := K) (diagHom hE K ((lam ^ q) ^ k)) f = 0) :
    ∀ f ∈ I, classify (R := K) (diagHom hE K lam) f = 0 := by
  intro f hf
  set ℓ := classify (R := K) (laurentPoint hE) f
  have hev : ∀ t, evalLaurent t ℓ = classify (R := K) (diagHom hE K t) f := fun t => by
    rw [← evalLaurent_comp_classify hE t]
    rfl
  rw [← hev, evalLaurent_eq_sum lam ℓ subset_rfl]
  refine sum_mul_eq_zero_of_pow (g := fun a => (charHom lam (Multiplicative.ofAdd a) : K)) hq
    fun k => ?_
  have hk := h k f hf
  rw [← hev, evalLaurent_eq_sum _ ℓ subset_rfl] at hk
  rw [← hk]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [charHom_pow, charHom_pow]
  push_cast
  rfl

end Closure

section Binomial

variable {K : Type u} [Field K]

/-- The binomial polynomial `X (X - 1) ⋯ (X - i + 1) / i!`. -/
def binomPoly (i : ℕ) : K[X] := C ((i.factorial : K)⁻¹) * descPochhammer K i

theorem binomPoly_eval_natCast [CharZero K] (i k : ℕ) :
    (binomPoly i).eval (k : K) = (k.choose i : K) := by
  rw [binomPoly, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)), one_mul]

theorem binomPoly_eval_zero (i : ℕ) : (binomPoly i).eval (0 : K) = if i = 0 then 1 else 0 := by
  rw [binomPoly, eval_mul, eval_C, descPochhammer_eval_zero]
  split_ifs with h <;> simp [h]

theorem binomPoly_zero : (binomPoly 0 : K[X]) = 1 := by
  simp [binomPoly]

end Binomial

section Unipotent

variable {K : Type u} [Field K] {n : Type} [Fintype n] [DecidableEq n]

/-- The polynomial matrix `∑_{i ≤ m} binom(X, i) N ^ i`, interpolating `(1 + N) ^ k`. -/
def binomMatrix (N : Matrix n n K) (m : ℕ) : Matrix n n K[X] :=
  ∑ i ∈ Finset.range (m + 1), (binomPoly i : K[X]) • (C : K →+* K[X]).mapMatrix (N ^ i)

theorem aeval_mapMatrix_binomMatrix (N : Matrix n n K) (m : ℕ) (τ : K) :
    (aeval τ : K[X] →ₐ[K] K).toRingHom.mapMatrix (binomMatrix N m) =
      ∑ i ∈ Finset.range (m + 1), (binomPoly i).eval τ • N ^ i := by
  ext a b
  simp only [binomMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, map_sum, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    coe_aeval_eq_eval, eval_C, eval_mul]

theorem sum_binomPoly_eval_natCast [CharZero K] {N : Matrix n n K} {m : ℕ}
    (hN : N ^ (m + 1) = 0) (k : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (binomPoly i).eval (k : K) • N ^ i = (1 + N) ^ k := by
  have hbin : (1 + N) ^ k = ∑ i ∈ Finset.range (k + 1), (k.choose i : K) • N ^ i := by
    rw [add_comm, (Commute.one_right N).add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_pow, mul_one, ← Nat.cast_comm, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  rw [hbin]
  simp only [binomPoly_eval_natCast]
  have hsub1 : Finset.range (m + 1) ⊆ Finset.range (m + k + 2) :=
    Finset.range_subset_range.2 (by omega)
  have hsub2 : Finset.range (k + 1) ⊆ Finset.range (m + k + 2) :=
    Finset.range_subset_range.2 (by omega)
  rw [Finset.sum_subset hsub1, Finset.sum_subset hsub2]
  · intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]
  · intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    rw [pow_eq_zero_of_le hi hN, smul_zero]

theorem sum_binomPoly_eval_zero (N : Matrix n n K) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (binomPoly i).eval (0 : K) • N ^ i = 1 := by
  rw [Finset.sum_eq_single 0]
  · simp [binomPoly_eval_zero]
  · intro i _ hi
    simp [binomPoly_eval_zero, hi]
  · simp

theorem isUnit_binomMatrix {N : Matrix n n K} {m : ℕ} (hN : N ^ (m + 1) = 0) :
    IsUnit (binomMatrix N m) := by
  set N' : Matrix n n K[X] := (C : K →+* K[X]).mapMatrix N with hN'
  have hpow : ∀ i, (C : K →+* K[X]).mapMatrix (N ^ i) = N' ^ i := fun i => map_pow _ _ _
  have hsplit : binomMatrix N m =
      1 + N' * ∑ i ∈ Finset.range m, (binomPoly (i + 1) : K[X]) • N' ^ i := by
    rw [binomMatrix, Finset.sum_range_succ', binomPoly_zero, hpow 0, pow_zero, one_smul,
      add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpow, mul_smul_comm, pow_succ']
  have hnil : IsNilpotent N' := ⟨m + 1, by rw [← hpow, hN, map_zero]⟩
  have hcomm : Commute N' (∑ i ∈ Finset.range m, (binomPoly (i + 1) : K[X]) • N' ^ i) :=
    Commute.sum_right _ _ _ fun i _ => ((Commute.refl N').pow_right i).smul_right _
  rw [hsplit]
  exact (hcomm.isNilpotent_mul_right hnil).isUnit_one_add

end Unipotent

section GroupingZero

variable {K : Type u} [Field K] {A : Type*}

/-- Grouping a vanishing exponential-polynomial sum by the values of `g` gives the vanishing of
the sum at `g` for every value of the polynomial variable. -/
theorem sum_mul_eval_eq_zero [CharZero K] {S : Finset A} {g : A → K} (hg : ∀ a, g a ≠ 0)
    {Q : A → K[X]}
    (h : ∀ k : ℕ, ∑ a ∈ S, g a ^ k * (Q a).eval (k : K) = 0) (τ : K) :
    ∑ a ∈ S, g a * (Q a).eval τ = 0 := by
  classical
  set V := S.image g with hVdef
  let R : K → K[X] := fun v => ∑ a ∈ S with g a = v, Q a
  have hsum : ∀ (x : K) (j : ℕ), ∑ a ∈ S, g a ^ j * (Q a).eval x =
      ∑ v ∈ V, v ^ j * (R v).eval x := by
    intro x j
    rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := V)
      (fun a ha => Finset.mem_image_of_mem _ ha)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.1 ha).2]
  have hR : ∀ v ∈ V, R v = 0 := eq_zero_of_finset_sum_pow_mul_eval_eq_zero V R
    (fun v hv => by
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hv
      exact hg a)
    fun k => (hsum (k : K) k).symm.trans (h k)
  have h1 := hsum τ 1
  simp only [pow_one] at h1
  rw [h1]
  exact Finset.sum_eq_zero fun v hv => by rw [hR v hv, eval_zero, mul_zero]

end GroupingZero

section ClosureZero

variable {K : Type u} [Field K] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

/-- Evaluation of polynomials over Laurent polynomials at `(t, τ)`. -/
def evalLX (t : Fin r → Kˣ) (τ : K) : (Laurent K r)[X] →ₐ[K] K :=
  (aeval τ).comp (mapAlgHom (evalLaurent t))

theorem evalLX_C (t : Fin r → Kˣ) (τ : K) (ℓ : Laurent K r) :
    evalLX t τ (C ℓ) = evalLaurent t ℓ := by
  simp [evalLX]

theorem evalLX_map_algebraMap (t : Fin r → Kˣ) (τ : K) (p : K[X]) :
    evalLX t τ (p.map (algebraMap K (Laurent K r))) = aeval τ p := by
  simp [evalLX, Polynomial.map_map]

/-- The support of all coefficients of a polynomial over Laurent polynomials. -/
def lxSupport (ℓ : (Laurent K r)[X]) : Finset (Fin r → ℤ) :=
  ℓ.support.biUnion fun j => (ℓ.coeff j).coeff.support

/-- The polynomial coefficient of the Laurent monomial `a`. -/
def lxCoeffPoly (ℓ : (Laurent K r)[X]) (a : Fin r → ℤ) : K[X] :=
  ∑ j ∈ ℓ.support, monomial j ((ℓ.coeff j).coeff a)

theorem evalLX_eq_sum (t : Fin r → Kˣ) (τ : K) (ℓ : (Laurent K r)[X]) :
    evalLX t τ ℓ = ∑ a ∈ lxSupport ℓ,
      (charHom t (Multiplicative.ofAdd a) : K) * (lxCoeffPoly ℓ a).eval τ := by
  have h1 : evalLX t τ ℓ = ∑ j ∈ ℓ.support, evalLaurent t (ℓ.coeff j) * τ ^ j := by
    have hmap : (mapAlgHom (evalLaurent t)) ℓ = ℓ.map (evalLaurent t : Laurent K r →+* K) := rfl
    rw [evalLX, AlgHom.comp_apply, hmap, coe_aeval_eq_eval, eval_map, eval₂_eq_sum,
      Polynomial.sum_def]
    rfl
  have h2 : ∀ j ∈ ℓ.support, evalLaurent t (ℓ.coeff j) = ∑ a ∈ lxSupport ℓ,
      (ℓ.coeff j).coeff a * (charHom t (Multiplicative.ofAdd a) : K) := fun j hj =>
    evalLaurent_eq_sum t _ (Finset.subset_biUnion_of_mem (fun j => (ℓ.coeff j).coeff.support) hj)
  rw [h1, Finset.sum_congr rfl fun j hj => by rw [h2 j hj], ]
  simp only [lxCoeffPoly, eval_finsetSum, eval_monomial, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {E : Fin r → Matrix n n K} (hE : CompleteOrthogonalIdempotents E)
include hE

/-- The point `(∑ X i • E i) U` over polynomials in `τ` with Laurent coefficients. -/
def laurentPolyPoint (U : GL n K[X]) : GL n (Laurent K r)[X] :=
  diagHom hE (Laurent K r)[X]
      (fun i => Units.map (C : Laurent K r →+* (Laurent K r)[X]).toMonoidHom (genericUnit i)) *
    Matrix.GeneralLinearGroup.map (mapRingHom (algebraMap K (Laurent K r))) U

theorem evalLX_comp_classify (U : GL n K[X]) (t : Fin r → Kˣ) (τ : K) :
    (evalLX t τ).comp (classify (R := K) (laurentPolyPoint hE U)) =
      classify (R := K) (diagHom hE K t *
        Matrix.GeneralLinearGroup.map (aeval τ : K[X] →ₐ[K] K).toRingHom U) := by
  rw [← classify_map, laurentPolyPoint, map_mul, map_diagHom]
  refine congrArg _ (congrArg₂ (· * ·) (congrArg _ (funext fun i => ?_)) ?_)
  · apply Units.ext
    rw [← evalLaurent_genericUnit t i]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    exact evalLX_C t τ _
  · apply Units.ext
    ext a b
    simp only [Matrix.GeneralLinearGroup.map_apply, coe_mapRingHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    exact evalLX_map_algebraMap t τ _

/-- **Closure under unipotent parts (characteristic zero form).** If, for a unipotent `u`, the
points `D(lam) ^ k u ^ k` all kill an ideal of the coordinate ring of `GL_n`, then the
block-scalar point `D(lam)` kills it. -/
theorem classify_diagHom_eq_zero_of_unipotent [CharZero K] {I : Ideal (CoordinateRing n K)}
    {lam : Fin r → Kˣ} (u : GL n K) {m : ℕ} (hm : ((u : Matrix n n K) - 1) ^ (m + 1) = 0)
    (h : ∀ k : ℕ, ∀ f ∈ I, classify (R := K) (diagHom hE K (lam ^ k) * u ^ k) f = 0) :
    ∀ f ∈ I, classify (R := K) (diagHom hE K lam) f = 0 := by
  set N := (u : Matrix n n K) - 1 with hNdef
  let U : GL n K[X] := (isUnit_binomMatrix hm).unit
  have hUval : (U : Matrix n n K[X]) = binomMatrix N m := rfl
  have hUk : ∀ k : ℕ,
      Matrix.GeneralLinearGroup.map (aeval (k : K) : K[X] →ₐ[K] K).toRingHom U = u ^ k := by
    intro k
    apply Units.ext
    change (aeval (k : K) : K[X] →ₐ[K] K).toRingHom.mapMatrix (U : Matrix n n K[X]) = _
    rw [hUval, aeval_mapMatrix_binomMatrix, sum_binomPoly_eval_natCast hm, hNdef, add_sub_cancel,
      Units.val_pow_eq_pow_val]
  have hU0 : Matrix.GeneralLinearGroup.map (aeval (0 : K) : K[X] →ₐ[K] K).toRingHom U = 1 := by
    apply Units.ext
    change (aeval (0 : K) : K[X] →ₐ[K] K).toRingHom.mapMatrix (U : Matrix n n K[X]) = _
    rw [hUval, aeval_mapMatrix_binomMatrix, sum_binomPoly_eval_zero, Units.val_one]
  intro f hf
  set ℓ := classify (R := K) (laurentPolyPoint hE U) f
  have hev : ∀ t τ, evalLX t τ ℓ = classify (R := K) (diagHom hE K t *
      Matrix.GeneralLinearGroup.map (aeval τ : K[X] →ₐ[K] K).toRingHom U) f := fun t τ => by
    rw [← evalLX_comp_classify hE U t τ]
    rfl
  have key := sum_mul_eval_eq_zero (S := lxSupport ℓ)
    (g := fun a => (charHom lam (Multiplicative.ofAdd a) : K)) (fun a => Units.ne_zero _)
    (Q := lxCoeffPoly ℓ) (fun k => ?_) 0
  · rw [← evalLX_eq_sum, hev, hU0, mul_one] at key
    exact key
  · have hk := h k f hf
    rw [← hUk, ← hev, evalLX_eq_sum] at hk
    rw [← hk]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [charHom_pow]
    push_cast
    rfl

end ClosureZero

end Langlands.BruhatTits.RationalPoints.CentralNormKernel
