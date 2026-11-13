import Mathlib

/-!
# Frobenius independence modulo an absolutely irreducible plane curve

Schmidt, *Zur Methode von Stepanov* (1973), Hilfssatz 3 (printed p. 350), in the form needed for
the Stepanov method.  A bivariate polynomial is represented as `fh : F[X][Y]`
(`Polynomial (Polynomial F)`, outer variable `Y`).
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

open Polynomial

namespace FrobIndep

/-! ### Degree boxes -/

section Boxes

variable {F : Type*} [CommRing F]

/-- Bivariate polynomials of `Y`-degree at most `b` whose coefficients have `X`-degree at most
`a`. -/
def boxXY (a b : ℕ) : AddSubgroup (Polynomial (Polynomial F)) where
  carrier := {p | p.natDegree ≤ b ∧ ∀ i, (p.coeff i).natDegree ≤ a}
  add_mem' := by
    rintro p p' ⟨hp, hp'⟩ ⟨hq, hq'⟩
    refine ⟨natDegree_add_le_of_degree_le hp hq, fun i => ?_⟩
    rw [coeff_add]
    exact natDegree_add_le_of_degree_le (hp' i) (hq' i)
  zero_mem' := ⟨by simp, fun i => by simp⟩
  neg_mem' := by
    rintro p ⟨hp, hp'⟩
    exact ⟨by rwa [natDegree_neg], fun i => by rw [coeff_neg, natDegree_neg]; exact hp' i⟩

lemma mem_boxXY {a b : ℕ} {p : Polynomial (Polynomial F)} :
    p ∈ boxXY a b ↔ p.natDegree ≤ b ∧ ∀ i, (p.coeff i).natDegree ≤ a := Iff.rfl

lemma C_mem_boxXY {a b : ℕ} {p : Polynomial F} (hp : p.natDegree ≤ a) :
    (C p : Polynomial (Polynomial F)) ∈ boxXY a b := by
  refine ⟨by simp, fun i => ?_⟩
  rw [coeff_C]
  split_ifs
  · exact hp
  · simp

lemma mul_mem_boxXY {a b a' b' : ℕ} {p p' : Polynomial (Polynomial F)} (hp : p ∈ boxXY a b)
    (hp' : p' ∈ boxXY a' b') : p * p' ∈ boxXY (a + a') (b + b') := by
  refine ⟨natDegree_mul_le.trans (add_le_add hp.1 hp'.1), fun i => ?_⟩
  rw [coeff_mul]
  refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  exact natDegree_mul_le.trans (add_le_add (hp.2 _) (hp'.2 _))

/-- Polynomials in a third variable `Z` all of whose coefficients lie in `boxXY a b`. -/
def boxZ (a b : ℕ) : AddSubgroup (Polynomial (Polynomial (Polynomial F))) where
  carrier := {p | ∀ j, p.coeff j ∈ boxXY a b}
  add_mem' := fun hp hq j => by rw [coeff_add]; exact add_mem (hp j) (hq j)
  zero_mem' := fun j => by rw [coeff_zero]; exact zero_mem _
  neg_mem' := fun hp j => by rw [coeff_neg]; exact neg_mem (hp j)

lemma mem_boxZ {a b : ℕ} {p : Polynomial (Polynomial (Polynomial F))} :
    p ∈ boxZ a b ↔ ∀ j, p.coeff j ∈ boxXY a b := Iff.rfl

lemma one_mem_boxZ : (1 : Polynomial (Polynomial (Polynomial F))) ∈ boxZ 0 0 := by
  intro j
  rw [coeff_one]
  split_ifs
  · exact C_mem_boxXY (by simp)
  · exact zero_mem _

lemma mul_mem_boxZ {a b a' b' : ℕ} {p p' : Polynomial (Polynomial (Polynomial F))}
    (hp : p ∈ boxZ a b) (hp' : p' ∈ boxZ a' b') : p * p' ∈ boxZ (a + a') (b + b') := by
  intro j
  rw [coeff_mul]
  exact sum_mem fun x _ => mul_mem_boxXY (hp _) (hp' _)

lemma C_mul_X_pow_mem_boxZ {a b : ℕ} {p : Polynomial (Polynomial F)} (hp : p ∈ boxXY a b)
    (j : ℕ) : C p * X ^ j ∈ boxZ a b := by
  intro i
  rw [coeff_C_mul_X_pow]
  split_ifs
  · exact hp
  · exact zero_mem _

lemma prod_mem_boxZ {ι : Type*} (s : Finset ι) (g : ι → Polynomial (Polynomial (Polynomial F)))
    (a b : ι → ℕ) (h : ∀ i ∈ s, g i ∈ boxZ (a i) (b i)) :
    ∏ i ∈ s, g i ∈ boxZ (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_boxZ
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.sum_insert hx]
    exact mul_mem_boxZ (h x (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma det_mem_boxZ {k : ℕ} (M : Matrix (Fin k) (Fin k) (Polynomial (Polynomial (Polynomial F))))
    (a b : Fin k → ℕ) (h : ∀ i j, M i j ∈ boxZ (a j) (b j)) :
    M.det ∈ boxZ (∑ j, a j) (∑ j, b j) := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem_boxZ _ _ _ _ fun i _ => h (σ i) i) _

/-- Degree box for a resultant, read off from the Sylvester matrix (`sylvester f g m n` has `m`
columns of coefficients of `g` and `n` columns of coefficients of `f`). -/
lemma resultant_mem_boxZ (f g : Polynomial (Polynomial (Polynomial (Polynomial F))))
    (m n af bf ag bg : ℕ) (hf : ∀ k, f.coeff k ∈ boxZ af bf) (hg : ∀ k, g.coeff k ∈ boxZ ag bg) :
    f.resultant g m n ∈ boxZ (m * ag + n * af) (m * bg + n * bf) := by
  have := det_mem_boxZ (sylvester f g m n) (Fin.addCases (fun _ => ag) (fun _ => af))
    (Fin.addCases (fun _ => bg) (fun _ => bf)) ?_
  · simpa [Fin.sum_univ_add, resultant] using this
  · intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hg _
      · exact zero_mem _
    | right j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hf _
      · exact zero_mem _

end Boxes

/-! ### Pseudo-division and base-`q` digits -/

/-- Pseudo-division by `fh` in the outer variable, with control of the inner degrees. -/
lemma exists_pseudoDiv {F : Type*} [CommRing F] (fh : Polynomial (Polynomial F)) (n m : ℕ)
    (hn : 1 ≤ n) (hfn : fh.natDegree ≤ n) (hm : ∀ i, (fh.coeff i).natDegree ≤ m) :
    ∀ (δ D : ℕ) (P : Polynomial (Polynomial F)), P.natDegree ≤ n - 1 + δ →
      (∀ i, (P.coeff i).natDegree ≤ D) →
      ∃ U Rr : Polynomial (Polynomial F), C (fh.coeff n) ^ δ * P = U * fh + Rr ∧
        Rr.natDegree ≤ n - 1 ∧ ∀ i, (Rr.coeff i).natDegree ≤ D + m * δ := by
  intro δ
  induction δ with
  | zero =>
    intro D P hP hPD
    exact ⟨0, P, by simp, by simpa using hP, by simpa using hPD⟩
  | succ δ ih =>
    intro D P hP hPD
    set c := P.coeff (n + δ) with hc
    have hP1deg : (C (fh.coeff n) * P - C c * X ^ δ * fh).natDegree ≤ n - 1 + δ := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_sub, coeff_C_mul, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
      rcases Nat.lt_or_ge (n + δ) k with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k)]
        split_ifs with h'
        · rw [coeff_eq_zero_of_natDegree_lt (by omega : fh.natDegree < k - δ)]; simp
        · simp
      · have hk' : k = n + δ := by omega
        subst hk'
        simp only [show δ ≤ n + δ by omega, ↓reduceIte]
        rw [show n + δ - δ = n by omega, ← hc, mul_comm, sub_self]
    have hP1D : ∀ i, ((C (fh.coeff n) * P - C c * X ^ δ * fh).coeff i).natDegree ≤ D + m := by
      intro i
      rw [coeff_sub, coeff_C_mul, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_mul_le.trans (by have := hm n; have := hPD i; omega)
      · split_ifs
        · have h1 := hPD (n + δ)
          rw [← hc] at h1
          exact natDegree_mul_le.trans (by have := hm (i - δ); omega)
        · simp
    obtain ⟨U, Rr, hUR, hRdeg, hRD⟩ := ih (D + m) _ hP1deg hP1D
    refine ⟨U + C (fh.coeff n) ^ δ * C c * X ^ δ, Rr, ?_, hRdeg, fun i => (hRD i).trans ?_⟩
    · linear_combination hUR
    · rw [Nat.mul_succ]; omega

/-- Base-`q` digits: if `∑ c_j X^(q j) = 0` and every `c_j` has degree `< q`, all `c_j` vanish. -/
lemma eq_zero_of_sum_mul_X_pow_eq_zero {F : Type*} [Semiring F] (q : ℕ) (s : Finset ℕ)
    (c : ℕ → Polynomial F) (hc : ∀ j ∈ s, (c j).natDegree < q)
    (h : ∑ j ∈ s, c j * X ^ (q * j) = 0) : ∀ j ∈ s, c j = 0 := by
  intro j hj
  ext r
  rw [coeff_zero]
  rcases Nat.lt_or_ge r q with hr | hr
  · have := congrArg (fun p => p.coeff (q * j + r)) h
    simp only [finsetSum_coeff, coeff_mul_X_pow', coeff_zero] at this
    rw [Finset.sum_eq_single j] at this
    · simpa using this
    · intro i hi hij
      split_ifs with hle
      · have hci := hc i hi
        rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
        · apply coeff_eq_zero_of_natDegree_lt
          have : q * (i + 1) ≤ q * j := Nat.mul_le_mul_left q hlt
          rw [Nat.mul_succ] at this
          omega
        · exfalso
          have : q * (j + 1) ≤ q * i := Nat.mul_le_mul_left q hgt
          rw [Nat.mul_succ] at this
          omega
      · rfl
    · intro hj'; exact absurd hj hj'
  · exact coeff_eq_zero_of_natDegree_lt ((hc j hj).trans_le hr)

/-! ### Nonvanishing of resultants against an irreducible polynomial -/

/-- If `f ∈ K[Z][W]` is irreducible of positive `W`-degree `n` and `g ≠ 0` has `W`-degree `< n`,
then the resultant of sizes `(n, n - 1)` is nonzero. -/
lemma resultant_ne_zero_of_irreducible {K : Type*} [Field K]
    (f g : Polynomial (Polynomial K)) (hf : Irreducible f) (hn : f.natDegree ≠ 0) (hg : g ≠ 0)
    (hgd : g.natDegree < f.natDegree) : f.resultant g f.natDegree (f.natDegree - 1) ≠ 0 := by
  let L := FractionRing (Polynomial K)
  have hinj : Function.Injective (algebraMap (Polynomial K) L) := IsFractionRing.injective _ _
  have hirrL : Irreducible (f.map (algebraMap (Polynomial K) L)) :=
    ((hf.isPrimitive hn).irreducible_iff_irreducible_map_fraction_map).1 hf
  have hcop : IsCoprime (f.map (algebraMap (Polynomial K) L)) (g.map (algebraMap (Polynomial K) L)) := by
    rw [hirrL.coprime_iff_not_dvd]
    intro hdvd
    have h0 := eq_zero_of_dvd_of_natDegree_lt hdvd (by
      rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj]; exact hgd)
    exact hg ((Polynomial.map_eq_zero_iff hinj).1 h0)
  have hres := resultant_ne_zero _ _ hcop
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
    resultant_map_map] at hres
  have h0 : f.resultant g f.natDegree g.natDegree ≠ 0 := fun h => hres (by rw [h, map_zero])
  obtain ⟨k, hk⟩ : ∃ k, f.natDegree - 1 = g.natDegree + k :=
    ⟨f.natDegree - 1 - g.natDegree, by omega⟩
  rw [hk, resultant_add_right_deg _ _ _ _ k le_rfl]
  exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.2 hf.ne_zero)) h0

/-! ### The auxiliary polynomial `a(X, Y, Z, W) = ∑ B_{jk}(X, Y) Z^j W^k` -/

/-- `∑_{j ≤ N, k < n} B j k · Z^j W^k` in `S[Z][W]`. -/
noncomputable def auxPoly {S : Type*} [CommRing S] (B : ℕ → ℕ → S) (N n : ℕ) :
    Polynomial (Polynomial S) :=
  ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range n, C (C (B j k) * X ^ j) * X ^ k

lemma natDegree_auxPoly_le {S : Type*} [CommRing S] (B : ℕ → ℕ → S) (N n : ℕ) :
    (auxPoly B N n).natDegree ≤ n - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by simp at hk; omega)

lemma auxPoly_map {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T) (B : ℕ → ℕ → S)
    (N n : ℕ) : (auxPoly B N n).map (mapRingHom φ) = auxPoly (fun j k => φ (B j k)) N n := by
  simp [auxPoly, Polynomial.map_sum]

lemma coeff_coeff_auxPoly {S : Type*} [CommRing S] (B : ℕ → ℕ → S) (N n : ℕ) {j k : ℕ}
    (hj : j ≤ N) (hk : k < n) : ((auxPoly B N n).coeff k).coeff j = B j k := by
  simp only [auxPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'; simp [Ne.symm hk']
    · intro h; simp at h; omega
  · intro j' _ hj'
    rw [Finset.sum_eq_single k]
    · simp [Ne.symm hj']
    · intro k' _ hk'; simp [Ne.symm hk']
    · intro h; simp at h; omega
  · intro h; simp at h; omega

lemma evalEval_auxPoly {S : Type*} [CommRing S] (B : ℕ → ℕ → S) (N n : ℕ) (x y : S) :
    (auxPoly B N n).evalEval x y =
      ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range n, B j k * x ^ j * y ^ k := by
  simp [auxPoly, evalEval_finsetSum, evalEval_mul, evalEval_C, evalEval_pow, evalEval_X]

lemma coeff_auxPoly_mem_boxZ {F : Type*} [CommRing F] (B : ℕ → ℕ → Polynomial (Polynomial F))
    (N n a b : ℕ) (hB : ∀ j k, B j k ∈ boxXY a b) (k : ℕ) :
    (auxPoly B N n).coeff k ∈ boxZ a b := by
  simp only [auxPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  refine sum_mem fun j _ => sum_mem fun k' _ => ?_
  split_ifs
  · exact C_mul_X_pow_mem_boxZ (hB _ _) _
  · exact zero_mem _

/-! ### Frobenius -/

lemma evalEval_map_frobenius {F : Type*} [Field F] [Fintype F] (fh : Polynomial (Polynomial F)) :
    (fh.map (mapRingHom (algebraMap F (Polynomial (Polynomial F))))).evalEval
      (C (X ^ Fintype.card F)) (X ^ Fintype.card F) = fh ^ Fintype.card F := by
  have key : (evalEvalRingHom (R := Polynomial (Polynomial F)) (C (X ^ Fintype.card F))
      (X ^ Fintype.card F)).comp
      (mapRingHom (mapRingHom (algebraMap F (Polynomial (Polynomial F))))) =
      (FiniteField.frobeniusAlgHom F (Polynomial (Polynomial F))).toRingHom := by
    ext c
    · simp [← map_pow, FiniteField.pow_card]
    · simp
    · simp
  exact (RingHom.congr_fun key fh).trans (by simp)

end FrobIndep

open FrobIndep in
/-- **Schmidt, Hilfssatz 3** (Frobenius independence).  Let `fh ∈ F[X][Y]` be absolutely
irreducible of `Y`-degree `n ≥ 1` with coefficients of `X`-degree `≤ m`, and let `q = |F|`.  If
`fh` divides `∑_{j ≤ N, k < n} B_{jk}(X, Y) X^{qj} Y^{qk}`, where each `B_{jk}` has `Y`-degree
`< n` and `X`-degree `≤ d`, and `n d + m (n - 1)^2 < q`, then every `B_{jk}` vanishes. -/
theorem frobeniusIndependence
    {F : Type u} [Field F] [Finite F] (fh : Polynomial (Polynomial F)) (m d N : ℕ)
    (hirr : Irreducible (fh.map (Polynomial.mapRingHom (algebraMap F (AlgebraicClosure F)))))
    (hn : 1 ≤ fh.natDegree) (hm : ∀ i, (fh.coeff i).natDegree ≤ m)
    (hd : fh.natDegree * d + m * (fh.natDegree - 1) ^ 2 < Nat.card F)
    (B : ℕ → ℕ → Polynomial (Polynomial F))
    (hBY : ∀ j k, (B j k).natDegree < fh.natDegree)
    (hBX : ∀ j k i, ((B j k).coeff i).natDegree ≤ d)
    (hdvd : fh ∣ ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range fh.natDegree,
        B j k * Polynomial.C (Polynomial.X ^ (Nat.card F * j)) *
          Polynomial.X ^ (Nat.card F * k)) :
    ∀ j ≤ N, ∀ k < fh.natDegree, B j k = 0 := by
  classical
  have := Fintype.ofFinite F
  set n := fh.natDegree with hn_def
  set q := Nat.card F with hq_def
  have hqF : q = Fintype.card F := Nat.card_eq_fintype_card
  have hq0 : 0 < q := Nat.card_pos
  set g0 := fh.coeff n with hg0
  set δ := (n - 1) ^ 2 with hδ
  set fZW : Polynomial (Polynomial (Polynomial (Polynomial F))) :=
    fh.map (mapRingHom (algebraMap F (Polynomial (Polynomial F)))) with hfZW
  set a := auxPoly B N n with ha
  set P := fZW.resultant a n (n - 1) with hP
  -- Step 1: `fh ∣ P(X, Y, X^q)`.
  have h1 : fh ∣ P.eval (C (X ^ q)) := by
    obtain ⟨u, v, -, -, huv⟩ := exists_mul_add_mul_eq_C_resultant fZW a
      (natDegree_map_le.trans le_rfl) (natDegree_auxPoly_le B N n) (Or.inl (by omega))
    have e := congrArg (evalEval (C (X ^ q)) (X ^ q)) huv
    rw [evalEval_add, evalEval_mul, evalEval_mul, evalEval_C, hqF, evalEval_map_frobenius,
      ← hqF, evalEval_auxPoly] at e
    rw [← e]
    refine dvd_add (dvd_mul_of_dvd_left (dvd_pow_self fh hq0.ne') _)
      (dvd_mul_of_dvd_left ?_ _)
    simpa only [pow_mul, map_pow] using hdvd
  -- Step 2: degree box for the `Z`-coefficients of `P`.
  have h2 : ∀ j, P.coeff j ∈ boxXY (n * d) (n * (n - 1)) := by
    have hf' : ∀ k, fZW.coeff k ∈ boxZ 0 0 := by
      intro k j
      rw [hfZW, coeff_map, coe_mapRingHom, coeff_map]
      simpa [Polynomial.algebraMap_apply] using
        (C_mem_boxXY (b := 0) (p := C ((fh.coeff k).coeff j)) (by simp))
    have ha' : ∀ k, a.coeff k ∈ boxZ d (n - 1) :=
      coeff_auxPoly_mem_boxZ B N n d (n - 1) fun j k => ⟨by have := hBY j k; omega, hBX j k⟩
    have := resultant_mem_boxZ fZW a n (n - 1) 0 0 d (n - 1) hf' ha'
    intro j
    simpa using this j
  -- Step 3: reduction modulo `fh` and base-`q` digits.
  have hPdeg : ∀ j, (P.coeff j).natDegree ≤ n - 1 + δ := by
    intro j
    refine (h2 j).1.trans ?_
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [hδ, hk, Nat.add_sub_cancel]
    exact le_of_eq (by ring)
  choose U Rr hUR hRdeg hRX using fun j =>
    exists_pseudoDiv fh n m hn le_rfl hm δ (n * d) (P.coeff j) (hPdeg j) (h2 j).2
  have hT : fh ∣ ∑ j ∈ Finset.range (P.natDegree + 1), Rr j * C (X ^ q) ^ j := by
    have e : C g0 ^ δ * P.eval (C (X ^ q)) =
        (∑ j ∈ Finset.range (P.natDegree + 1), U j * C (X ^ q) ^ j) * fh +
          ∑ j ∈ Finset.range (P.natDegree + 1), Rr j * C (X ^ q) ^ j := by
      rw [eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, hUR j]
      ring
    have e' : ∑ j ∈ Finset.range (P.natDegree + 1), Rr j * C (X ^ q) ^ j =
        C g0 ^ δ * P.eval (C (X ^ q)) -
          (∑ j ∈ Finset.range (P.natDegree + 1), U j * C (X ^ q) ^ j) * fh := by
      rw [e]; ring
    rw [e']
    exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_left _ _)
  have hT0 : ∑ j ∈ Finset.range (P.natDegree + 1), Rr j * C (X ^ q) ^ j = 0 := by
    refine eq_zero_of_dvd_of_natDegree_lt hT (lt_of_le_of_lt
      (natDegree_sum_le_of_forall_le (n := n - 1) _ _ fun j _ => ?_) (by omega))
    rw [← map_pow]
    exact (natDegree_mul_C_le _ _).trans (hRdeg j)
  have hR0 : ∀ j ∈ Finset.range (P.natDegree + 1), Rr j = 0 := by
    intro j hj
    ext i : 1
    have hi := congrArg (fun p => p.coeff i) hT0
    simp only [finsetSum_coeff, ← map_pow, coeff_mul_C, coeff_zero] at hi
    rw [coeff_zero]
    refine eq_zero_of_sum_mul_X_pow_eq_zero q _ (fun j => (Rr j).coeff i)
      (fun j _ => (hRX j i).trans_lt hd) ?_ j hj
    simpa only [pow_mul] using hi
  have h3 : ∀ j, ∃ V, C g0 ^ δ * P.coeff j = V * fh := by
    intro j
    by_cases hj : j ∈ Finset.range (P.natDegree + 1)
    · exact ⟨U j, by rw [hUR j, hR0 j hj, add_zero]⟩
    · refine ⟨0, ?_⟩
      rw [coeff_eq_zero_of_natDegree_lt (by simp at hj; omega)]
      simp
  -- Step 4: at points of the curve over `F̄`, the auxiliary polynomial vanishes.
  set K := AlgebraicClosure F
  set ι := algebraMap F K
  set fb := fh.map (mapRingHom ι) with hfb
  have hfb_deg : fb.natDegree = n :=
    natDegree_map_eq_of_injective (Polynomial.map_injective ι ι.injective) fh
  have hfh0 : fh ≠ 0 := by
    intro h
    have : n = 0 := by rw [hn_def, h, natDegree_zero]
    omega
  have hg0ne : g0 ≠ 0 := leadingCoeff_ne_zero.2 hfh0
  let ev (x0 y0 : K) : Polynomial (Polynomial F) →+* K :=
    (evalEvalRingHom x0 y0).comp (mapRingHom (mapRingHom ι))
  have hev (x0 y0 : K) (p : Polynomial (Polynomial F)) :
      ev x0 y0 p = (p.map (mapRingHom ι)).evalEval x0 y0 := rfl
  have h4 : ∀ x0 y0 : K, (g0.map ι).eval x0 ≠ 0 → fb.evalEval x0 y0 = 0 →
      ∀ j ≤ N, ∀ k < n, ev x0 y0 (B j k) = 0 := by
    intro x0 y0 hg hf j hj k hk
    have hPj : ∀ j, ev x0 y0 (P.coeff j) = 0 := by
      intro j
      obtain ⟨V, hV⟩ := h3 j
      have := congrArg (ev x0 y0) hV
      rw [map_mul, map_mul, hev x0 y0 fh, ← hfb, hf, mul_zero, map_pow] at this
      refine (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ ?_)
      rw [hev]; simpa [evalEval_C] using hg
    have hΦP : P.map (ev x0 y0) = 0 := by
      ext j; simp [coeff_map, hPj]
    have e1 : fZW.map (mapRingHom (ev x0 y0)) = fb := by
      rw [hfZW, Polynomial.map_map, mapRingHom_comp]
      congr 2
      ext c
      simp [hev]
    have hres : fb.resultant (auxPoly (fun j k => ev x0 y0 (B j k)) N n) n (n - 1) = 0 := by
      rw [← e1, ← auxPoly_map,
        resultant_map_map fZW (auxPoly B N n) n (n - 1) (mapRingHom (ev x0 y0))]
      change (mapRingHom (ev x0 y0)) P = 0
      rw [coe_mapRingHom, hΦP]
    by_contra hne
    have ha0 : auxPoly (fun j k => ev x0 y0 (B j k)) N n ≠ 0 := by
      intro h0
      apply hne
      rw [← coeff_coeff_auxPoly (fun j k => ev x0 y0 (B j k)) N n hj hk, h0]
      simp
    refine resultant_ne_zero_of_irreducible fb _ hirr (by omega) ha0 ?_ (by rwa [hfb_deg])
    rw [hfb_deg]
    exact (natDegree_auxPoly_le _ N n).trans_lt (by omega)
  -- Step 5: conclusion via `Res_Y(fb, B_jk)`.
  intro j hj k hk
  by_contra hB
  set b := (B j k).map (mapRingHom ι) with hb
  have hb0 : b ≠ 0 := (Polynomial.map_ne_zero_iff (Polynomial.map_injective ι ι.injective)).2 hB
  have hbdeg : b.natDegree < fb.natDegree := by
    rw [hfb_deg]; exact natDegree_map_le.trans_lt (hBY j k)
  have hR := resultant_ne_zero_of_irreducible fb b hirr (by omega) hb0 hbdeg
  apply hR
  set g0b := g0.map ι with hg0b
  have hg0b0 : g0b ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).2 hg0ne
  have hprod : fb.resultant b fb.natDegree (fb.natDegree - 1) * g0b = 0 := by
    apply Polynomial.funext
    intro x0
    rw [eval_mul, eval_zero]
    by_cases hx : g0b.eval x0 = 0
    · rw [hx, mul_zero]
    · refine mul_eq_zero_of_left ?_ _
      set p0 := fb.map (evalRingHom x0) with hp0
      set b0 := b.map (evalRingHom x0) with hb0'
      have hp0c : p0.coeff n = g0b.eval x0 := by
        rw [hp0, coeff_map, hfb, coeff_map, coe_evalRingHom, coe_mapRingHom]
      have hp0deg : p0.natDegree = n :=
        natDegree_eq_of_le_of_coeff_ne_zero (natDegree_map_le.trans hfb_deg.le)
          (by rw [hp0c]; exact hx)
      have hp0ne : p0 ≠ 0 := by
        intro h; rw [h] at hp0deg; simp at hp0deg; omega
      have e := resultant_map_map fb b fb.natDegree (fb.natDegree - 1) (evalRingHom x0)
      rw [← coe_evalRingHom, ← e, hfb_deg, ← hp0, ← hb0', ← hp0deg,
        resultant_eq_prod_eval p0 b0 (p0.natDegree - 1)
          (natDegree_map_le.trans (by rw [hp0deg]; omega)) (IsAlgClosed.splits p0)]
      obtain ⟨y0, hy0⟩ := IsAlgClosed.exists_root p0
        (by rw [degree_eq_natDegree hp0ne, hp0deg]; exact_mod_cast (by omega : n ≠ 0))
      have hfy : fb.evalEval x0 y0 = 0 := by
        rw [← map_evalRingHom_eval, ← hp0]; exact hy0
      have hBy : b0.eval y0 = 0 := by
        rw [hb0', map_evalRingHom_eval, ← hev]
        exact h4 x0 y0 hx hfy j hj k hk
      refine mul_eq_zero_of_right _ (Multiset.prod_eq_zero (Multiset.mem_map.2
        ⟨y0, (mem_roots hp0ne).2 hy0, hBy⟩))
  exact (mul_eq_zero.1 hprod).resolve_right hg0b0

end Langlands.AlgebraicGeometry.LangWeil.Stepanov
