import Langlands.GroupScheme.Dynamic.GeneralLinearWeightComponents
import Langlands.GroupScheme.Dynamic.GeneralLinearCellBlock
import Langlands.GroupScheme.Dynamic.GeneralLinearTranslation
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.Polynomial.Basic

/-! # Closed subgroups of `GL_n` and the opposite cell

Let `k` be a field and `J` an ideal of the polynomial ring `k[x_{ij}, y_{ij}]` of the coordinates
of `GL_n` containing the ideal of `GL_n`. Suppose that the common zeros `Z(S)` of `J` in `GL_n(S)`
are closed under multiplication for every `k`-algebra `S`, contain `1`, and contain the diagonal
matrix `diag(T ^ e i)` over `k[T, T⁻¹]`. If `v q ∈ Z(S)` with `v` block unipotent for `-e` and
`q` block parabolic for `e`, then `q ∈ Z(S)`.

The proof is the stabilizer argument of Conrad–Gabber–Prasad, Proposition 2.1.8(3), with the
line stabilizer replaced by the stabilizer of the subspace `W = J ∩ F_d` of polynomials of total
degree at most `d` and the block lemma of `GeneralLinearCellBlock`.
-/

noncomputable section

universe u

open Matrix MvPolynomial

namespace Langlands.GroupScheme.GeneralLinear

section Pivot

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

variable (K) in
/-- The vectors vanishing outside a finite set of indices. -/
def coordinateSubspace (s : Finset ι) : Submodule K (ι → K) where
  carrier := {c | ∀ i, i ∉ s → c i = 0}
  add_mem' {a b} ha hb i hi := by
    change a i + b i = 0
    rw [ha i hi, hb i hi, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r c hc i hi := by
    change r • c i = 0
    rw [hc i hi, smul_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem mem_coordinateSubspace {s : Finset ι} {c : ι → K} :
    c ∈ coordinateSubspace K s ↔ ∀ i, i ∉ s → c i = 0 :=
  Iff.rfl

/-- **Pivot coordinates for a graded subspace.** If `W` contains the weight components of its
vectors, there are a set `s` of non-pivot indices and a matrix `N` with entries only from the
pivot columns to the non-pivot rows, and only within a weight, such that the pivot columns of
`1 + N` lie in `W` and `(1 - N) c` vanishes at the non-pivot indices for every `c ∈ W`. -/
theorem exists_pivot (a : ι → ℤ) (W : Submodule K (ι → K))
    (hW : ∀ c ∈ W, ∀ w : ℤ, weightPart a w c ∈ W) :
    ∃ (s : Finset ι) (N : Matrix ι ι K), (∀ i j, N i j ≠ 0 → i ∈ s ∧ j ∉ s) ∧
      (∀ i j, a i ≠ a j → N i j = 0) ∧ (∀ j, j ∉ s → (fun i => (1 + N) i j) ∈ W) ∧
      (∀ c ∈ W, ∀ i ∈ s, ((1 - N) *ᵥ c) i = 0) := by
  classical
  -- a set `s` of maximal cardinality with `W ⊓ C(s) = ⊥`
  have hne : (Finset.univ.filter fun s : Finset ι =>
      W ⊓ coordinateSubspace K s = ⊥).Nonempty := by
    refine ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, eq_bot_iff.2 fun c hc => ?_⟩⟩
    exact (Submodule.mem_bot K).2 (funext fun i =>
      (Submodule.mem_inf.1 hc).2 i (Finset.notMem_empty i))
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  have hdisj : ∀ c ∈ W, c ∈ coordinateSubspace K s → c = 0 := fun c hcW hcC =>
    (Submodule.mem_bot K).1 (by
      rw [← (Finset.mem_filter.1 hs).2]
      exact Submodule.mem_inf.2 ⟨hcW, hcC⟩)
  -- every standard basis vector is in `W + C(s)`
  have hspan : ∀ j, ∃ w ∈ W, ∃ c ∈ coordinateSubspace K s, w + c = Pi.single j 1 := by
    intro j
    by_cases hj : j ∈ s
    · refine ⟨0, W.zero_mem, Pi.single j 1, fun i hi => ?_, zero_add _⟩
      exact Pi.single_eq_of_ne (fun h => hi (by rw [h]; exact hj)) 1
    · have hbig : ¬ (W ⊓ coordinateSubspace K (insert j s) = ⊥) := by
        intro h
        have := hmax (insert j s) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
        rw [Finset.card_insert_of_notMem hj] at this
        omega
      obtain ⟨v, hv, hv0⟩ := Submodule.ne_bot_iff _ |>.1 hbig
      obtain ⟨hvW, hvC⟩ := Submodule.mem_inf.1 hv
      have hvj : v j ≠ 0 := by
        intro hvj
        refine hv0 (hdisj v hvW fun i hi => ?_)
        by_cases hij : i = j
        · rw [hij, hvj]
        · exact hvC i (by simp [hij, hi])
      refine ⟨(v j)⁻¹ • v, W.smul_mem _ hvW, Pi.single j 1 - (v j)⁻¹ • v, fun i hi => ?_,
        add_sub_cancel _ _⟩
      by_cases hij : i = j
      · subst hij
        simp [hvj]
      · rw [Pi.sub_apply, Pi.single_eq_of_ne hij, Pi.smul_apply,
          hvC i (by simp [hij, hi]), smul_zero, sub_zero]
  choose w hwW c hcC hwc using hspan
  -- the vectors `w j` have the weight of `j`
  have hhom : ∀ j i, a i ≠ a j → w j i = 0 := by
    intro j i hij
    have hw' := hW _ (hwW j) (a j)
    have hc' : weightPart a (a j) (c j) ∈ coordinateSubspace K s := fun i' hi' => by
      simp only [weightPart]
      split_ifs
      · exact hcC j i' hi'
      · rfl
    have hsum : weightPart a (a j) (w j) + weightPart a (a j) (c j) = w j + c j := by
      rw [← weightPart_add, hwc]
      funext i'
      simp only [weightPart]
      split_ifs with h
      · rfl
      · rw [Pi.single_apply, ite_eq_right (fun h' : i' = j => h (by rw [h']))]
    have h0 : w j - weightPart a (a j) (w j) = 0 := by
      refine hdisj _ (W.sub_mem (hwW j) hw') ?_
      have : w j - weightPart a (a j) (w j) = weightPart a (a j) (c j) - c j := by
        rw [sub_eq_sub_iff_add_eq_add, ← hsum, add_comm]
      rw [this]
      exact (coordinateSubspace K s).sub_mem hc' (hcC j)
    have := congrFun h0 i
    simp only [Pi.sub_apply, weightPart, ite_eq_right hij, sub_zero, Pi.zero_apply] at this
    exact this
  -- `w j i = δ_{ij}` for non-pivot... coordinates outside `s`
  have hwout : ∀ j i, i ∉ s → w j i = (1 : Matrix ι ι K) i j := by
    intro j i hi
    have := congrFun (hwc j) i
    rw [Pi.add_apply, hcC j i hi, add_zero] at this
    rw [this, Pi.single_apply, Matrix.one_apply]
  refine ⟨s, Matrix.of fun i j => if j ∈ s then 0 else w j i - (1 : Matrix ι ι K) i j,
    fun i j hN => ?_, fun i j hij => ?_, fun j hj => ?_, fun x hx i hi => ?_⟩
  · simp only [Matrix.of_apply] at hN
    split_ifs at hN with hj
    · exact absurd rfl hN
    · refine ⟨?_, hj⟩
      by_contra hi
      rw [hwout j i hi, sub_self] at hN
      exact hN rfl
  · simp only [Matrix.of_apply]
    split_ifs
    · rfl
    · rw [hhom j i hij, Matrix.one_apply_ne (fun h => hij (by rw [h])), sub_zero]
  · convert hwW j using 1
    funext i
    simp only [Matrix.add_apply, Matrix.of_apply, ite_eq_right hj, add_sub_cancel]
  · -- `x` is the combination of the pivot columns
    set y := x - ∑ j, (if j ∈ s then 0 else x j) • w j with hy
    have hyW : y ∈ W :=
      W.sub_mem hx (W.sum_mem fun j _ => W.smul_mem _ (hwW j))
    have hyC : y ∈ coordinateSubspace K s := by
      intro i' hi'
      rw [hy, Pi.sub_apply, Finset.sum_apply, sub_eq_zero]
      rw [Finset.sum_eq_single i']
      · rw [ite_eq_right hi', Pi.smul_apply, hwout i' i' hi', Matrix.one_apply_eq, smul_eq_mul, mul_one]
      · intro j _ hji
        split_ifs with hj
        · rw [zero_smul, Pi.zero_apply]
        · rw [Pi.smul_apply, hwout j i' hi', Matrix.one_apply_ne (fun h => hji h.symm),
            smul_zero]
      · exact fun h => absurd (Finset.mem_univ i') h
    have hy0 := congrFun (hdisj y hyW hyC) i
    rw [hy, Pi.sub_apply, Finset.sum_apply, Pi.zero_apply, sub_eq_zero] at hy0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero, hy0]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rw [zero_smul, Pi.zero_apply, zero_mul]
    · rw [Matrix.one_apply_ne (fun h => hj (by rw [← h]; exact hi)), sub_zero, Pi.smul_apply, smul_eq_mul,
        mul_comm]

omit [DecidableEq ι] in
/-- A linear functional on `ι → K` in terms of its values on the standard basis. -/
theorem linearMap_apply_eq_sum [DecidableEq ι] (μ : (ι → K) →ₗ[K] K) (c : ι → K) :
    μ c = ∑ i, c i * μ (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ' c]
  simp only [map_sum, map_smul, smul_eq_mul]

end Pivot

variable {n : Type} [Fintype n] [DecidableEq n]

section Coefficients

variable {S : Type*} [CommRing S] (d : ℕ)

/-- The polynomial with prescribed coefficients at the monomials of total degree at most `d`. -/
def ofCoeffs : (Exponent n d → S) →ₗ[S] MvPolynomial (Coordinate n) S :=
  Fintype.linearCombination S fun m => monomial m.1 1

omit [DecidableEq n] in
theorem ofCoeffs_apply (c : Exponent n d → S) : ofCoeffs d c = ∑ m, monomial m.1 (c m) := by
  simp only [ofCoeffs, Fintype.linearCombination_apply, smul_monomial, smul_eq_mul, mul_one]

theorem coeff_ofCoeffs (c : Exponent n d → S) (m : Exponent n d) :
    (ofCoeffs d c).coeff m.1 = c m := by
  rw [ofCoeffs_apply, coeff_sum, Finset.sum_eq_single m]
  · rw [coeff_monomial, ite_eq_left rfl]
  · intro m' _ hm'
    rw [coeff_monomial, ite_eq_right (fun h => hm' (Subtype.ext h))]
  · exact fun h => absurd (Finset.mem_univ m) h

omit [DecidableEq n] in
theorem ofCoeffs_coeff {F : MvPolynomial (Coordinate n) S} (hF : F.totalDegree ≤ d) :
    ofCoeffs d (fun m => F.coeff m.1) = F := by
  rw [ofCoeffs_apply]
  exact (eq_sum_exponent hF).symm

theorem ofCoeffs_single (m : Exponent n d) :
    ofCoeffs d (Pi.single m (1 : S)) = monomial m.1 1 := by
  rw [ofCoeffs, Fintype.linearCombination_apply_single, one_smul]

omit [DecidableEq n] in
theorem totalDegree_ofCoeffs_le (c : Exponent n d → S) : (ofCoeffs d c).totalDegree ≤ d := by
  rw [ofCoeffs_apply]
  exact totalDegree_finsetSum_le fun m _ =>
    (isHomogeneous_monomial (c m) rfl).totalDegree_le.trans m.2

omit [DecidableEq n] in
theorem map_ofCoeffs {S' : Type*} [CommRing S'] (φ : S →+* S') (c : Exponent n d → S) :
    map φ (ofCoeffs d c) = ofCoeffs d (φ ∘ c) := by
  simp only [ofCoeffs_apply, map_sum, map_monomial, Function.comp_apply]

theorem totalDegree_translate_le {F : MvPolynomial (Coordinate n) S} {d : ℕ}
    (hF : F.totalDegree ≤ d) (g : GL n S) : (translate g F).totalDegree ≤ d := by
  rw [eq_sum_exponent hF, map_sum]
  refine totalDegree_finsetSum_le fun m _ => ?_
  rw [show monomial m.1 (F.coeff m.1) = F.coeff m.1 • monomial m.1 (1 : S) by
    rw [smul_monomial, smul_eq_mul, mul_one], map_smul]
  exact (totalDegree_smul_le _ _).trans ((totalDegree_translate_monomial_le g m.1).trans m.2)

end Coefficients

section ZeroLocus

variable {k : Type*} [CommRing k]

variable (S : Type*) [CommRing S] [Algebra k S] in
/-- The invertible matrices over `S` at which all polynomials of `J` vanish. -/
def zeroLocus (J : Ideal (MvPolynomial (Coordinate n) k)) : Set (GL n S) :=
  {g | ∀ f ∈ J, aeval (values g) f = 0}

theorem values_map {S S' : Type*} [CommRing S] [CommRing S'] (φ : S →+* S') (g : GL n S) :
    values (Matrix.GeneralLinearGroup.map φ g) = φ ∘ values g := by
  funext v
  cases v with
  | entry i j => rfl
  | inverseEntry i j =>
    change ((Matrix.GeneralLinearGroup.map φ g)⁻¹ : GL n S') i j = φ (((g⁻¹ : GL n S)) i j)
    rw [← Matrix.GeneralLinearGroup.map_inv, Matrix.GeneralLinearGroup.map_apply]

theorem map_mem_zeroLocus {J : Ideal (MvPolynomial (Coordinate n) k)} {S S' : Type*} [CommRing S]
    [CommRing S'] [Algebra k S] [Algebra k S'] (ψ : S →ₐ[k] S') {g : GL n S}
    (hg : g ∈ zeroLocus S J) : Matrix.GeneralLinearGroup.map ψ.toRingHom g ∈ zeroLocus S' J := by
  intro f hf
  rw [values_map, show (ψ.toRingHom ∘ values g) = fun v => ψ (values g v) from rfl,
    ← comp_aeval_apply, hg f hf, map_zero]

end ZeroLocus

section Functional

variable {k : Type*} [Field k] (d : ℕ) {J : Ideal (MvPolynomial (Coordinate n) k)}

omit [DecidableEq n] in
/-- **Extension of functionals.** A functional on the coefficient vectors of degree at most `d`
which kills the coefficient vectors of the polynomials of `J` is the restriction of a functional
on all polynomials killing `J`. -/
theorem exists_functional_extension (μ : (Exponent n d → k) →ₗ[k] k)
    (hμ : ∀ c, ofCoeffs d c ∈ J → μ c = 0) :
    ∃ ℓ : MvPolynomial (Coordinate n) k →ₗ[k] k, (∀ f ∈ J, ℓ f = 0) ∧
      ∀ c, ℓ (ofCoeffs d c) = μ c := by
  set p := J.restrictScalars k
  set φ := p.mkQ ∘ₗ ofCoeffs (S := k) d
  have hle : LinearMap.ker φ ≤ LinearMap.ker μ := fun c hc => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hc
    exact hμ c hc
  set μ' := (LinearMap.ker φ).liftQ μ hle
  set φ' := (LinearMap.ker φ).liftQ φ le_rfl
  obtain ⟨ψ, hψ⟩ := φ'.exists_leftInverse_of_injective
    (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  refine ⟨μ' ∘ₗ ψ ∘ₗ p.mkQ, fun f hf => ?_, fun c => ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero p).2 hf, map_zero, map_zero]
  · have h := LinearMap.congr_fun hψ ((LinearMap.ker φ).mkQ c)
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.id_apply] at h
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    change μ' (ψ (φ c)) = μ c
    rw [h, Submodule.liftQ_apply]

variable (S : Type*) [CommRing S] [Algebra k S]

/-- The base change of a functional on the polynomials over `k` to the polynomials over `S`. -/
def baseChangeFunctional (ℓ : MvPolynomial (Coordinate n) k →ₗ[k] k) :
    MvPolynomial (Coordinate n) S →ₗ[S] S :=
  (basisMonomials (Coordinate n) S).constr S fun m => algebraMap k S (ℓ (monomial m 1))

variable {S}

omit [Fintype n] [DecidableEq n] in
theorem baseChangeFunctional_monomial (ℓ : MvPolynomial (Coordinate n) k →ₗ[k] k)
    (m : Coordinate n →₀ ℕ) (s : S) :
    baseChangeFunctional S ℓ (monomial m s) = s * algebraMap k S (ℓ (monomial m 1)) := by
  rw [show monomial m s = s • (basisMonomials (Coordinate n) S) m by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one], map_smul, baseChangeFunctional,
    Module.Basis.constr_basis, smul_eq_mul]

omit [Fintype n] [DecidableEq n] in
theorem baseChangeFunctional_map (ℓ : MvPolynomial (Coordinate n) k →ₗ[k] k)
    (f : MvPolynomial (Coordinate n) k) :
    baseChangeFunctional S ℓ (map (algebraMap k S) f) = algebraMap k S (ℓ f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [map_monomial, baseChangeFunctional_monomial, ← map_mul,
      show monomial m a = a • monomial m (1 : k) by rw [smul_monomial, smul_eq_mul, mul_one],
      map_smul, smul_eq_mul]
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]

omit [Fintype n] [DecidableEq n] in
/-- The base change of a functional killing `J` kills the extension of `J` to `S`. -/
theorem baseChangeFunctional_eq_zero {ℓ : MvPolynomial (Coordinate n) k →ₗ[k] k}
    (hℓ : ∀ f ∈ J, ℓ f = 0) {F : MvPolynomial (Coordinate n) S}
    (hF : F ∈ J.map (map (algebraMap k S))) : baseChangeFunctional S ℓ F = 0 := by
  let K : Ideal (MvPolynomial (Coordinate n) S) :=
    { carrier := {F | ∀ G, baseChangeFunctional S ℓ (G * F) = 0}
      add_mem' := fun {F F'} hF hF' G => by
        change baseChangeFunctional S ℓ (G * (F + F')) = 0
        rw [mul_add, map_add, hF G, hF' G, add_zero]
      zero_mem' := fun G => by
        change baseChangeFunctional S ℓ (G * 0) = 0
        rw [mul_zero, map_zero]
      smul_mem' := fun c F hF G => by
        change baseChangeFunctional S ℓ (G * (c * F)) = 0
        rw [← mul_assoc]
        exact hF _ }
  have hJK : J.map (map (algebraMap k S)) ≤ K := by
    refine Ideal.map_le_iff_le_comap.2 fun f hf G => ?_
    induction G using MvPolynomial.induction_on' with
    | monomial m s =>
      rw [show monomial m s * map (algebraMap k S) f =
          s • map (algebraMap k S) (monomial m 1 * f) by
        rw [map_mul, map_monomial, map_one, smul_eq_C_mul, ← mul_assoc, C_mul_monomial, mul_one],
        map_smul, baseChangeFunctional_map, hℓ _ (J.mul_mem_left _ hf), map_zero, smul_zero]
    | add G G' hG hG' => rw [add_mul, map_add, hG, hG', add_zero]
  have := hJK hF 1
  rwa [one_mul] at this

/-- **Functionals vanishing on `J`.** If `μ` kills the coefficient vectors of the polynomials of
`J` of degree at most `d`, then for every polynomial `F` of the extension of `J` to `S` of degree
at most `d`, the sum of the coefficients of `F` weighted by the values of `μ` vanishes. -/
theorem sum_coeff_mul_eq_zero (μ : (Exponent n d → k) →ₗ[k] k)
    (hμ : ∀ c, ofCoeffs d c ∈ J → μ c = 0) {F : MvPolynomial (Coordinate n) S}
    (hF : F ∈ J.map (map (algebraMap k S))) (hFd : F.totalDegree ≤ d) :
    ∑ m : Exponent n d, F.coeff m.1 * algebraMap k S (μ (Pi.single m 1)) = 0 := by
  obtain ⟨ℓ, hℓJ, hℓμ⟩ := exists_functional_extension d μ hμ
  have h := baseChangeFunctional_eq_zero hℓJ hF
  rw [eq_sum_exponent hFd, map_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [baseChangeFunctional_monomial, ← hℓμ, ofCoeffs_single]

end Functional

section Stabilizer

variable {k : Type u} [Field k] {J : Ideal (MvPolynomial (Coordinate n) k)}

variable (J) in
/-- The coefficient vectors of the polynomials of `J` of total degree at most `d`. -/
def coeffSubspace (d : ℕ) : Submodule k (Exponent n d → k) :=
  (J.restrictScalars k).comap (ofCoeffs d)

omit [DecidableEq n] in
theorem mem_coeffSubspace {d : ℕ} {c : Exponent n d → k} :
    c ∈ coeffSubspace J d ↔ ofCoeffs d c ∈ J :=
  Iff.rfl

variable (J) in
/-- The zero loci of `J` in `GL_n(R)` are closed under multiplication for all `k`-algebras `R`. -/
def ZeroLocusMulClosed : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] (g h : GL n R), g ∈ zeroLocus R J →
    h ∈ zeroLocus R J → g * h ∈ zeroLocus R J

/-- The ideal of `GL_n` over `S` lies in the extension of `J` to `S`. -/
theorem ideal_le_map (hJ : ideal n k ≤ J) (S : Type u) [CommRing S] [Algebra k S] :
    ideal n S ≤ J.map (MvPolynomial.map (algebraMap k S)) := by
  have hgm : (MvPolynomial.map (algebraMap k S)).mapMatrix (genericMatrix n k) =
      genericMatrix n S := by
    ext i j
    simp [genericMatrix]
  have hgi : (MvPolynomial.map (algebraMap k S)).mapMatrix (genericInverse n k) =
      genericInverse n S := by
    ext i j
    simp [genericInverse]
  refine Ideal.span_le.2 ?_
  rintro _ (⟨⟨i, j⟩, rfl⟩ | ⟨⟨i, j⟩, rfl⟩)
  · change (genericMatrix n S * genericInverse n S - 1) i j ∈ _
    rw [show genericMatrix n S * genericInverse n S - 1 =
        (MvPolynomial.map (algebraMap k S)).mapMatrix (genericMatrix n k * genericInverse n k - 1) by
      rw [map_sub, map_mul, map_one, hgm, hgi]]
    exact Ideal.mem_map_of_mem _ (hJ (Ideal.subset_span (Or.inl ⟨(i, j), rfl⟩)))
  · change (genericInverse n S * genericMatrix n S - 1) i j ∈ _
    rw [show genericInverse n S * genericMatrix n S - 1 =
        (MvPolynomial.map (algebraMap k S)).mapMatrix (genericInverse n k * genericMatrix n k - 1) by
      rw [map_sub, map_mul, map_one, hgm, hgi]]
    exact Ideal.mem_map_of_mem _ (hJ (Ideal.subset_span (Or.inr ⟨(i, j), rfl⟩)))

/-- **Translation preserves the extended ideal.** If the zero loci of `J` are closed under
multiplication and `h` is a zero of `J` over `S`, then right translation by `h` maps the
polynomials of `J` into the extension of `J` to `S`. -/
theorem translate_map_mem (hJ : ideal n k ≤ J) (hmul : ZeroLocusMulClosed J) {S : Type u}
    [CommRing S] [Algebra k S] {h : GL n S} (hh : h ∈ zeroLocus S J)
    {f : MvPolynomial (Coordinate n) k} (hf : f ∈ J) :
    translate h (MvPolynomial.map (algebraMap k S) f) ∈
      J.map (MvPolynomial.map (algebraMap k S)) := by
  -- the generic zero of the extension of `J`
  let x : GL n (MvPolynomial (Coordinate n) S ⧸ J.map (MvPolynomial.map (algebraMap k S))) :=
    point (Ideal.Quotient.factorₐ S (ideal_le_map hJ S))
  have hx : aeval (values x) = Ideal.Quotient.mkₐ S (J.map (MvPolynomial.map (algebraMap k S))) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rw [aeval_X]
    cases v <;> rfl
  have hxZ : x ∈ zeroLocus _ J := by
    intro f' hf'
    rw [← aeval_map_algebraMap S, hx, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hf'
  have hhZ := map_mem_zeroLocus
    (IsScalarTower.toAlgHom k S (MvPolynomial (Coordinate n) S ⧸
      J.map (MvPolynomial.map (algebraMap k S)))) hh
  have := hmul _ x _ hxZ hhZ f hf
  rw [← aeval_map_algebraMap S] at this
  erw [← aeval_values_translate] at this
  rwa [hx, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at this

variable (k) in
/-- The unit `T` of the Laurent polynomials. -/
def unitT : (LaurentPolynomial k)ˣ :=
  (LaurentPolynomial.isUnit_T 1).unit

theorem coe_unitT_zpow (j : ℤ) :
    ((unitT k ^ j : (LaurentPolynomial k)ˣ) : LaurentPolynomial k) = LaurentPolynomial.T j := by
  have hinv : ((unitT k)⁻¹ : (LaurentPolynomial k)ˣ) = (LaurentPolynomial.T (-1) : LaurentPolynomial k) :=
    Units.inv_eq_of_mul_eq_one_right (by
      rw [unitT, IsUnit.unit_spec, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero])
  induction j using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one, LaurentPolynomial.T_zero]
  | succ i ih =>
    rw [zpow_add_one, Units.val_mul, ih, unitT, IsUnit.unit_spec, ← LaurentPolynomial.T_add]
  | pred i ih =>
    rw [zpow_sub_one, Units.val_mul, ih, hinv, LaurentPolynomial.T_sub]

/-- **The coefficient subspace is graded.** If the zero loci of `J` are closed under
multiplication and contain `diag(T ^ e i)` over the Laurent polynomials, then the space of
coefficient vectors of the polynomials of `J` of degree at most `d` contains the weight
components of its vectors. -/
theorem weightPart_mem_coeffSubspace (e : n → ℤ) (hJ : ideal n k ≤ J) (hmul : ZeroLocusMulClosed J)
    (hdiag : diagonalUnits (LaurentPolynomial k) e (unitT k) ∈ zeroLocus (LaurentPolynomial k) J)
    {d : ℕ} {c : Exponent n d → k} (hc : c ∈ coeffSubspace J d) (w : ℤ) :
    weightPart (fun m : Exponent n d => monomialWeight e m.1) w c ∈ coeffSubspace J d := by
  by_contra hnot
  obtain ⟨μ, hμ, hμW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hμJ : ∀ c', ofCoeffs d c' ∈ J → μ c' = 0 := fun c' hc' => by
    have : μ c' ∈ (coeffSubspace J d).map μ := Submodule.mem_map_of_mem hc'
    rwa [hμW, Submodule.mem_bot] at this
  have hF := translate_map_mem hJ hmul hdiag hc
  have hFeq : translate (diagonalUnits (LaurentPolynomial k) e (unitT k))
      (MvPolynomial.map (algebraMap k (LaurentPolynomial k)) (ofCoeffs d c)) =
      ofCoeffs d fun m => LaurentPolynomial.C (c m) *
        LaurentPolynomial.T (monomialWeight e m.1) := by
    rw [map_ofCoeffs, ofCoeffs_apply, ofCoeffs_apply, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [translate_diagonalUnits_monomial, coe_unitT_zpow]
    rfl
  rw [hFeq] at hF
  have hsum := sum_coeff_mul_eq_zero d μ hμJ hF (totalDegree_ofCoeffs_le d _)
  simp only [coeff_ofCoeffs] at hsum
  have hterm : ∀ m : Exponent n d, LaurentPolynomial.C (c m) *
      LaurentPolynomial.T (monomialWeight e m.1) * algebraMap k (LaurentPolynomial k) (μ (Pi.single m 1)) =
      AddMonoidAlgebra.single (monomialWeight e m.1) (c m * μ (Pi.single m 1)) := by
    intro m
    rw [LaurentPolynomial.single_eq_C_mul_T, map_mul, ← LaurentPolynomial.C_eq_algebraMap]
    ring
  simp only [hterm] at hsum
  have hw := congrArg (fun p : LaurentPolynomial k => p.coeff w) hsum
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hw
  apply hμ
  rw [linearMap_apply_eq_sum μ]
  simpa only [weightPart, ite_mul, zero_mul] using hw

/-- **The stabilizer argument.** Let `J` contain the ideal of `GL_n`, and let its zero loci be
closed under multiplication, contain `1` and contain `diag(T ^ e i)` over the Laurent
polynomials. If `v q` is a zero of `J` over `S`, with `v` block unipotent for `-e` and `q` block
parabolic for `e`, then `q` is a zero of `J`. -/
theorem mem_zeroLocus_of_mul_mem (e : n → ℤ) (hJ : ideal n k ≤ J) (hmul : ZeroLocusMulClosed J)
    (h1 : (1 : GL n k) ∈ zeroLocus k J)
    (hdiag : diagonalUnits (LaurentPolynomial k) e (unitT k) ∈ zeroLocus (LaurentPolynomial k) J)
    {S : Type u} [CommRing S] [Algebra k S] {v q : GL n S}
    (hv : v ∈ blockUnipotentSubgroup S (-e)) (hq : q ∈ blockParabolicSubgroup S e)
    (hvq : v * q ∈ zeroLocus S J) : q ∈ zeroLocus S J := by
  intro g hg
  obtain ⟨d, hd⟩ : ∃ d, g.totalDegree ≤ d := ⟨_, le_rfl⟩
  -- pivot coordinates for the graded space of coefficient vectors
  obtain ⟨s, N, hN, hNa, hNW, hNs⟩ := exists_pivot (fun m : Exponent n d => monomialWeight e m.1)
    (coeffSubspace J d) fun c hc w => weightPart_mem_coeffSubspace e hJ hmul hdiag hc w
  have hNN : N * N = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h : N i l = 0
    · rw [h, zero_mul]
    · have : N l j = 0 := by
        by_contra h'
        exact (hN i l h).2 (hN l j h').1
      rw [this, mul_zero]
  let B : GL (Exponent n d) k :=
    { val := 1 + N
      inv := 1 - N
      val_inv := by rw [mul_sub, mul_one, add_mul, one_mul, hNN, add_zero, add_sub_cancel_right]
      inv_val := by rw [mul_add, mul_one, sub_mul, one_mul, hNN, sub_zero, sub_add_cancel] }
  have hB : B ∈ blockLeviSubgroup k (fun m : Exponent n d => monomialWeight e m.1) :=
    fun i j hij => by
      change (1 + N) i j = 0
      rw [Matrix.add_apply, Matrix.one_apply_ne (fun h => hij (by rw [h])), hNa i j hij, add_zero]
  obtain ⟨Bu, hBu⟩ : ∃ Bu, Bu = Matrix.GeneralLinearGroup.map (algebraMap k S) B := ⟨_, rfl⟩
  have hBuL : Bu ∈ blockLeviSubgroup S (fun m : Exponent n d => monomialWeight e m.1) := by
    rw [hBu]
    exact map_mem_blockLeviSubgroup _ _ hB
  have hBuval : (Bu : Matrix (Exponent n d) (Exponent n d) S) = (1 + N).map (algebraMap k S) := by
    rw [hBu]
    rfl
  have hBuinv : ((Bu⁻¹ : GL (Exponent n d) S) : Matrix (Exponent n d) (Exponent n d) S) =
      (1 - N).map (algebraMap k S) := by
    rw [hBu, ← Matrix.GeneralLinearGroup.map_inv]
    rfl
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Bu⁻¹ * translationHom S d q * Bu := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = Bu⁻¹ * translationHom S d v * Bu := ⟨_, rfl⟩
  have hQP : Q ∈ blockParabolicSubgroup S (fun m : Exponent n d => monomialWeight e m.1) := by
    rw [hQ]
    exact conj_mem_blockParabolicSubgroup _ hBuL (translationHom_mem_blockParabolicSubgroup e hq d)
  have hVU : V ∈ blockUnipotentSubgroup S (-fun m : Exponent n d => monomialWeight e m.1) := by
    rw [hV]
    exact conj_mem_blockUnipotentSubgroup _ (by rw [blockLeviSubgroup_neg]; exact hBuL)
      (translationHom_mem_blockUnipotentSubgroup e hv d)
  -- the conjugated translation by `v q` has no entries from the pivot columns to the rows of `s`
  have hkey : ∀ r j, ¬ (r ∉ s) → j ∉ s →
      ((Bu⁻¹ * translationHom S d (v * q) * Bu : GL (Exponent n d) S) :
        Matrix (Exponent n d) (Exponent n d) S) r j = 0 := by
    intro r j hr hj
    rw [not_not] at hr
    have hcj : ofCoeffs d (fun i => (1 + N) i j) ∈ J := hNW j hj
    have hdeg : (MvPolynomial.map (algebraMap k S) (ofCoeffs d fun i => (1 + N) i j)).totalDegree
        ≤ d := by
      rw [map_ofCoeffs]
      exact totalDegree_ofCoeffs_le d _
    have hsum := sum_coeff_mul_eq_zero d (LinearMap.proj r ∘ₗ (1 - N).mulVecLin)
      (fun c hc => hNs c hc r hr) (translate_map_mem hJ hmul hvq hcj)
      (totalDegree_translate_le hdeg (v * q))
    refine Eq.trans ?_ hsum
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hBuinv, coeff_translate hdeg, map_ofCoeffs, mul_comm (Matrix.map (1 - N) (algebraMap k S) r m)]
    congr 1
    · simp only [coeff_ofCoeffs, hBuval]
      rfl
    · simp only [Matrix.map_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  have hQzero : ∀ r j, r ∈ s → j ∉ s → (Q : Matrix (Exponent n d) (Exponent n d) S) r j = 0 :=
    fun r j hr hj => eq_zero_of_eq_mul_of_compl_zero _ (fun i => i ∉ s) hVU hQP
      (by rw [hV, hQ, map_mul]; simp only [mul_assoc, mul_inv_cancel_left]) hkey r j
      (not_not.2 hr) hj
  -- evaluation at `q` through the translation matrix
  have h1S : (1 : GL n S) ∈ zeroLocus S J := by
    have := map_mem_zeroLocus (Algebra.ofId k S) h1
    rwa [map_one] at this
  have hε : ∀ c : Exponent n d → S, aeval (values (1 : GL n S)) (ofCoeffs d c) =
      ∑ m, c m * aeval (values (1 : GL n S)) (monomial m.1 (1 : S)) := by
    intro c
    rw [ofCoeffs_apply, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show monomial m.1 (c m) = c m • monomial m.1 (1 : S) by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  set ℓ : Exponent n d → S := fun m => aeval (values (1 : GL n S)) (monomial m.1 (1 : S)) with hℓ
  have hℓB : ∀ j, j ∉ s → (ℓ ᵥ* (Bu : Matrix (Exponent n d) (Exponent n d) S)) j = 0 := by
    intro j hj
    have h0 := h1S _ ((mem_coeffSubspace).1 (hNW j hj))
    rw [← aeval_map_algebraMap S, map_ofCoeffs, hε] at h0
    rw [← h0, hBuval]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Function.comp_apply]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  set cg : Exponent n d → k := fun m => g.coeff m.1 with hcgdef
  have hcg : ofCoeffs d cg = g := ofCoeffs_coeff d hd
  have hz : ∀ j, j ∈ s → (((Bu⁻¹ : GL (Exponent n d) S) : Matrix (Exponent n d) (Exponent n d) S)
      *ᵥ (algebraMap k S ∘ cg)) j = 0 := by
    intro j hj
    rw [hBuinv, ← RingHom.map_mulVec, hNs cg (by rw [mem_coeffSubspace, hcg]; exact hg) j hj,
      map_zero]
  have hgd : (MvPolynomial.map (algebraMap k S) g).totalDegree ≤ d := by
    rw [← hcg, map_ofCoeffs]
    exact totalDegree_ofCoeffs_le d _
  have hρq : ((translationHom S d q : GL (Exponent n d) S) : Matrix (Exponent n d) (Exponent n d) S) =
      (Bu : Matrix (Exponent n d) (Exponent n d) S) * (Q : Matrix (Exponent n d) (Exponent n d) S) *
        ((Bu⁻¹ : GL (Exponent n d) S) : Matrix (Exponent n d) (Exponent n d) S) := by
    rw [← Units.val_mul, ← Units.val_mul, hQ]
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
  have hG := totalDegree_translate_le hgd q
  calc aeval (values q) g
      = aeval (values (1 : GL n S)) (translate q (MvPolynomial.map (algebraMap k S) g)) := by
        rw [aeval_values_translate, Algebra.algebraMap_self, Matrix.GeneralLinearGroup.map_id,
          MonoidHom.id_apply, one_mul, aeval_map_algebraMap]
    _ = ∑ m, (translationHom S d q *ᵥ (algebraMap k S ∘ cg) : Exponent n d → S) m * ℓ m := by
        rw [← ofCoeffs_coeff d hG, hε]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [coeff_translate hgd, ← hcg, map_ofCoeffs]
        simp only [coeff_ofCoeffs]
        rfl
    _ = (ℓ ᵥ* (Bu : Matrix (Exponent n d) (Exponent n d) S)) ⬝ᵥ
          ((Q : Matrix (Exponent n d) (Exponent n d) S) *ᵥ
            (((Bu⁻¹ : GL (Exponent n d) S) : Matrix (Exponent n d) (Exponent n d) S) *ᵥ
              (algebraMap k S ∘ cg))) := by
        rw [← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hρq,
          dotProduct_comm]
        rfl
    _ = 0 := by
        refine Finset.sum_eq_zero fun r _ => ?_
        by_cases hr : r ∈ s
        · rw [Matrix.mulVec, dotProduct, Finset.sum_eq_zero fun j _ => ?_, mul_zero]
          by_cases hj : j ∈ s
          · rw [hz j hj, mul_zero]
          · rw [hQzero r j hr hj, zero_mul]
        · rw [hℓB r hr, zero_mul]

end Stabilizer

end Langlands.GroupScheme.GeneralLinear
