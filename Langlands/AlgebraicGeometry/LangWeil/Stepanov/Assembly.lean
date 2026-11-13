import Langlands.AlgebraicGeometry.LangWeil.Stepanov.Construction
import Langlands.AlgebraicGeometry.LangWeil.Stepanov.RootTools

/-!
# The two auxiliary norm polynomials

For an absolutely irreducible `P ∈ F[X][Y]` over a finite field `F` with `q` elements we
construct two nonzero polynomials `h₁, h₂ ∈ F[X]`, resultants `Res_Y(P, A)` of auxiliary
polynomials `A = ∑ B_{jk} X^{qj} Y^{qk}`, such that

* `h₁` vanishes to order `≥ M` at `x` along every rational point `(x, y)`, `y ∈ F`,
  with `P_Y(x, y) ≠ 0`;
* `h₂` vanishes to order `≥ M` at `x` along every point `(x, y)`, `y ∈ F̄`, with
  `P(x, y^q) = 0`, `y^q ≠ y` and `P_Y(x, y) ≠ 0`, provided the leading coefficient of `P`
  does not vanish at `x`.
-/

noncomputable section

universe u

open Polynomial

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

variable {F : Type u} [Field F]

local notation "R2" => Polynomial (Polynomial F)

theorem exists_charP_card [Finite F] :
    ∃ p k : ℕ, Fact p.Prime ∧ CharP F p ∧ Nat.card F = p ^ k := by
  have := Fintype.ofFinite F
  obtain ⟨p, hchar, k, hp, hcard⟩ := FiniteField.card' F
  exact ⟨p, k, ⟨hp⟩, hchar, by rw [Nat.card_eq_fintype_card, hcard]⟩

/-- The low coefficients of the image of the auxiliary polynomial under a point branch. -/
theorem coeff_rho_normPoly {L : Type*} [Field L] [Algebra F L] {p : ℕ} [Fact p.Prime]
    [CharP L p] (k : ℕ) (P : R2) (x : F) (y : L) (N n d : ℕ) (v : Idx N n d → F) {l : ℕ}
    (hl : l < p ^ k) :
    PowerSeries.coeff l (rho P x y (normPoly (p ^ k) N n d v)) =
      ((ev x y (derivative P))⁻¹ ^ 2) ^ l *
        ∑ t ∈ Finset.range (N + 1) ×ˢ Finset.range n,
          ev x y (Ql P l (coefPolyL N n d t.1 t.2 v)) *
            ev x y (C (X ^ t.1) * X ^ t.2 : R2) ^ (p ^ k) := by
  rw [normPoly_eq_sum_mul_pow]
  exact coeff_rho_sum_mul_pow k P x y _ _ _ hl

/-! ### Rational points -/

/-- At a rational point of `P = 0`, the conditions of the first kind make the first `M`
coefficients of the branch image of the auxiliary polynomial vanish. -/
theorem coeff_rho_normPoly_eq_zero_of_E1L [Finite F] (P : R2) (x y : F) (N d M : ℕ)
    (v : Idx N P.natDegree d → F) (hMq : M ≤ Nat.card F)
    (hv : ∀ l < M, P ∣ E1L P N P.natDegree d l v) (hy : ev x y P = 0) :
    ∀ l < M, PowerSeries.coeff l (rho P x y (normPoly (Nat.card F) N P.natDegree d v)) = 0 := by
  intro l hl
  have := Fintype.ofFinite F
  obtain ⟨p, k, hp, hchar, hq⟩ := exists_charP_card (F := F)
  have hE : ∀ t : ℕ × ℕ, ev x y (C (X ^ t.1) * X ^ t.2 : R2) ^ (p ^ k) =
      ev x y (C (X ^ t.1) * X ^ t.2 : R2) := by
    intro t
    rw [← hq, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hsum : ∑ t ∈ Finset.range (N + 1) ×ˢ Finset.range P.natDegree,
      ev x y (Ql P l (coefPolyL N P.natDegree d t.1 t.2 v)) *
        ev x y (C (X ^ t.1) * X ^ t.2 : R2) = ev x y (E1L P N P.natDegree d l v) := by
    rw [E1L_apply, map_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul]
  obtain ⟨Q, hQ⟩ := hv l hl
  rw [hq, coeff_rho_normPoly k P x y N _ d v (by omega),
    Finset.sum_congr rfl fun t _ => by rw [hE t], hsum, hQ, map_mul, hy, zero_mul, mul_zero]

/-- The first auxiliary polynomial: vanishing to order `M` along rational points. -/
theorem exists_normPoly_rational [Finite F] (P : R2) (m d N M : ℕ)
    (habs : Irreducible (P.map (Polynomial.mapRingHom (algebraMap F (AlgebraicClosure F)))))
    (hirr : Irreducible P) (hn : 1 ≤ P.natDegree) (hm1 : 1 ≤ m)
    (hm : ∀ i, (P.coeff i).natDegree ≤ m)
    (hd : P.natDegree * d + m * (P.natDegree - 1) ^ 2 < Nat.card F)
    (hMq : M ≤ Nat.card F)
    (hdim : ∑ l ∈ Finset.range M, (P.natDegree * (d + l * (2 * m - 1) + N + 1) +
        m * ((P.natDegree - 1) * (2 * l + 2) + 1 - P.natDegree)) <
      P.natDegree * P.natDegree * (N + 1) * (d + 1)) :
    ∃ h : Polynomial F, h ≠ 0 ∧
      h.natDegree ≤ (P.natDegree - 1) * (Nat.card F + 1) * m +
        P.natDegree * (d + Nat.card F * N) ∧
      ∀ (x : F) (T : Finset F), (∀ y ∈ T, ev x y P = 0 ∧ ev x y (derivative P) ≠ 0) →
        M * T.card ≤ h.rootMultiplicity x := by
  classical
  have hP : InBox (m : ℤ) (P.natDegree : ℤ) P := inBox_iff_of_nonneg.mpr ⟨le_rfl, hm⟩
  have h2m : 1 ≤ 2 * m := by omega
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_forall_dvd F P m hirr.ne_zero hm
    (Idx N P.natDegree d → F) (Fin M) (fun l => E1L P N P.natDegree d l)
    (fun l => d + l * (2 * m - 1) + N) (fun l => (P.natDegree - 1) * (2 * l + 2))
    (fun l v => by
      refine inBox_iff_of_nonneg.mp ((inBox_E1L hP hn N d l v).mono ?_ ?_)
      · push_cast [Nat.cast_sub h2m]
        exact le_rfl
      · push_cast [Nat.cast_sub hn]
        exact le_rfl)
    (by
      rw [Module.finrank_fintype_fun_eq_card]
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [Fin.sum_univ_eq_sum_range (fun l => P.natDegree * (d + l * (2 * m - 1) + N + 1) +
        m * ((P.natDegree - 1) * (2 * l + 2) + 1 - P.natDegree)) M]
      calc _ < _ := hdim
        _ = _ := by ring)
  obtain ⟨hh0, hdeg, hA⟩ := normPoly_resultant P m d N v hv0 habs hn hm hd
    (fun A D hA hnd => resultant_ne_zero_of_not_dvd F P A D hirr hn hA hnd)
  refine ⟨_, hh0, hdeg, fun x T hT => ?_⟩
  refine mul_card_le_rootMultiplicity_of_rho P _ _ M x T hirr.ne_zero hA hh0 fun y hy => ?_
  exact ⟨(hT y hy).1, (hT y hy).2, coeff_rho_normPoly_eq_zero_of_E1L P x y N d M v hMq
    (fun l hl => hv ⟨l, hl⟩) (hT y hy).1⟩

/-! ### Points moved by Frobenius -/

/-- At a point `(x, y)` of `P = 0` over `F̄` with `P(x, y^q) = 0` and `y^q ≠ y`, the conditions
of the second kind make the first `M` coefficients of the branch image of the auxiliary
polynomial vanish. -/
theorem coeff_rho_normPoly_eq_zero_of_E2L [Finite F] (P : R2) (hn : 1 ≤ P.natDegree) (x : F)
    (y : AlgebraicClosure F) (N d M : ℕ) (v : Idx N P.natDegree d → F) (hMq : M ≤ Nat.card F)
    (hv : ∀ l < M, ∀ k < P.natDegree - 1, P ∣ E2L P N P.natDegree d l k v)
    (hg : P.leadingCoeff.eval x ≠ 0) (hy : ev x y P = 0) (hy' : ev x (y ^ Nat.card F) P = 0)
    (hyy : y ^ Nat.card F ≠ y) :
    ∀ l < M, PowerSeries.coeff l (rho P x y (normPoly (Nat.card F) N P.natDegree d v)) = 0 := by
  intro l hl
  have := Fintype.ofFinite F
  obtain ⟨p, k, hp, hchar, hq⟩ := exists_charP_card (F := F)
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hE : ∀ t : ℕ × ℕ, ev x y (C (X ^ t.1) * X ^ t.2 : R2) ^ (p ^ k) =
      ev x y (C (X ^ t.1) : R2) * (y ^ Nat.card F) ^ t.2 := by
    intro t
    have hx : algebraMap F (AlgebraicClosure F) x ^ Nat.card F = algebraMap F _ x := by
      rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
    simp only [map_mul, map_pow, ev_C, ev_X, eval_X]
    rw [← hq]
    calc _ = (algebraMap F (AlgebraicClosure F) x ^ Nat.card F) ^ t.1 * (y ^ Nat.card F) ^ t.2 := by
          ring
      _ = _ := by rw [hx]
  have hsum : ∑ t ∈ Finset.range (N + 1) ×ˢ Finset.range P.natDegree,
      ev x y (Ql P l (coefPolyL N P.natDegree d t.1 t.2 v)) *
        (ev x y (C (X ^ t.1) : R2) * (y ^ Nat.card F) ^ t.2) =
      ∑ k ∈ Finset.range P.natDegree, ev x y (eL P N P.natDegree d l k v) * (y ^ Nat.card F) ^ k := by
    rw [Finset.sum_product_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eL_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  have hrel : ∀ k ∈ Finset.range P.natDegree, ev x y (C P.leadingCoeff : R2) * ev x y (eL P N P.natDegree d l k v) =
      ev x y (eL P N P.natDegree d l (P.natDegree - 1) v) * ev x y (divX^[k + 1] P) := by
    intro k hk
    have hk := Finset.mem_range.mp hk
    by_cases hk' : k < P.natDegree - 1
    · obtain ⟨Q, hQ⟩ := hv l hl k hk'
      have h := congrArg (ev x y) hQ
      rw [E2L_apply, map_sub, map_mul, map_mul, map_mul, hy, zero_mul] at h
      exact sub_eq_zero.mp h
    · obtain rfl : k = P.natDegree - 1 := by omega
      rw [Nat.sub_add_cancel hn, divX_iterate_natDegree, mul_comm]
  have htel : ∑ k ∈ Finset.range P.natDegree, ev x y (divX^[k + 1] P) * (y ^ Nat.card F) ^ k = 0 := by
    set ψ := (algebraMap F (AlgebraicClosure F)).comp (Polynomial.evalRingHom x) with hψ
    have hev : ∀ (A : R2) (z : AlgebraicClosure F), ev x z A = (A.map ψ).eval z := by
      intro A z
      rw [eval_map]
      rfl
    have h := divX_telescoping (AlgebraicClosure F) (P.map ψ) P.natDegree natDegree_map_le y
      (y ^ Nat.card F)
    rw [← hev, ← hev, hy, hy', sub_self] at h
    simp_rw [divX_iterate_map, ← hev] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (sub_ne_zero.mpr hyy.symm)
  have hg' : ev x y (C P.leadingCoeff : R2) ≠ 0 := by
    rw [ev_C]
    exact (_root_.map_ne_zero _).mpr hg
  have hfinal : ∑ k ∈ Finset.range P.natDegree, ev x y (eL P N P.natDegree d l k v) * (y ^ Nat.card F) ^ k = 0 := by
    have h : ev x y (C P.leadingCoeff : R2) *
        ∑ k ∈ Finset.range P.natDegree, ev x y (eL P N P.natDegree d l k v) * (y ^ Nat.card F) ^ k =
        ev x y (eL P N P.natDegree d l (P.natDegree - 1) v) *
          ∑ k ∈ Finset.range P.natDegree, ev x y (divX^[k + 1] P) * (y ^ Nat.card F) ^ k := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [← mul_assoc, hrel k hk, mul_assoc]
    rw [htel, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hg'
  rw [hq, coeff_rho_normPoly k P x y N _ d v (by omega),
    Finset.sum_congr rfl fun t _ => by rw [hE t], hsum, hfinal, mul_zero]

/-- The second auxiliary polynomial: vanishing to order `M` along the points of `P = 0` over
`F̄` moved by Frobenius. -/
theorem exists_normPoly_nonrational [Finite F] (P : R2) (m d N M : ℕ)
    (habs : Irreducible (P.map (Polynomial.mapRingHom (algebraMap F (AlgebraicClosure F)))))
    (hirr : Irreducible P) (hn : 1 ≤ P.natDegree) (hm1 : 1 ≤ m)
    (hm : ∀ i, (P.coeff i).natDegree ≤ m)
    (hd : P.natDegree * d + m * (P.natDegree - 1) ^ 2 < Nat.card F)
    (hMq : M ≤ Nat.card F)
    (hdim : (P.natDegree - 1) * ∑ l ∈ Finset.range M,
        (P.natDegree * (d + l * (2 * m - 1) + N + m + 1) +
          m * ((P.natDegree - 1) * (2 * l + 2) + 1 - P.natDegree)) <
      P.natDegree * P.natDegree * (N + 1) * (d + 1)) :
    ∃ h : Polynomial F, h ≠ 0 ∧
      h.natDegree ≤ (P.natDegree - 1) * (Nat.card F + 1) * m +
        P.natDegree * (d + Nat.card F * N) ∧
      ∀ (x : F) (T : Finset (AlgebraicClosure F)), P.leadingCoeff.eval x ≠ 0 →
        (∀ y ∈ T, ev x y P = 0 ∧ ev x y (derivative P) ≠ 0 ∧ ev x (y ^ Nat.card F) P = 0 ∧
          y ^ Nat.card F ≠ y) →
        M * T.card ≤ h.rootMultiplicity x := by
  classical
  have hP : InBox (m : ℤ) (P.natDegree : ℤ) P := inBox_iff_of_nonneg.mpr ⟨le_rfl, hm⟩
  have h2m : 1 ≤ 2 * m := by omega
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_forall_dvd F P m hirr.ne_zero hm
    (Idx N P.natDegree d → F) (Fin M × Fin (P.natDegree - 1))
    (fun t => E2L P N P.natDegree d t.1 t.2)
    (fun t => d + t.1 * (2 * m - 1) + N + m) (fun t => (P.natDegree - 1) * (2 * t.1 + 2))
    (fun t v => by
      refine inBox_iff_of_nonneg.mp ((inBox_E2L hP hn N d t.1 t.2 v).mono ?_ ?_)
      · push_cast [Nat.cast_sub h2m]
        exact le_rfl
      · push_cast [Nat.cast_sub hn]
        exact le_rfl)
    (by
      rw [Module.finrank_fintype_fun_eq_card]
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.sum_prod_type, Finset.sum_const,
        Finset.card_univ, smul_eq_mul, ← Finset.mul_sum]
      rw [Fin.sum_univ_eq_sum_range (fun l => P.natDegree * (d + l * (2 * m - 1) + N + m + 1) +
        m * ((P.natDegree - 1) * (2 * l + 2) + 1 - P.natDegree)) M]
      calc _ < _ := hdim
        _ = _ := by ring)
  obtain ⟨hh0, hdeg, hA⟩ := normPoly_resultant P m d N v hv0 habs hn hm hd
    (fun A D hA hnd => resultant_ne_zero_of_not_dvd F P A D hirr hn hA hnd)
  refine ⟨_, hh0, hdeg, fun x T hg hT => ?_⟩
  refine mul_card_le_rootMultiplicity_of_rho P _ _ M x T hirr.ne_zero hA hh0 fun y hy => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hT y hy
  exact ⟨h1, h2, coeff_rho_normPoly_eq_zero_of_E2L P hn x y N d M v hMq
    (fun l hl k hk => hv ⟨⟨l, hl⟩, ⟨k, hk⟩⟩) hg h1 h3 h4⟩

end Langlands.AlgebraicGeometry.LangWeil.Stepanov
