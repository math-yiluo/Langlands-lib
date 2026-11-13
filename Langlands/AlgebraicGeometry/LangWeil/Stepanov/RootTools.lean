import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Inductions

/-!
# Root and resultant tools for the Stepanov–Schmidt argument

Three independent facts used in the plane-curve Hasse–Weil assembly:

* `resultant_ne_zero_of_not_dvd`: for `fh : F[X][Y]` irreducible of positive `Y`-degree and
  `A` not divisible by `fh`, the resultant `Res_Y(fh, A)` (Sylvester sizes `deg_Y fh`, `D` with
  `deg_Y A ≤ D`) is nonzero;
* `nonrationalRoots`: a separable polynomial `p` over a finite field `F` with `q` elements has at
  least `deg p - #(roots of p in F)` roots `y` in the algebraic closure with `y ^ q ≠ y`, and for
  each of them `y ^ q` is again a root;
* `divX_telescoping`: `f(y) - f(y') = (y - y') ∑_{k < n} (divX^[k+1] f)(y) y'^k` for
  `deg f ≤ n`.
-/

open Polynomial

universe u

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

/-! ### Nonvanishing of the resultant -/

/-- If `fh : F[X][Y]` is irreducible of positive `Y`-degree and does not divide `A`, then the
resultant `Res_Y(fh, A)` with Sylvester sizes `natDegree fh` and any `D ≥ natDegree A` is
nonzero. -/
theorem resultant_ne_zero_of_not_dvd (F : Type u) [Field F] (fh A : Polynomial (Polynomial F))
    (D : ℕ) (hirr : Irreducible fh) (hdeg : 1 ≤ fh.natDegree) (hA : A.natDegree ≤ D)
    (hndvd : ¬ fh ∣ A) :
    Polynomial.resultant fh A fh.natDegree D ≠ 0 := by
  classical
  have hn : fh.natDegree ≠ 0 := by omega
  have hfh0 : fh ≠ 0 := hirr.ne_zero
  let K := FractionRing (Polynomial F)
  let φ : Polynomial F →+* K := algebraMap (Polynomial F) K
  have hφ : Function.Injective φ := IsFractionRing.injective (Polynomial F) K
  have hprim : fh.IsPrimitive := hirr.isPrimitive hn
  have hirrK : Irreducible (fh.map φ) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := K)).1 hirr
  have hndvdK : ¬ fh.map φ ∣ A.map φ := by
    intro hdvd
    have hA0 : A ≠ 0 := by
      rintro rfl
      exact hndvd (dvd_zero _)
    have hc : A.content ≠ 0 := fun h => hA0 (content_eq_zero_iff.1 h)
    have e : A.map φ = C (φ A.content) * A.primPart.map φ := by
      conv_lhs => rw [eq_C_content_mul_primPart A]
      rw [Polynomial.map_mul, map_C]
    have hu : IsUnit (C (φ A.content)) :=
      isUnit_C.2 (IsUnit.mk0 _ ((map_ne_zero_iff φ hφ).2 hc))
    rw [e, hu.dvd_mul_left] at hdvd
    exact hndvd ((hprim.dvd_of_fraction_map_dvd_fraction_map hdvd).trans (primPart_dvd A))
  have hcop : IsCoprime (fh.map φ) (A.map φ) := hirrK.coprime_iff_not_dvd.2 hndvdK
  have hdegK : (fh.map φ).natDegree = fh.natDegree := natDegree_map_eq_of_injective hφ fh
  have hdegA : (A.map φ).natDegree = A.natDegree := natDegree_map_eq_of_injective hφ A
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hA
  have hres : φ (resultant fh A fh.natDegree D) =
      (fh.map φ).coeff fh.natDegree ^ k * resultant (fh.map φ) (A.map φ) := by
    rw [← resultant_map_map, hk, ← hdegA,
      resultant_add_right_deg (f := fh.map φ) (g := A.map φ) (m := fh.natDegree)
        (n := (A.map φ).natDegree) k le_rfl, hdegK]
  have hlc : (fh.map φ).coeff fh.natDegree ≠ 0 := by
    rw [coeff_map, coeff_natDegree]
    exact (map_ne_zero_iff φ hφ).2 (leadingCoeff_ne_zero.2 hfh0)
  intro h0
  rw [h0, map_zero] at hres
  exact mul_ne_zero (pow_ne_zero _ hlc) (resultant_ne_zero _ _ hcop) hres.symm

/-! ### Roots moved by Frobenius -/

/-- In any field extension `K` of a finite field `F` with `q` elements, the solutions of
`y ^ q = y` are exactly the elements of `F`. -/
theorem exists_algebraMap_eq_of_pow_card_eq (F : Type u) [Field F] [Fintype F] {K : Type*}
    [Field K] [Algebra F K] (y : K) (hy : y ^ Fintype.card F = y) :
    ∃ x : F, algebraMap F K x = y := by
  classical
  by_contra! hne
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hyS : y ∉ Finset.univ.image (algebraMap F K) := by
    intro h
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 h
    exact hne x hx
  have hS : (insert y (Finset.univ.image (algebraMap F K))).card = Fintype.card F + 1 := by
    rw [Finset.card_insert_of_notMem hyS,
      Finset.card_image_of_injective _ (algebraMap F K).injective, Finset.card_univ]
  have hsub : insert y (Finset.univ.image (algebraMap F K)) ⊆
      (X ^ Fintype.card F - X : K[X]).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots (FiniteField.X_pow_card_sub_X_ne_zero K hq), IsRoot.def,
      eval_sub, eval_pow, eval_X, sub_eq_zero]
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hy
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hz
      rw [← map_pow, FiniteField.pow_card]
  have h := (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans (card_roots' _))
  rw [hS, FiniteField.X_pow_card_sub_X_natDegree_eq K hq] at h
  omega

open Classical in
/-- **Nonrational roots.** Let `p` be separable over a finite field `F` with `q` elements. There
is a finite set `T` of roots `y` of `p` in the algebraic closure with `y ^ q ≠ y` and `y ^ q`
again a root, with `#T ≥ deg p - #(roots of p in F)`. -/
theorem nonrationalRoots (F : Type u) [Field F] [Finite F] (p : Polynomial F)
    (hsep : p.Separable) :
    ∃ T : Finset (AlgebraicClosure F),
      (∀ y ∈ T, (p.map (algebraMap F (AlgebraicClosure F))).eval y = 0 ∧
        (p.map (algebraMap F (AlgebraicClosure F))).eval (y ^ Nat.card F) = 0 ∧
        y ^ Nat.card F ≠ y) ∧
      p.natDegree - p.roots.toFinset.card ≤ T.card := by
  classical
  have := Fintype.ofFinite F
  have hq : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact not_separable_zero hsep
  have hp'0 : p.map (algebraMap F (AlgebraicClosure F)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap F (AlgebraicClosure F)).injective).2 hp0
  have hfrob : ∀ y : AlgebraicClosure F, (p.map (algebraMap F (AlgebraicClosure F))).eval y = 0 →
      (p.map (algebraMap F (AlgebraicClosure F))).eval (y ^ Nat.card F) = 0 := by
    intro y hy
    have h1 : y ^ Nat.card F = FiniteField.frobeniusAlgHom F (AlgebraicClosure F) y := by
      rw [hq]
      rfl
    rw [eval_map_algebraMap] at hy ⊢
    rw [h1, aeval_algHom_apply, hy, map_zero]
  refine ⟨(p.map (algebraMap F (AlgebraicClosure F))).roots.toFinset.filter
    (fun y => y ^ Nat.card F ≠ y), ?_, ?_⟩
  · intro y hy
    rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hp'0, IsRoot.def] at hy
    exact ⟨hy.1, hfrob y hy.1, hy.2⟩
  · have hcard : (p.map (algebraMap F (AlgebraicClosure F))).roots.toFinset.card = p.natDegree := by
      rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep.map),
        ← (IsAlgClosed.splits (p.map (algebraMap F (AlgebraicClosure F)))).natDegree_eq_card_roots,
        natDegree_map]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (p.map (algebraMap F (AlgebraicClosure F))).roots.toFinset)
      (fun y => y ^ Nat.card F ≠ y)
    have hsub : (p.map (algebraMap F (AlgebraicClosure F))).roots.toFinset.filter
        (fun y => ¬ (y ^ Nat.card F ≠ y)) ⊆
        p.roots.toFinset.image (algebraMap F (AlgebraicClosure F)) := by
      intro y hy
      rw [Finset.mem_filter, not_not, Multiset.mem_toFinset, mem_roots hp'0, IsRoot.def] at hy
      obtain ⟨x, rfl⟩ := exists_algebraMap_eq_of_pow_card_eq F y (hq ▸ hy.2)
      refine Finset.mem_image.2 ⟨x, ?_, rfl⟩
      rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot.def]
      have h := hy.1
      rw [eval_map, eval₂_at_apply] at h
      exact (map_eq_zero_iff _ (algebraMap F (AlgebraicClosure F)).injective).1 h
    have hle := (Finset.card_le_card hsub).trans Finset.card_image_le
    omega

/-! ### Telescoping with `divX` -/

/-- For `natDegree f ≤ n`,
`f(y) - f(y') = (y - y') * ∑_{k < n} (divX^[k+1] f)(y) * y' ^ k`. -/
theorem divX_telescoping (R : Type u) [CommRing R] (f : Polynomial R) (n : ℕ)
    (hf : f.natDegree ≤ n) (y y' : R) :
    f.eval y - f.eval y' =
      (y - y') * ∑ k ∈ Finset.range n, (Polynomial.divX^[k + 1] f).eval y * y' ^ k := by
  induction n generalizing f with
  | zero =>
    rw [eq_C_of_natDegree_le_zero hf]
    simp
  | succ n ih =>
    have hd : (divX f).natDegree ≤ n := by
      rw [natDegree_divX_eq_natDegree_tsub_one]
      omega
    have h := ih (divX f) hd
    have e : ∀ z, f.eval z = (divX f).eval z * z + f.coeff 0 := fun z => by
      conv_lhs => rw [← divX_mul_X_add f]
      simp
    have hs : ∀ k, (divX^[k + 1 + 1] f).eval y * y' ^ (k + 1) =
        y' * ((divX^[k + 1] (divX f)).eval y * y' ^ k) := fun k => by
      rw [show divX^[k + 1 + 1] f = divX^[k + 1] (divX f) from
        Function.iterate_succ_apply _ _ _, pow_succ]
      ring
    rw [Finset.sum_range_succ', e y, e y']
    simp only [hs, ← Finset.mul_sum, zero_add, Function.iterate_one, pow_zero, mul_one]
    linear_combination y' * h

end Langlands.AlgebraicGeometry.LangWeil.Stepanov
