import Langlands.GroupScheme.Rational.TorusLinearization.Complement
import Langlands.GroupScheme.Rational.TorusLinearization.NoetherianInverse

/-! # Linearizing coordinates from a stable space of additive polynomials -/

noncomputable section

universe u

open MvPolynomial

namespace Langlands.GroupScheme.TorusLinearization

section LinearPart

variable {n : ℕ} {k : Type u} [Field k]

/-- The linear part of a polynomial: its coefficients at the variables. -/
def linPart : MvPolynomial (Fin n) k →ₗ[k] (Fin n → k) :=
  LinearMap.pi fun j => MvPolynomial.lcoeff k (Finsupp.single j 1)

theorem linPart_apply (f : MvPolynomial (Fin n) k) (j : Fin n) :
    linPart f j = f.coeff (Finsupp.single j 1) := rfl

theorem linPart_X (i : Fin n) : linPart (X i : MvPolynomial (Fin n) k) = Pi.single i 1 := by
  classical
  funext j
  rw [linPart_apply, coeff_X, Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · have h' : Finsupp.single i 1 ≠ Finsupp.single j 1 := fun e =>
      h ((Finsupp.single_left_inj one_ne_zero).mp e).symm
    simp [h, h']

theorem linPart_sum_smul (c : Fin n → k) (Φ : Fin n → MvPolynomial (Fin n) k)
    (hΦ : ∀ j, linPart (Φ j) = Pi.single j 1) : linPart (∑ j, c j • Φ j) = c := by
  simp only [map_sum, map_smul, hΦ]
  funext i
  simp [Pi.single_apply]

variable {p : ℕ} [hp : Fact p.Prime]

/-- The higher additive polynomials have no linear part. -/
theorem linPart_eq_zero_of_mem_higher {f : MvPolynomial (Fin n) k} (hf : f ∈ higher n k p) :
    linPart f = 0 := by
  have hle : higher n k p ≤ LinearMap.ker linPart := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨l, rfl⟩, s, hs, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext j
    rw [linPart_apply, X_pow_eq_monomial, coeff_monomial, Pi.zero_apply]
    split_ifs with h
    · exfalso
      rcases Finsupp.single_eq_single_iff _ _ _ _ |>.mp h with ⟨-, h1⟩ | ⟨-, h1⟩
      · exact (Nat.one_lt_pow (by omega) hp.out.one_lt).ne' h1
      · exact one_ne_zero h1
    · rfl
  exact hle hf

variable [CharP k p]

/-- The Frobenius span of a space of additive polynomials has no linear parts beyond those of
the space itself. -/
theorem linPart_mem_map_of_mem_frobSpan {W : Submodule k (MvPolynomial (Fin n) k)}
    (hWA : W ≤ addSpan n k p) {f : MvPolynomial (Fin n) k}
    (hf : f ∈ frobSpan k p 0 (W : Set (MvPolynomial (Fin n) k))) :
    linPart f ∈ W.map linPart := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, r, -, rfl⟩ := hx
    rcases r with _ | r
    · rw [pow_zero, pow_one]
      exact Submodule.mem_map_of_mem hw
    · have hh : w ^ p ^ (r + 1) ∈ higher n k p :=
        pow_mem_of_mem_addSpan (CharP.cast_eq_zero k p)
          (fun l s hs => show X l ^ p ^ s ∈ frobSpan k p 1 (Set.range X) from
            pow_mem_frobSpan ⟨l, rfl⟩ (by omega)) (hWA hw)
      rw [linPart_eq_zero_of_mem_higher hh]
      exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end LinearPart

namespace PointAction

variable {k K I : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ}

/-- A stable space of additive polynomials, without nonzero elements of vanishing linear part,
whose Frobenius span contains the variables, yields linearizing coordinates: a basis `Φ` of
the space, adapted to the linear parts, is an additive change of coordinates, and every point
acts on it through a matrix. -/
theorem exists_linearizing_of_subspace (a : PointAction k K I n) (p : ℕ) [Fact p.Prime]
    [CharP k p] (W : Submodule k (MvPolynomial (Fin n) k)) (hWA : W ≤ addSpan n k p)
    (hWs : a.Stable W)
    (hinj : ∀ w ∈ W, (∀ j, w.coeff (Finsupp.single j 1) = 0) → w = 0)
    (hgen : ∀ j, (MvPolynomial.X j : MvPolynomial (Fin n) k) ∈ frobSpan k p 0 (W : Set _)) :
    ∃ Φ Q : Fin n → MvPolynomial (Fin n) k, (∀ i, IsAddPoly (Φ i)) ∧
      (∀ j, MvPolynomial.aeval Φ (Q j) = MvPolynomial.X j) ∧
      (∀ i, MvPolynomial.aeval Q (Φ i) = MvPolynomial.X i) ∧
      ∀ (B : Type u) [CommRing B] [Algebra k B] (t : a.Pt B), ∃ b : Fin n → Fin n → B,
        ∀ i, a.pull t (Φ i) = ∑ j, b i j • MvPolynomial.map (algebraMap k B) (Φ j) := by
  -- Elements of `W` with prescribed linear parts `e_i`.
  have hΦ : ∀ i, ∃ φ ∈ W, linPart φ = Pi.single i 1 := fun i => by
    have h := linPart_mem_map_of_mem_frobSpan hWA (hgen i)
    rw [linPart_X] at h
    exact Submodule.mem_map.mp h
  choose Φ hΦW hΦl using hΦ
  -- Every element of `W` is the combination of the `Φ j` given by its linear part.
  have hrepr : ∀ w ∈ W, w = ∑ j, linPart w j • Φ j := fun w hw => by
    have hd : w - ∑ j, linPart w j • Φ j ∈ W :=
      sub_mem hw (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hΦW j))
    refine sub_eq_zero.mp (hinj _ hd fun j => ?_)
    rw [← linPart_apply, map_sub, linPart_sum_smul _ _ hΦl, sub_self, Pi.zero_apply]
  -- Hence `W` lies in the image of substitution of `Φ`, and so does its Frobenius span.
  have hrange : ∀ w ∈ W, w ∈ (aeval Φ).range := fun w hw => by
    refine (AlgHom.mem_range _).mpr ⟨∑ j, linPart w j • (X j : MvPolynomial (Fin n) k), ?_⟩
    simp only [map_sum, map_smul, aeval_X]
    exact (hrepr w hw).symm
  have hspan : frobSpan k p 0 (W : Set (MvPolynomial (Fin n) k)) ≤
      Subalgebra.toSubmodule (aeval Φ).range := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, hw, r, -, rfl⟩
    exact Subalgebra.pow_mem _ (hrange w hw) _
  have hQ : ∀ j, ∃ q, aeval Φ q = X j := fun j => (AlgHom.mem_range _).mp (hspan (hgen j))
  choose Q hQ using hQ
  refine ⟨Φ, Q, fun i => addSpan_le_addPolys (CharP.cast_eq_zero k p) (hWA (hΦW i)), hQ,
    aeval_eq_X_of_aeval_eq_X Φ Q hQ, fun B _ _ t => ?_⟩
  -- Linearity: stability puts `pull t (Φ i)` in the `B`-span of the `Φ j`.
  have hle : Submodule.span B (MvPolynomial.map (algebraMap k B) '' (W : Set _)) ≤
      Submodule.span B (Set.range fun j => MvPolynomial.map (algebraMap k B) (Φ j)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, hrepr w hw, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hb : ∀ i, ∃ c : Fin n → B,
      ∑ j, c j • MvPolynomial.map (algebraMap k B) (Φ j) = a.pull t (Φ i) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun B).mp (hle (hWs B t (Φ i) (hΦW i)))
  choose b hb using hb
  exact ⟨b, fun i => (hb i).symm⟩

end PointAction

end Langlands.GroupScheme.TorusLinearization
