import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Uniqueness of Fourier coefficients on finitely generated abelian groups

For a finitely generated commutative group `Γ` and an absolutely summable `f : Γ → ℂ`, if
`∑_γ χ(γ) f(γ) = 0` for every unitary character `χ : Γ → ℂˣ`, then `f = 0`.

The proof goes through the structure theorem `Γ ≅ ℤⁿ × T` with `T` finite: on `ℤⁿ` the
coefficients of an absolutely convergent Fourier series on the torus `(ℝ/ℤ)ⁿ` are recovered by
integration against the monomials, and on `T` by orthogonality of characters.
-/

noncomputable section

open MeasureTheory UnitAddTorus

namespace Langlands.HarmonicAnalysis.DiscreteFourier

universe u

/-- The Fourier transform `f̂(χ) = ∑_γ χ(γ) f(γ)` of `f : Γ → ℂ` at a character `χ : Γ → ℂˣ`.
It is a `tsum`, hence `0` when the family is not summable. -/
def characterSum {Γ : Type u} [Monoid Γ] (f : Γ → ℂ) (χ : Γ →* ℂˣ) : ℂ :=
  ∑' γ, (χ γ : ℂ) * f γ

theorem characterSum_apply {Γ : Type u} [Monoid Γ] (f : Γ → ℂ) (χ : Γ →* ℂˣ) :
    characterSum f χ = ∑' γ, (χ γ : ℂ) * f γ :=
  rfl

section Torus

variable {d : Type*} [Fintype d]

/-- The probability Haar measure on the torus `(ℝ/ℤ)^d`. -/
abbrev torusHaar (d : Type*) [Fintype d] : Measure (UnitAddTorus d) :=
  Measure.pi fun _ : d => (AddCircle.haarAddCircle : Measure UnitAddCircle)

theorem norm_mFourier_apply (n : d → ℤ) (x : UnitAddTorus d) : ‖mFourier n x‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe,
    Finset.prod_const_one]

/-- `∫_{ℝ/ℤ} e(k t) dt = 1` if `k = 0` and `0` otherwise. -/
theorem integral_fourier_haarAddCircle (k : ℤ) :
    ∫ t, fourier k t ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) =
      if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) k) 0
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul] at h
  rw [h, Pi.single_apply]
  simp only [eq_comm]

/-- `∫_{(ℝ/ℤ)^d} e(n · x) dx = 1` if `n = 0` and `0` otherwise. -/
theorem integral_mFourier (n : d → ℤ) :
    ∫ x, mFourier n x ∂torusHaar d = if n = 0 then 1 else 0 := by
  have h : (fun x : UnitAddTorus d => mFourier n x) = fun x => ∏ i, fourier (n i) (x i) := rfl
  rw [h, integral_fintype_prod_eq_prod (fun i t => fourier (n i) t)]
  simp only [integral_fourier_haarAddCircle, Fintype.prod_boole]
  congr 1
  exact propext ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- **Uniqueness on `ℤ^d`**: an absolutely summable `f : ℤ^d → ℂ` whose Fourier series
`∑_m e(m · x) f(m)` vanishes at every point `x` of the torus is zero. -/
theorem eq_zero_of_tsum_mFourier_mul_eq_zero {f : (d → ℤ) → ℂ}
    (hf : Summable fun m => ‖f m‖) (h : ∀ x : UnitAddTorus d, ∑' m, mFourier m x * f m = 0) :
    f = 0 := by
  funext k
  have hint : ∀ m : d → ℤ, Integrable (fun x => mFourier (-k) x * (mFourier m x * f m))
      (torusHaar d) := fun m =>
    (integrable_const ‖f m‖).mono'
      ((((mFourier (-k)).continuous.mul ((mFourier m).continuous.mul
        continuous_const))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, norm_mul, norm_mFourier_apply, norm_mFourier_apply, one_mul, one_mul])
  have hnorm : ∀ m : d → ℤ, ∫ x, ‖mFourier (-k) x * (mFourier m x * f m)‖ ∂torusHaar d =
      ‖f m‖ := fun m => by
    simp only [norm_mul, norm_mFourier_apply, one_mul]
    simp
  have hsum := integral_tsum_of_summable_integral_norm hint (by simpa only [hnorm] using hf)
  have hzero : ∫ x, ∑' m, mFourier (-k) x * (mFourier m x * f m) ∂torusHaar d = 0 := by
    refine (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans
      (integral_zero _ _)
    simp only [tsum_mul_left, h x, mul_zero]
  rw [← hsum] at hzero
  have hterm : ∀ m : d → ℤ, ∫ x, mFourier (-k) x * (mFourier m x * f m) ∂torusHaar d =
      if m = k then f m else 0 := fun m => by
    have : (fun x => mFourier (-k) x * (mFourier m x * f m)) =
        fun x => mFourier (-k + m) x * f m := by
      funext x
      rw [mFourier_add, mul_assoc]
    rw [this, integral_mul_const, integral_mFourier]
    by_cases hm : m = k
    · subst hm; simp
    · have h1 : ¬(-k + m = 0) := fun h' => hm (neg_add_eq_zero.mp h').symm
      simp [h1, hm]
  simp only [hterm, tsum_ite_eq] at hzero
  exact hzero

end Torus

section Finite

variable {T : Type*} [AddCommGroup T] [Fintype T]

/-- **Uniqueness on a finite abelian group**: if `∑_t ψ(t) g(t) = 0` for every character `ψ`
of `T`, then `g = 0`. -/
theorem eq_zero_of_sum_addChar_mul_eq_zero {g : T → ℂ}
    (h : ∀ ψ : AddChar T ℂ, ∑ t, ψ t * g t = 0) : g = 0 := by
  classical
  funext t₀
  have h0 : ∑ ψ : AddChar T ℂ, ψ (-t₀) * ∑ t, ψ t * g t = 0 := by simp [h]
  have h1 : ∑ ψ : AddChar T ℂ, ψ (-t₀) * ∑ t, ψ t * g t =
      ∑ t, (∑ ψ : AddChar T ℂ, ψ (t - t₀)) * g t := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun ψ _ => ?_
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  rw [h1] at h0
  simp only [AddChar.sum_apply_eq_ite, sub_eq_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h0
  have hc : (Fintype.card T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp h0).resolve_left hc

end Finite

section Product

variable {d : Type*} [Fintype d] {T : Type*} [AddCommGroup T] [Fintype T]

/-- **Uniqueness on `ℤ^d × T`** with `T` finite abelian. -/
theorem eq_zero_of_tsum_mFourier_mul_addChar_mul_eq_zero {f : (d → ℤ) × T → ℂ}
    (hf : Summable fun x => ‖f x‖)
    (h : ∀ (θ : UnitAddTorus d) (ψ : AddChar T ℂ),
      ∑' x : (d → ℤ) × T, mFourier x.1 θ * ψ x.2 * f x = 0) :
    f = 0 := by
  have hfib : ∀ t : T, Summable fun m : d → ℤ => ‖f (m, t)‖ := fun t =>
    hf.comp_injective (Prod.mk_left_injective t)
  have hg : ∀ ψ : AddChar T ℂ, (fun m : d → ℤ => ∑ t, ψ t * f (m, t)) = 0 := fun ψ => by
    refine eq_zero_of_tsum_mFourier_mul_eq_zero ?_ fun θ => ?_
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
        (summable_sum (s := Finset.univ) (f := fun t m => ‖f (m, t)‖) fun t _ => hfib t)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
      rw [norm_mul, ψ.norm_apply, one_mul]
    · have hs : Summable fun x : (d → ℤ) × T => mFourier x.1 θ * ψ x.2 * f x :=
        Summable.of_norm_bounded hf fun x => by
          rw [norm_mul, norm_mul, norm_mFourier_apply, ψ.norm_apply, one_mul, one_mul]
      have := h θ ψ
      rw [hs.tsum_prod] at this
      refine (tsum_congr fun m => ?_).trans this
      rw [tsum_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring
  funext x
  obtain ⟨m, t⟩ := x
  have hm : (fun t : T => f (m, t)) = 0 :=
    eq_zero_of_sum_addChar_mul_eq_zero fun ψ => congrFun (hg ψ) m
  exact congrFun hm t

end Product

section FinitelyGenerated

variable {Γ : Type u} [CommGroup Γ]

/-- A finitely generated commutative group is isomorphic to `ℤⁿ × T` for a finite abelian group
`T` (structure theorem, `AddCommGroup.equiv_free_prod_directSum_zmod`). -/
theorem exists_addEquiv_pi_int_prod_finite [Group.FG Γ] :
    ∃ (n : ℕ) (T : Type) (_ : AddCommGroup T) (_ : Fintype T),
      Nonempty (Additive Γ ≃+ (Fin n → ℤ) × T) := by
  obtain ⟨n, ι, _, p, hp, e, ⟨E⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive Γ)
  have hne : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_equiv _ (DFinsupp.equivFunOnFintype (β := fun i => ZMod (p i ^ e i))).symm
  refine ⟨n, DirectSum ι fun i => ZMod (p i ^ e i), inferInstance, Fintype.ofFinite _, ⟨?_⟩⟩
  exact E.trans (AddEquiv.prodCongr (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toAddEquiv
    (AddEquiv.refl _))

/-- A finitely generated commutative group is countable. -/
theorem countable_of_fg [Group.FG Γ] : Countable Γ := by
  obtain ⟨n, T, _, _, ⟨E⟩⟩ := exists_addEquiv_pi_int_prod_finite (Γ := Γ)
  have : Countable (Additive Γ) := Countable.of_equiv _ E.toEquiv.symm
  exact Countable.of_equiv _ Additive.toMul

/-- **Uniqueness of Fourier coefficients on a finitely generated commutative group**: if
`f : Γ → ℂ` is absolutely summable and `∑_γ χ(γ) f(γ) = 0` for every unitary character
`χ : Γ → ℂˣ`, then `f = 0`. -/
theorem eq_zero_of_characterSum_eq_zero [Group.FG Γ] {f : Γ → ℂ}
    (hf : Summable fun γ => ‖f γ‖)
    (h : ∀ χ : Γ →* ℂˣ, (∀ γ, ‖(χ γ : ℂ)‖ = 1) → characterSum f χ = 0) : f = 0 := by
  obtain ⟨n, T, _, _, ⟨E⟩⟩ := exists_addEquiv_pi_int_prod_finite (Γ := Γ)
  let e : Γ ≃ (Fin n → ℤ) × T := Additive.ofMul.trans E.toEquiv
  have he : ∀ a b : Γ, e (a * b) = e a + e b := fun a b => E.map_add (Additive.ofMul a)
    (Additive.ofMul b)
  let F : (Fin n → ℤ) × T → ℂ := fun x => f (e.symm x)
  have hF : F = 0 := by
    refine eq_zero_of_tsum_mFourier_mul_addChar_mul_eq_zero ?_ fun θ ψ => ?_
    · exact (e.symm.summable_iff (f := fun γ => ‖f γ‖)).mpr hf
    · have hz : ∀ γ : Γ, mFourier (e γ).1 θ * ψ (e γ).2 ≠ 0 := fun γ => by
        rw [← norm_ne_zero_iff, norm_mul, norm_mFourier_apply, ψ.norm_apply, one_mul]
        exact one_ne_zero
      let χ : Γ →* ℂˣ := MonoidHom.mk' (fun γ => Units.mk0 _ (hz γ)) fun a b => by
        ext
        simp only [Units.val_mk0, Units.val_mul, he, Prod.fst_add, Prod.snd_add, mFourier_add,
          AddChar.map_add_eq_mul]
        ring
      have hχ : ∀ γ, ‖(χ γ : ℂ)‖ = 1 := fun γ => by
        change ‖mFourier (e γ).1 θ * ψ (e γ).2‖ = 1
        rw [norm_mul, norm_mFourier_apply, ψ.norm_apply, one_mul]
      have := h χ hχ
      rw [characterSum_apply, ← e.symm.tsum_eq] at this
      refine (tsum_congr fun x => ?_).trans this
      change _ = mFourier (e (e.symm x)).1 θ * ψ (e (e.symm x)).2 * f (e.symm x)
      rw [e.apply_symm_apply]
  funext γ
  have := congrFun hF (e γ)
  simpa [F] using this

end FinitelyGenerated

end Langlands.HarmonicAnalysis.DiscreteFourier
