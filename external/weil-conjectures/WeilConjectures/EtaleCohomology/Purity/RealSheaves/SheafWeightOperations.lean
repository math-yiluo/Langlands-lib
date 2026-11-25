/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy
public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed
public import WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine
public import WeilConjectures.Mathlib.Algebra.Polynomial.FieldDivision
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Derivative
public import WeilConjectures.WeilSheaf.StalkPairing
public import WeilConjectures.WeilSheaf.TateTwistCohomology
public import WeilConjectures.WeilSheaf.TensorPower
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Real

/-!
# Weights of Tate twists, duals and tensor powers of Weil sheaves

Sheaf-level versions of the weight rules of the real-sheaves chapter, for lisse Weil sheaves
on a `k₀`-scheme (`AlgebraicGeometry.WeilSheaf`) rather than for Weil group representations.

* The Tate twist `F(n) = ℚ̄_ℓ(n) ⊗ F` is the constant Weil twist `F ⊗ 𝓑_{χ_ℓ(σ)ⁿ}`
  (`AlgebraicGeometry.WeilSheaf.tateTwistSheafTensorObjIso`), with `χ_ℓ(σ) = q⁻¹`, so it shifts
  punctual weights and mixed upper weight bounds by `-2n`.
* The dual of a lisse sheaf punctually pure of weight `w` is punctually pure of weight `-w`.
* For an `ι`-real lisse sheaf `G`, the traces of the local Frobenius powers on the stalks of the
  tensor powers `G^{⊗ k}` are the `k`-th powers of those of `G` (times the rank `1` of the
  constant sheaf), so `G^{⊗ k}` is `ι`-real, and for `k` even the inverse local factors
  `ι det(1 - t Fₓ | (G^{⊗ k})_x̄)⁻¹` have nonnegative coefficients.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.tateTwist` and
  `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.tateTwist`: blueprint
  `proposition-weights-under-usual-operations--14`.
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.dual`: blueprint
`proposition-weights-under-usual-operations--4`.
- `AlgebraicGeometry.WeilSheaf.IsReal.tensorPow` and
  `AlgebraicGeometry.WeilSheaf.IsReal.inv_localPolynomial_stalk_tensorPow_nonneg`: blueprint
  `lemma-positivity-euler-factors--1`.
-/

@[expose] public section

universe u v

open CategoryTheory PowerSeries

open scoped ComplexOrder TensorProduct

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- The traces of the powers of the Frobenius of a tensor product are the products of the
traces. -/
theorem trace_frobeniusEnd_pow_tensor (M : FrobeniusModule.{u, v} K)
    (N : FrobeniusModule.{u, v} K) (n : ℕ) :
    LinearMap.trace K (M.tensor N).carrier ((M.tensor N).frobeniusEnd ^ n) =
      LinearMap.trace K M.carrier (M.frobeniusEnd ^ n) *
        LinearMap.trace K N.carrier (N.frobeniusEnd ^ n) := by
  have key (f : Module.End K M.carrier) (g : Module.End K N.carrier) :
      LinearMap.trace K (M.carrier ⊗[K] N.carrier) (TensorProduct.map f g ^ n) =
        LinearMap.trace K M.carrier (f ^ n) * LinearMap.trace K N.carrier (g ^ n) := by
    rw [TensorProduct.map_pow, LinearMap.trace_tensorProduct']
  rw [frobeniusEnd_tensor]
  exact key _ _

/-- The constant coefficient of the complex inverse local factor `ι det(1 - t F)⁻¹` is `1`. -/
theorem constantCoeff_inv_map_localPolynomial (ι : K →+* ℂ) (M : FrobeniusModule.{u, v} K) :
    constantCoeff (((M.localPolynomial.map ι : Polynomial ℂ) : ℂ⟦X⟧))⁻¹ = 1 := by
  rw [PowerSeries.constantCoeff_inv, Polynomial.constantCoeff_coe, Polynomial.coeff_map,
    localPolynomial, LinearMap.coeff_zero_charpolyRev, map_one, inv_one]

/-- If the `ι`-images of the traces `tr(Fⁿ)`, `n ≥ 1`, of the powers of the Frobenius are
nonnegative reals, then the complex inverse local factor `ι det(1 - t F)⁻¹` has nonnegative
real coefficients: by `det (1 - t F)⁻¹ = exp (∑ tr(Fⁿ) tⁿ / n)`
(`PowerSeries.coeff_inv_prod_one_sub_C_mul_X_nonneg`). -/
theorem coeff_inv_map_localPolynomial_nonneg [IsAlgClosed K] (ι : K →+* ℂ)
    (M : FrobeniusModule.{u, v} K)
    (h : ∀ n, 0 < n → 0 ≤ ι (LinearMap.trace K M.carrier (M.frobeniusEnd ^ n))) (k : ℕ) :
    0 ≤ coeff k (((M.localPolynomial.map ι : Polynomial ℂ) : ℂ⟦X⟧))⁻¹ := by
  have hP : ((M.localPolynomial.map ι : Polynomial ℂ) : ℂ⟦X⟧) =
      (((M.frobeniusEnd.charpoly.roots.map ι).map fun c ↦ 1 - PowerSeries.C c * X)).prod := by
    rw [localPolynomial, LinearMap.charpolyRev_eq_prod_roots,
      Polynomial.map_multiset_prod_one_sub_C_mul_X,
      ← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
    exact congrArg _ (Multiset.map_congr rfl fun c _ ↦ by simp)
  rw [hP]
  refine coeff_inv_prod_one_sub_C_mul_X_nonneg _ (fun n hn ↦ ?_) k
  have := h n hn
  rw [LinearMap.trace_pow_eq_sum_pow_roots_charpoly, map_multiset_sum, Multiset.map_map] at this
  simpa [Multiset.map_map, Function.comp_def] using this

end FrobeniusModule

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-! ### Tate twists -/

section TateTwist

variable (k₀ l) in
/-- The Tate twist `F(m) = ℚ̄_ℓ(m) ⊗ F` of a Weil sheaf (the tensor product with the lisse Tate
sheaf, as in `AlgebraicGeometry.WeilComplex.tateTwist`) is the constant Weil twist
`F ⊗ 𝓑_{χ_ℓ(σ)ᵐ}`: `ℚ̄_ℓ(m)` is `ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)ᵐ}`, its dual is `ℚ̄_ℓ ⊗ 𝓑_{χ_ℓ(σ)⁻ᵐ}`, and
`𝓗om(ℚ̄_ℓ ⊗ 𝓑_b, F) ≅ F ⊗ 𝓑_{b⁻¹}`. (blueprint: `prose-10-21`) -/
noncomputable def tateTwistSheafTensorObjIso (m : ℤ) (F : WeilSheaf k₀ l X) :
    (tateTwistSheaf k₀ l X m).tensorObj F (isLisse_tateTwistSheaf k₀ l X m) ≅
      F.constantTwist (cyclotomicUnit k₀ l ^ m) :=
  ObjectProperty.isoMk _
    (ProEtaleWeilSheaf.ihomMapIsoLeft
        (dualObjIsoOfIso _ _ (tateTwistSheafObjIso k₀ l X m)).symm F.obj ≪≫
      ProEtaleWeilSheaf.ihomConstantTwistLeftIso _ _ _ ≪≫
      (ProEtaleWeilSheaf.constantTwist k₀ l X _).mapIso
        (ProEtaleWeilSheaf.ihomAdicConstantIso _) ≪≫
      ProEtaleWeilSheaf.constantTwistCongrIso (inv_inv _) _ ≪≫
      (F.constantTwistObjIso _).symm)

/-- The constant `χ_ℓ(σ)ᵐ = q⁻ᵐ` of the Tate twist `(m)` has `2 log_q |ι χ_ℓ(σ)ᵐ| = -2m`. -/
lemma two_mul_logb_norm_cyclotomicUnit_zpow (ι : PadicAlgCl l →+* ℂ) (m : ℤ) :
    2 * Real.logb (Nat.card k₀) ‖ι (cyclotomicUnit k₀ l ^ m : (PadicAlgCl l)ˣ)‖ = -(2 * m) := by
  have hq : (1 : ℝ) < Nat.card k₀ := by exact_mod_cast Finite.one_lt_card
  rw [cyclotomicUnit_zpow_eq, map_zpow₀, map_natCast, norm_zpow, Complex.norm_natCast,
    ← Real.rpow_intCast, Real.logb_rpow (by positivity) hq.ne']
  push_cast
  ring

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- **Weight shift under a Tate twist.** If a Weil sheaf `F` is punctually `ι`-pure of weight
`w`, its Tate twist `F(n) = ℚ̄_ℓ(n) ⊗ F` is punctually `ι`-pure of weight `w - 2n`, for every
`n ∈ ℤ`: at a closed point of degree `m` the local Frobenius of `F(n)` is `q^{-mn}` times that
of `F`. (blueprint: `proposition-weights-under-usual-operations--14`) -/
theorem IsPunctuallyPureOfWeight.tateTwist {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}
    {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) (n : ℤ) :
    ((tateTwistSheaf k₀ l X n).tensorObj F (isLisse_tateTwistSheaf k₀ l X n)
      ).IsPunctuallyPureOfWeight ι (w - 2 * n) := by
  have := h.constantTwist (two_mul_logb_norm_cyclotomicUnit_zpow ι n)
  rw [← sub_eq_add_neg] at this
  exact this.of_epi (tateTwistSheafTensorObjIso k₀ l n F).inv

/-- **Weight shift under a Tate twist, for upper bounds.** If a Weil sheaf `F` is `ι`-mixed of
weights at most `w`, its Tate twist `F(n) = ℚ̄_ℓ(n) ⊗ F` is `ι`-mixed of weights at most
`w - 2n`, for every `n ∈ ℤ`. (blueprint: `proposition-weights-under-usual-operations--14`) -/
theorem IsMixedOfWeightsAtMost.tateTwist {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}
    {w : ℝ} (h : F.IsMixedOfWeightsAtMost ι w) (n : ℤ) :
    ((tateTwistSheaf k₀ l X n).tensorObj F (isLisse_tateTwistSheaf k₀ l X n)
      ).IsMixedOfWeightsAtMost ι (w - 2 * n) := by
  have := h.constantTwist (two_mul_logb_norm_cyclotomicUnit_zpow ι n)
  rw [← sub_eq_add_neg] at this
  exact this.of_iso (tateTwistSheafTensorObjIso k₀ l n F).symm

/-- **Weight shift under a Tate twist, for punctual upper bounds.** If a Weil sheaf `F` has
punctual weights at most `w`, its Tate twist `F(n) = ℚ̄_ℓ(n) ⊗ F` has punctual weights at most
`w - 2n`. (blueprint: `proposition-weights-under-usual-operations--14`) -/
theorem HasWeightsAtMost.tateTwist {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}
    {w : ℝ} (h : F.HasWeightsAtMost ι w) (n : ℤ) :
    ((tateTwistSheaf k₀ l X n).tensorObj F (isLisse_tateTwistSheaf k₀ l X n)
      ).HasWeightsAtMost ι (w - 2 * n) := by
  have hT : (tateTwistSheaf k₀ l X n).HasWeightsAtMost ι (-(2 * n)) := by
    have := ((isPunctuallyPureOfWeight_adicConstant (k₀ := k₀) (l := l) (X := X)
      (ι := ι)).constantTwist (two_mul_logb_norm_cyclotomicUnit_zpow ι n)).of_epi
        (tateTwistSheafIso k₀ l X n).inv
    rw [zero_add] at this
    exact this.hasWeightsAtMost
  have := hT.tensorObj (isLisse_tateTwistSheaf k₀ l X n) h
  rwa [neg_add_eq_sub] at this

end TateTwist

/-! ### Duals -/

/-- **Weight of the linear dual.** If a lisse Weil sheaf `F` is punctually `ι`-pure of weight
`w`, its dual `F^∨` is punctually `ι`-pure of weight `-w`: the local Frobenius eigenvalues of
`F^∨` are the inverses of those of `F`. (blueprint:
`proposition-weights-under-usual-operations--4`) -/
theorem IsPunctuallyPureOfWeight.dual {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse) {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) :
    (F.dual hF).IsPunctuallyPureOfWeight ι (-w) := fun x ↦ by
  obtain ⟨e⟩ := nonempty_equiv_stalk_dual hF x
  exact FrobeniusModule.IsPureOfWeight.of_equiv e (h x).dual

/-! ### Tensor powers of real sheaves -/

section TensorPow

/-- The local Frobenius of the constant Weil sheaf `ℚ̄_ℓ` at a closed point is the identity. -/
lemma frobeniusEnd_stalk_adicConstant (x : X.finitePoints) :
    ((adicConstant k₀ l X).stalk x).frobeniusEnd = 1 := by
  rw [FrobeniusModule.frobeniusEnd, stalk, adicConstant_stalkAt_frobenius]
  rfl

/-- The traces of the powers of the local Frobenius on the stalk of a tensor power `F^{⊗ k}` are
the `k`-th powers of those on the stalk of `F`, times the rank of the constant sheaf: the
eigenvalues of `Fₓⁿ` on `(F^{⊗ k})_x̄` are the `k`-fold products of those on `F_x̄`. -/
theorem trace_frobeniusEnd_pow_stalk_tensorPow {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (x : X.finitePoints) (n : ℕ) :
    ∀ k : ℕ, LinearMap.trace _ _ (((F.tensorPow hF k).stalk x).frobeniusEnd ^ n) =
      LinearMap.trace _ _ ((F.stalk x).frobeniusEnd ^ n) ^ k *
        (Module.finrank (PadicAlgCl l) ((adicConstant k₀ l X).stalk x).carrier : PadicAlgCl l)
  | 0 => by
    change LinearMap.trace _ _ (((adicConstant k₀ l X).stalk x).frobeniusEnd ^ n) = _
    rw [frobeniusEnd_stalk_adicConstant, one_pow, LinearMap.trace_one, pow_zero, one_mul]
  | k + 1 => by
    change LinearMap.trace _ _ (((F.tensorObj (F.tensorPow hF k) hF).stalk x).frobeniusEnd ^ n) =
      _
    rw [← (stalkTensorObjEquiv F (F.tensorPow hF k) hF x).trace_frobeniusEnd_pow,
      FrobeniusModule.trace_frobeniusEnd_pow_tensor,
      trace_frobeniusEnd_pow_stalk_tensorPow hF x n k]
    ring

/-- **Tensor powers of a real sheaf are real.** Every tensor power `G^{⊗ k}` of a lisse
`ι`-real Weil sheaf `G` is `ι`-real: at every closed point `x` the local characteristic
polynomial `ι det(1 - t Fₓ | (G^{⊗ k})_x̄)` has real coefficients.
(blueprint: `lemma-positivity-euler-factors--1`, part (i)) -/
theorem IsReal.tensorPow {ι : PadicAlgCl l →+* ℂ} {G : WeilSheaf k₀ l X} (hG : G.IsLisse)
    (h : G.IsReal ι) (k : ℕ) : (G.tensorPow hG k).IsReal ι := fun x ↦ by
  rw [FrobeniusModule.isReal_iff_forall_trace_pow]
  intro m
  rw [trace_frobeniusEnd_pow_stalk_tensorPow hG x m k, map_mul, map_pow, map_natCast, map_mul,
    map_pow, map_natCast, ((FrobeniusModule.isReal_iff_forall_trace_pow ι _).1 (h x) m)]

/-- **Even tensor powers of a real sheaf are positive.** Let `G` be a lisse `ι`-real Weil sheaf
and `k` an even natural number. At every closed point `x`, the power series
`ι det(1 - t Fₓ | (G^{⊗ k})_x̄)⁻¹ = ∑ aₙ tⁿ` has nonnegative real coefficients `aₙ ≥ 0`, and its
constant term is `1`: by `det (1 - t M)⁻¹ = exp (∑ tr(Mⁿ) tⁿ / n)`, it suffices that the traces
`ι tr(Fₓⁿ | (G^{⊗ k})_x̄) = (ι tr(Fₓⁿ | G_x̄))ᵏ` are nonnegative, and they are even powers of real
numbers. (blueprint: `lemma-positivity-euler-factors--1`, part (ii)) -/
theorem IsReal.inv_localPolynomial_stalk_tensorPow_nonneg {ι : PadicAlgCl l →+* ℂ}
    {G : WeilSheaf k₀ l X} (hG : G.IsLisse) (h : G.IsReal ι) (x : X.finitePoints) {k : ℕ}
    (hk : Even k) :
    (∀ n, 0 ≤ coeff n
      ((((G.tensorPow hG k).stalk x).localPolynomial.map ι : Polynomial ℂ) : ℂ⟦X⟧)⁻¹) ∧
      constantCoeff
        ((((G.tensorPow hG k).stalk x).localPolynomial.map ι : Polynomial ℂ) : ℂ⟦X⟧)⁻¹ = 1 := by
  refine ⟨FrobeniusModule.coeff_inv_map_localPolynomial_nonneg ι _ fun m _ ↦ ?_,
    FrobeniusModule.constantCoeff_inv_map_localPolynomial ι _⟩
  rw [trace_frobeniusEnd_pow_stalk_tensorPow hG x m k, map_mul, map_pow, map_natCast,
    ← Complex.conj_eq_iff_re.1 ((FrobeniusModule.isReal_iff_forall_trace_pow ι _).1 (h x) m),
    ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
  exact Complex.zero_le_real.2 (mul_nonneg (hk.pow_nonneg _) (Nat.cast_nonneg _))

end TensorPow

end AlgebraicGeometry.WeilSheaf
