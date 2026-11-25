/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RingTheory.PowerSeries.Expand
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LFunction
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation
public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius
public import WeilConjectures.WeilSheaf.Curve
import WeilConjectures.WeilSheaf.CurveTopCohomology
import Mathlib.Algebra.Order.Star.Real

/-!
# The ingredients of the Rankin–Selberg bound

This file collects the inputs of the Rankin–Selberg argument of
`proposition-bound-largest-determinant-weight--1`, which bounds the local Frobenius eigenvalues of
an `ι`-real lisse Weil sheaf on an affine curve by the largest determinant weight of its
constituents.

* Tensor squares: the tensor square `ℱ ⊗ ℱ` of a lisse, `ι`-real Weil sheaf is lisse and
  `ι`-real, and `α ^ 2` is a local eigenvalue of `ℱ ⊗ ℱ` whenever `α` is one of `ℱ`.
* `proposition-weights-under-usual-operations--14`: a Tate twist `ℱ (n)` shifts weights by `-2 n`.
* `lemma-positivity-euler-factors--1`: the inverse local factors of the tensor square of an
  `ι`-real sheaf have nonnegative coefficients.
* `proposition-bound-largest-determinant-weight`: the eigenvalues of the geometric Frobenius on
  the coinvariant Tate twist `V_{π₁(U)} (-1) = H_c² (U, ℱ)` are determinant weights.
* `theorem-trace-formula-euler-product--4`: the Euler series of `ℱ` times
`det (1 - F T ∣ H_c² (U, ℱ))` is a
  polynomial, namely `det (1 - F T ∣ H_c¹ (U, ℱ))`.

## Implementation notes

`H_c² (U, ℱ)` is not available for a Weil representation, only for a Weil sheaf. By global
Verdier duality on the smooth nonproper curve `U` it is the coinvariant Tate twist
`V_{π₁(U)} (-1)`, on which the geometric Frobenius acts as `q` times the endomorphism induced by
the degree-one lift `γ`; that endomorphism, `AlgebraicGeometry.WeilGroup.compactTopFrobenius`,
is used here in its place. The numerator `det (1 - F T ∣ H_c¹ (U, ℱ))` of the Euler product is only
asserted to be some polynomial, which is all that the Rankin–Selberg argument uses.

The Euler product identity `AlgebraicGeometry.WeilGroup.exists_eulerSeries_mul_eq_coe` is the
Grothendieck–Lefschetz trace formula for the lisse Weil sheaf attached to the representation
(`AlgebraicGeometry.WeilGroup.exists_weilSheaf_of_isLisse`), in the sheaf form
`AlgebraicGeometry.WeilSheaf.coeff_prod_inv_localPolynomial_stalk_eq`. It needs `ℓ ≠ char 𝔽_q`:
for `ℓ = p` the `L`-function of a `p`-adic character of infinite geometric image, such as that
of an Artin–Schreier–Witt `ℤ_p`-tower, is not rational.

## Main definitions

- `AlgebraicGeometry.WeilGroup.compactTopFrobenius`: the geometric Frobenius on `H_c² (U, ℱ)`.

## Main statements

- `AlgebraicGeometry.WeilGroup.IsLisse.tprod`, `AlgebraicGeometry.WeilGroup.IsReal.tprod`
- `AlgebraicGeometry.WeilGroup.IsPunctuallyPure.tprod_tateLine`,
  `AlgebraicGeometry.WeilGroup.HasWeightsAtMost.tprod_tateLine`
- `AlgebraicGeometry.WeilGroup.IsReal.hasNonnegCoeffs_eulerFactor_tprod_self`
- `AlgebraicGeometry.WeilGroup.exists_isConstituent_hasDetWeight_of_hasEigenvalue`
- `AlgebraicGeometry.WeilGroup.exists_eulerSeries_mul_eq_coe`
-/

@[expose] public section

universe u

open CategoryTheory

open scoped TensorProduct

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

variable {W : WeilGroup p} {l : ℕ} [Fact l.Prime] {V V' : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V] [AddCommGroup V']
  [Module (PadicAlgCl l) V'] [FiniteDimensional (PadicAlgCl l) V']
  {ρ : Representation (PadicAlgCl l) W.carrier V} {σ : Representation (PadicAlgCl l) W.carrier V'}
  (ι : PadicAlgCl l →+* ℂ)

section TensorProduct

/-- The tensor product of two lisse Weil representations is lisse: on a pure tensor, a
coefficient of the tensor product is a fixed linear combination of products of coefficients of
the factors. -/
theorem IsLisse.tprod (hρ : W.IsLisse l ρ) (hσ : W.IsLisse l σ) : W.IsLisse l (ρ.tprod σ) :=
  IsLisse.of_continuous_apply fun φ x ↦ by
    induction x using TensorProduct.inductionOn with
    | tmul v w =>
      let b := Module.finBasis (PadicAlgCl l) V
      let b' := Module.finBasis (PadicAlgCl l) V'
      have key (g : W.geometric) : φ (ρ.tprod σ g (v ⊗ₜ w)) =
          ∑ i, ∑ j, b.coord i (ρ g v) * b'.coord j (σ g w) * φ (b i ⊗ₜ b' j) := by
        rw [Representation.tprod_apply, TensorProduct.map_tmul]
        conv_lhs => rw [← b.sum_repr (ρ g v), ← b'.sum_repr (σ g w)]
        simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
          TensorProduct.smul_tmul_smul, map_smul, smul_eq_mul, Module.Basis.coord_apply]
        exact Finset.sum_comm
      simp_rw [key]
      exact continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
        ((hρ.continuous_apply _ _).mul (hσ.continuous_apply _ _)).mul continuous_const
    | add x y hx hy => exact (hx.add hy).congr fun g ↦ by simp

/-- Blueprint `lemma-filtrations-spectra`: the local eigenvalues of a tensor product are the
pairwise products of the local eigenvalues of the factors. -/
theorem localEigenvalues_tprod (x : C.finitePoints) :
    W.localEigenvalues l (ρ.tprod σ) x =
      (W.localEigenvalues l ρ x ×ˢ W.localEigenvalues l σ x).map fun a ↦ a.1 * a.2 :=
  LinearMap.charpoly_roots_tensorProduct _ _

/-- If `α` is a local eigenvalue of `ℱ`, then `α ^ 2` is a local eigenvalue of `ℱ ⊗ ℱ`. -/
theorem sq_mem_localEigenvalues_tprod_self {x : C.finitePoints} {α : PadicAlgCl l}
    (hα : α ∈ W.localEigenvalues l ρ x) : α ^ 2 ∈ W.localEigenvalues l (ρ.tprod ρ) x := by
  rw [localEigenvalues_tprod, sq]
  exact Multiset.mem_map_of_mem (fun a ↦ a.1 * a.2)
    (show (α, α) ∈ _ ×ˢ _ from Multiset.mem_product.2 ⟨hα, hα⟩)

/-- Mapping the pairwise products of two multisets along a ring homomorphism. -/
theorem _root_.Multiset.map_map_product_mul {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s t : Multiset R) :
    ((s ×ˢ t).map fun a ↦ a.1 * a.2).map f = ((s.map f) ×ˢ (t.map f)).map fun a ↦ a.1 * a.2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.cons_product, Multiset.map_add, Multiset.map_cons, ih, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun b _ ↦ by simp

/-- The tensor product of two `ι`-real Weil representations is `ι`-real: its multiset of complex
local eigenvalues consists of the pairwise products of two conjugation-stable multisets. -/
theorem IsReal.tprod (hρ : W.IsReal l ρ ι) (hσ : W.IsReal l σ ι) :
    W.IsReal l (ρ.tprod σ) ι := by
  refine isReal_of_map_conj_localEigenvalues ι fun x ↦ ?_
  rw [localEigenvalues_tprod, Multiset.map_map_product_mul, Multiset.map_map_product_mul,
    hρ.map_conj_localEigenvalues, hσ.map_conj_localEigenvalues]

/-- The tensor square `ℱ ⊗ ℱ` of a sheaf with weights at most `β` has weights at most `2 β`. -/
theorem HasWeightsAtMost.tprod_self {β : ℝ} (hw : W.HasWeightsAtMost l ρ ι β) :
    W.HasWeightsAtMost l (ρ.tprod ρ) ι (2 * β) := by
  intro x γ hγ
  rw [localEigenvalues_tprod] at hγ
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Multiset.mem_map.1 hγ
  rw [Multiset.mem_product] at hab
  rw [frobeniusWeight_mul ι _ (fun h ↦ zero_notMem_localEigenvalues x (h ▸ hab.1))
    (fun h ↦ zero_notMem_localEigenvalues x (h ▸ hab.2))]
  linarith [hw x a hab.1, hw x b hab.2]

end TensorProduct

section TateTwist

/-- The `ι`-weight of the Frobenius scalar `q ^ (-n e)` of the Tate line at a point of degree
`e` is `-2 n`. -/
private theorem frobeniusWeight_zpow_card {e : ℕ} (he : e ≠ 0) (n : ℤ) :
    frobeniusWeight ι (Nat.card K ^ e) (((Nat.card K : PadicAlgCl l) ^ (-n)) ^ e) = -2 * n := by
  have hq : (1 : ℝ) < Nat.card K := by
    exact_mod_cast Finite.one_lt_card_iff_nontrivial.2 inferInstance
  have hlog : Real.log (Nat.card K) ≠ 0 := (Real.log_pos hq).ne'
  simp only [frobeniusWeight, map_pow, map_zpow₀, map_natCast, norm_pow, norm_zpow,
    Complex.norm_natCast, Nat.cast_pow, Real.log_pow, Real.log_zpow, Int.cast_neg]
  field_simp

/-- The local eigenvalues of the Tate twist `ℱ (n) = ℱ ⊗ ℚ̄_ℓ (n)` at a closed point `x` of
degree `e` are the `α q ^ (-n e)` for the local eigenvalues `α` of `ℱ`. -/
theorem localEigenvalues_tprod_tateLine (n : ℤ) (x : C.finitePoints) :
    W.localEigenvalues l (ρ.tprod (W.tateLine l n)) x =
      (W.localEigenvalues l ρ x).map
        (· * ((Nat.card K : PadicAlgCl l) ^ (-n)) ^ p.degreeOver x.1) := by
  set c := ((Nat.card K : PadicAlgCl l) ^ (-n)) ^ p.degreeOver x.1
  have h : W.tateLine l n (W.frobenius x) = c • LinearMap.id := by
    ext
    simp [c, tateLine, constLine, W.deg_frobenius x, Units.smul_def, inv_pow]
  have hT : (W.tateLine l n (W.frobenius x)).charpoly.roots = {c} := by
    have hc : c ∈ (W.tateLine l n (W.frobenius x)).charpoly.roots := by
      rw [Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
        ← Module.End.hasEigenvalue_iff_isRoot_charpoly, h]
      refine Module.End.hasEigenvalue_of_hasEigenvector (x := 1) ⟨?_, one_ne_zero⟩
      simp
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.1 (show Multiset.card
        (W.tateLine l n (W.frobenius x)).charpoly.roots = 1 by
      rw [LinearMap.card_roots_charpoly, Module.finrank_self])
    rw [ha, Multiset.mem_singleton] at hc
    rw [ha, hc]
  unfold localEigenvalues
  rw [Representation.tprod_apply, LinearMap.charpoly_roots_tensorProduct, hT]
  induction (ρ (W.frobenius x)).charpoly.roots using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

/-- Blueprint `proposition-weights-under-usual-operations--14`: Weight shift under a Tate twist.

If `ℱ` is punctually `ι`-pure of weight `w`, its Tate twist `ℱ (n)` is punctually `ι`-pure of
weight `w - 2 n`: at a closed point `y` of degree `e` the local Frobenius of the twist is
`q ^ (-n e)` times that of `ℱ`, and `|ι (q ^ (-n e) α)| = q_y ^ ((w - 2 n) / 2)`. -/
theorem IsPunctuallyPure.tprod_tateLine {w : ℝ} (h : W.IsPunctuallyPure l ρ ι w) (n : ℤ) :
    W.IsPunctuallyPure l (ρ.tprod (W.tateLine l n)) ι (w - 2 * n) := by
  intro x β hβ
  rw [localEigenvalues_tprod_tateLine, Multiset.mem_map] at hβ
  obtain ⟨α, hα, rfl⟩ := hβ
  have he := p.degreeOver_ne_zero x.2
  rw [frobeniusWeight_mul ι _ (fun h ↦ zero_notMem_localEigenvalues x (h ▸ hα))
    (pow_ne_zero _ (zpow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne'))), h x α hα,
    Scheme.Hom.pointNorm_eq_pow_degreeOver p x.2, frobeniusWeight_zpow_card ι he]
  ring

/-- Blueprint `proposition-weights-under-usual-operations--14`: Weight shift under a Tate twist.

If `ℱ` has weights at most `w`, its Tate twist `ℱ (n)` has weights at most `w - 2 n`. -/
theorem HasWeightsAtMost.tprod_tateLine {w : ℝ} (h : W.HasWeightsAtMost l ρ ι w) (n : ℤ) :
    W.HasWeightsAtMost l (ρ.tprod (W.tateLine l n)) ι (w - 2 * n) := by
  intro x β hβ
  rw [localEigenvalues_tprod_tateLine, Multiset.mem_map] at hβ
  obtain ⟨α, hα, rfl⟩ := hβ
  have he := p.degreeOver_ne_zero x.2
  rw [frobeniusWeight_mul ι _ (fun h ↦ zero_notMem_localEigenvalues x (h ▸ hα))
    (pow_ne_zero _ (zpow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne'))),
    Scheme.Hom.pointNorm_eq_pow_degreeOver p x.2, frobeniusWeight_zpow_card ι he]
  have := h x α hα
  rw [Scheme.Hom.pointNorm_eq_pow_degreeOver p x.2] at this
  linarith

end TateTwist

section Positivity

open PowerSeries

open scoped ComplexOrder

/-- The power sums of the pairwise products of two multisets are the products of their power
sums. -/
theorem _root_.Multiset.sum_map_pow_map_product_mul {R : Type*} [CommRing R] (s t : Multiset R)
    (n : ℕ) :
    ((((s ×ˢ t).map fun a ↦ a.1 * a.2)).map (· ^ n)).sum =
      (s.map (· ^ n)).sum * (t.map (· ^ n)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.map_add, Multiset.sum_add, ih,
      Multiset.map_cons, Multiset.sum_cons, add_mul]
    congr 1
    simp [Multiset.map_map, mul_pow, Multiset.sum_map_mul_left]

/-- An inverse local factor `ι P_x (σ, T ^ e_x)⁻¹` has nonnegative real coefficients as soon as
all power sums `∑ (ι α) ^ n` of the complex local eigenvalues of `σ` at `x` are nonnegative:
the formal identity `det (1 - T M)⁻¹ = exp (∑ Tr (M ^ n) T ^ n / n)`
(`PowerSeries.coeff_inv_prod_one_sub_C_mul_X_nonneg`) turns nonnegative power sums into
nonnegative coefficients, and substituting `T ^ e_x` for `T` preserves nonnegativity. -/
theorem hasNonnegCoeffs_eulerFactor_of_sum_pow_nonneg (x : C.finitePoints)
    (hsum : ∀ n : ℕ, 0 ≤ (((W.localEigenvalues l σ x).map ι).map (· ^ n)).sum) :
    (W.eulerFactor l σ ι x).HasNonnegCoeffs := by
  set e := p.degreeOver x.1
  have he : e ≠ 0 := p.degreeOver_ne_zero x.2
  set M := (W.localEigenvalues l σ x).map ι
  set P : ℂ⟦X⟧ := (M.map fun c ↦ 1 - PowerSeries.C c * X).prod
  have hP : constantCoeff P = 1 := by
    simp only [P, map_multiset_prod, Multiset.map_map]
    exact Multiset.prod_eq_one fun a ha ↦ by
      obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 ha
      simp
  have hcoe : (((W.localPolynomial l σ x).map ι).comp (Polynomial.X ^ e) : ℂ⟦X⟧) =
      expand e he P := by
    have hQ : (((W.localPolynomial l σ x).map ι : Polynomial ℂ) : ℂ⟦X⟧) = P := by
      rw [map_localPolynomial, ← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod,
        Multiset.map_map]
      exact congrArg _ (Multiset.map_congr rfl fun c _ ↦ by simp)
    ext n
    rw [Polynomial.coeff_coe, ← Polynomial.expand_eq_comp_X_pow,
      Polynomial.coeff_expand (Nat.pos_of_ne_zero he), PowerSeries.coeff_expand, ← hQ]
    split_ifs <;> simp [Polynomial.coeff_coe]
  have hinv : W.eulerFactor l σ ι x = expand e he P⁻¹ := by
    rw [eulerFactor, hcoe]
    refine ((PowerSeries.eq_inv_iff_mul_eq_one (by simp [hP])).2 ?_).symm
    rw [← map_mul, PowerSeries.inv_mul_cancel _ (by simp [hP]), map_one]
  rw [hinv, hasNonnegCoeffs_iff]
  intro n
  rw [PowerSeries.coeff_expand]
  split_ifs
  · exact coeff_inv_prod_one_sub_C_mul_X_nonneg M (fun n _ ↦ hsum n) _
  · exact le_rfl

/-- The power sums of the complex local eigenvalues of an `ι`-real representation are real. -/
theorem IsReal.conj_sum_map_pow_localEigenvalues (hρ : W.IsReal l ρ ι) (x : C.finitePoints)
    (n : ℕ) : (starRingEnd ℂ) (((W.localEigenvalues l ρ x).map ι).map (· ^ n)).sum =
      (((W.localEigenvalues l ρ x).map ι).map (· ^ n)).sum := by
  have hA : ((W.localEigenvalues l ρ x).map ι).map (starRingEnd ℂ) =
      (W.localEigenvalues l ρ x).map ι := hρ.map_conj_localEigenvalues ι x
  conv_rhs => rw [← hA]
  simp [map_multiset_sum, Multiset.map_map]

/-- Blueprint `lemma-positivity-euler-factors--1`: Even tensor powers of a real sheaf are positive,
for the tensor square.

If `ℱ` is `ι`-real, then every inverse local factor `ι P_x (ℱ ⊗ ℱ, T ^ e_x)⁻¹` of the tensor
square of `ℱ` has nonnegative real coefficients (and constant term `1`, by
`AlgebraicGeometry.WeilGroup.constantCoeff_eulerFactor`); that `ℱ ⊗ ℱ` is again `ι`-real is
`AlgebraicGeometry.WeilGroup.IsReal.tprod`. The case of all even tensor powers is
`AlgebraicGeometry.WeilGroup.IsReal.hasNonnegCoeffs_eulerFactor_tensorPower`; the Rankin–Selberg
argument here only uses tensor squares, iterated.

Indeed the `n`-th power sum of the complex local eigenvalues of `ℱ ⊗ ℱ` is
`ι Tr (F_x ^ n ∣ ℱ ⊗ ℱ) = (ι Tr (F_x ^ n ∣ ℱ)) ^ 2`, the square of a real number since the
eigenvalue multiset of `ℱ` is stable under complex conjugation
(`AlgebraicGeometry.WeilGroup.hasNonnegCoeffs_eulerFactor_of_sum_pow_nonneg`). -/
theorem IsReal.hasNonnegCoeffs_eulerFactor_tprod_self (hρ : W.IsReal l ρ ι)
    (x : C.finitePoints) : (W.eulerFactor l (ρ.tprod ρ) ι x).HasNonnegCoeffs := by
  refine hasNonnegCoeffs_eulerFactor_of_sum_pow_nonneg ι x fun n ↦ ?_
  rw [localEigenvalues_tprod, Multiset.map_map_product_mul,
    Multiset.sum_map_pow_map_product_mul,
    ← Complex.conj_eq_iff_re.1 (hρ.conj_sum_map_pow_localEigenvalues ι x n),
    ← Complex.ofReal_mul]
  exact Complex.zero_le_real.2 (mul_self_nonneg _)

end Positivity

section TopCohomology

variable (ρ)

variable (W l) in
/-- Blueprint `lemma-degree-zero-top-cohomology--2`: Description of `H_c²` on an affine curve.

For a lisse Weil sheaf `ℱ` on a smooth geometrically connected affine curve `U₀` with local
generic fibre `V`, there is a canonical Frobenius-equivariant isomorphism
`H_c² (U, ℱ) ≅ V_{π₁(U)} (-1)`, by global Verdier duality on a smooth compactification and the
description of global sections as invariants (`lemma-degree-zero-top-cohomology--1`).

Compactly supported cohomology of a Weil representation is not available, so the right-hand
side is used as the model of `H_c² (U, ℱ)`: this is the geometric Frobenius acting on it, `q`
times the endomorphism induced by the degree-one lift `γ` on the geometric coinvariants. -/
noncomputable def compactTopFrobenius :
    Module.End (PadicAlgCl l) (Representation.Coinvariants (ρ.comp W.geometric.subtype)) :=
  (Nat.card K : PadicAlgCl l) • ρ.toCoinvariants W.geometric W.frobeniusLift

/-- Blueprint `proposition-bound-largest-determinant-weight`: Eigenvalues of `H_c²` are
determinant weights.

Let `ℱ` be a Weil representation on `V`, and let `α` be an eigenvalue of the geometric
Frobenius on `H_c² (U, ℱ) = V_{π₁(U)} (-1)`, which acts as `q` times the endomorphism induced by
the degree-one lift `γ` on the geometric coinvariants. Then `wt_{ι, q} (α q⁻¹)` is a
determinant weight of `ℱ`: it is the determinant weight of an irreducible constituent of `ℱ`,
presented as a subquotient `M ⧸ N` of `V`.

Indeed `β = α q⁻¹` is an eigenvalue of `γ` on `V_{π₁(U)}`, whose generalized eigenspace is
stable under `W (U₀)`, since `π₁(U)` acts trivially on the coinvariants and `W (U₀)` is generated
by `π₁(U)` and `γ`. An irreducible subquotient of it has trivial geometric action and `γ` acts on
it with the single eigenvalue `β`, so that the local Frobenius at a point of degree `e` has
determinant `β ^ (r e)`, of weight `r wt_{ι, q} (β)` relative to `q ^ e`. -/
theorem exists_isConstituent_hasDetWeight_of_hasEigenvalue {α : PadicAlgCl l}
    (hα : (W.compactTopFrobenius l ρ).HasEigenvalue α) :
    ∃ N M : Subrepresentation ρ, N ≤ M ∧ (M.subquotient N).IsConstituent ρ ∧
      W.HasDetWeight l (M.subquotient N) ι
        (frobeniusWeight ι (Nat.card K) (α / Nat.card K)) := by
  classical
  set q : PadicAlgCl l := (Nat.card K : PadicAlgCl l)
  have hq : q ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  set G := W.geometric
  set Q := ρ.toCoinvariants G
  set T := Q W.frobeniusLift
  set β := α / q
  let mk := Representation.Coinvariants.mk (ρ.comp G.subtype)
  have hmk (g : W.carrier) (v : V) : mk (ρ g v) = Q g (mk v) := rfl
  -- `β` is an eigenvalue of `γ` on the coinvariants
  have hβ : Module.End.HasEigenvalue T β := by
    obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩
    rw [Module.End.mem_eigenspace_iff]
    have h := hv.apply_eq_smul
    rw [compactTopFrobenius, LinearMap.smul_apply] at h
    calc T v = q⁻¹ • (q • T v) := by rw [smul_smul, inv_mul_cancel₀ hq, one_smul]
      _ = β • v := by rw [h, smul_smul, inv_mul_eq_div]
  -- the geometric part acts trivially on the coinvariants, so `γ` commutes with `W (U₀)`
  have htriv (g : W.carrier) (hg : g ∈ G) : Q g = 1 :=
    (inferInstance : Representation.IsTrivial (Q.comp G.subtype)).out ⟨g, hg⟩
  have hcomm (g : W.carrier) : Commute T (Q g) := by
    have hc : W.frobeniusLift * g * W.frobeniusLift⁻¹ * g⁻¹ ∈ G := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [mul_comm (W.deg W.frobeniusLift)]
      group
    change Q W.frobeniusLift * Q g = Q g * Q W.frobeniusLift
    rw [← map_mul, ← map_mul, show W.frobeniusLift * g =
      (W.frobeniusLift * g * W.frobeniusLift⁻¹ * g⁻¹) * (g * W.frobeniusLift) by group,
      map_mul, htriv _ hc, one_mul]
  set E := Module.End.maxGenEigenspace T β
  -- the subrepresentations `N = ker (V → V_{π₁(U)}) < M₀ = preimage of E`
  let N : Subrepresentation ρ :=
    ⟨Representation.Coinvariants.ker (ρ.comp G.subtype),
      fun g _ hv ↦ Representation.Coinvariants.le_comap_ker ρ G g hv⟩
  let M₀ : Subrepresentation ρ :=
    ⟨E.comap mk, fun g v hv ↦ by
      change mk (ρ g v) ∈ E
      rw [hmk]
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm g) β hv⟩
  have hmemN {v : V} : v ∈ N ↔ mk v = 0 := (Representation.Coinvariants.mk_eq_zero _).symm
  have hNM₀ : N < M₀ := by
    refine lt_of_le_of_ne (fun v hv ↦ ?_) fun h ↦ ?_
    · change mk v ∈ E
      rw [hmemN.1 hv]
      exact zero_mem _
    · obtain ⟨w, hw⟩ := hβ.exists_hasEigenvector
      obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ w
      have hv : v ∈ M₀ := Module.End.eigenspace_le_maxGenEigenspace hw.1
      rw [← h, hmemN] at hv
      exact hw.2 hv
  have : WellFoundedLT (Subrepresentation ρ) :=
    Subrelation.wf (r := fun a b ↦ a.toSubmodule < b.toSubmodule) (fun h ↦ h)
      (InvImage.wf _ wellFounded_lt)
  obtain ⟨M, hNM, hMM₀⟩ := exists_covBy_le_of_lt hNM₀
  refine ⟨N, M, hNM.le, ⟨(Subrepresentation.isIrreducible_subquotient_iff hNM.le).2 hNM,
    N, M, hNM.le, ⟨M.subquotientAsModuleLinearEquiv N⟩⟩, fun x ↦ ?_⟩
  -- the subquotient `σ = M ⧸ N`
  set σ := M.subquotient N
  set r := Module.finrank (PadicAlgCl l)
    (M.toSubmodule ⧸ N.toSubmodule.comap M.toSubmodule.subtype)
  have hσtriv (g : W.carrier) (hg : g ∈ G) : σ g = 1 := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v ↦ ?_)
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    exact Representation.Coinvariants.sub_mem_ker (ρ := ρ.comp G.subtype) ⟨g, hg⟩ v.1
  -- every eigenvalue of `γ` on `σ` is `β`
  have heig : ∀ μ ∈ (σ W.frobeniusLift).charpoly.roots, μ = β := by
    intro μ hμ
    rw [Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hμ
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    obtain ⟨⟨v, hvM⟩, rfl⟩ := Submodule.mkQ_surjective _ w
    have hv := hw.apply_eq_smul
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ at hv
    rw [Submodule.Quotient.eq] at hv
    have hv' : mk (ρ W.frobeniusLift v - μ • v) = 0 := hmemN.1 hv
    rw [map_sub, map_smul, hmk, sub_eq_zero] at hv'
    have hne : mk v ≠ 0 := fun h ↦ hw.2 ((Submodule.Quotient.mk_eq_zero _).2 (hmemN.2 h))
    by_contra hμβ
    have hdisj := (Module.End.independent_maxGenEigenspace T).pairwiseDisjoint hμβ
    exact hne ((Submodule.disjoint_def.1 hdisj) _
      (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hv'))
      (hMM₀ hvM))
  have hdet : LinearMap.det (σ W.frobeniusLift) = β ^ r := by
    rw [LinearMap.det_eq_prod_roots_charpoly, Multiset.eq_replicate.2
      ⟨LinearMap.card_roots_charpoly _, heig⟩, Multiset.prod_replicate]
  -- the local Frobenius at `x` acts on `σ` as `γ ^ e`
  set e := p.degreeOver x.1
  have he : e ≠ 0 := p.degreeOver_ne_zero x.2
  have hn : W.frobenius x * (W.frobeniusLift ^ e)⁻¹ ∈ G := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, W.deg_frobenius, W.deg_frobeniusLift,
      ← ofAdd_nsmul, nsmul_one, mul_inv_eq_one]
  have hσx : σ (W.frobenius x) = σ W.frobeniusLift ^ e := by
    rw [show W.frobenius x = (W.frobenius x * (W.frobeniusLift ^ e)⁻¹) * W.frobeniusLift ^ e
      by group, map_mul, hσtriv _ hn, one_mul, map_pow]
  rw [hσx, map_pow, hdet, ← pow_mul, Scheme.Hom.pointNorm_eq_pow_degreeOver p x.2]
  have hlog : Real.log (Nat.card K) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast Finite.one_lt_card_iff_nontrivial.2 inferInstance)).ne'
  simp only [frobeniusWeight, map_pow, norm_pow, Real.log_pow, Nat.cast_pow, Nat.cast_mul]
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he
  have he'' : ((p.degreeOver x.1 : ℕ) : ℝ) ≠ 0 := he'
  field_simp
  ring

open scoped PowerSeries.WithPiTopology in
/-- Blueprint `theorem-trace-formula-euler-product--4`: Euler product of the `L`-function of a lisse
sheaf.

Let `U₀` be a smooth geometrically connected affine curve and `ℱ` a lisse Weil sheaf on it.
Then, as power series in `T`,
`∏_{x ∈ |U₀|} ι det (1 - F_x T ^ e_x ∣ ℱ)⁻¹ = ι det (1 - F T ∣ H_c¹) / ι det (1 - F T ∣ H_c²)`,
with `H_c² (U, ℱ) = V_{π₁(U)} (-1)` the coinvariant Tate twist, on which the geometric Frobenius
acts as `q` times the endomorphism induced by `γ`. Here the numerator `ι det (1 - F T ∣ H_c¹)`
is only recorded as some polynomial `P`.

This is the curve case of the Euler-product form of the Grothendieck–Lefschetz trace formula,
together with `H_c⁰ (U, ℱ) = 0` (`lemma-degree-zero-top-cohomology--4`) and the coinvariant
description of `H_c²` (`lemma-degree-zero-top-cohomology--2`), for `ℓ ≠ char 𝔽_q`, applied to the
lisse Weil sheaf attached to `ρ`
(`AlgebraicGeometry.WeilSheaf.coeff_prod_inv_localPolynomial_stalk_eq`). -/
theorem exists_eulerSeries_mul_eq_coe [IsAffine C] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] [Fact (ringChar K ≠ l)] (hρ : W.IsLisse l ρ) :
    ∃ P : Polynomial ℂ, W.eulerSeries l ρ ι *
      (((W.compactTopFrobenius l ρ).charpolyRev.map ι : Polynomial ℂ) : PowerSeries ℂ) = P := by
  classical
  let _ : C.Over (Spec (.of K)) := ⟨p⟩
  have _ : IsCurve (C ↘ Spec (.of K)) := ‹IsCurve p›
  have _ : SmoothOfRelativeDimension 1 (C ↘ Spec (.of K)) := ‹SmoothOfRelativeDimension 1 p›
  have _ : GeometricallyConnected (C ↘ Spec (.of K)) := ‹GeometricallyConnected p›
  obtain ⟨F, hF, hst, f, hf⟩ := exists_weilSheaf_of_isLisse (W := W) hρ
  obtain ⟨e₂⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two F hF
  -- the Frobenius on `H_c² (U, ℱ) = V_{π₁(U)} (-1)` is `compactTopFrobenius`
  have hq : ((Nat.card K : PadicAlgCl l) ^ (-(-1 : ℤ))) ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have h₂ : (F.compactlySupportedCohomology 2).localPolynomial =
      (W.compactTopFrobenius l ρ).charpolyRev := by
    rw [FrobeniusModule.localPolynomial, LinearMap.charpolyRev_def, LinearMap.charpolyRev_def,
      ← e₂.charpoly_frobeniusEnd]
    refine congrArg _ (LinearMap.charpoly_eq_of_comp_eq f (LinearMap.ext fun v ↦ ?_))
    have key := FrobeniusModule.frobeniusEnd_rescale_apply (M := F.geometricCoinvariants hF) hq v
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    refine (congrArg f key).trans ?_
    rw [map_smul, FrobeniusModule.frobeniusEnd_apply, hf, compactTopFrobenius,
      LinearMap.smul_apply, neg_neg, zpow_one]
    rfl
  -- the Euler product converges to `ι (det (1 - F T ∣ H_c¹) / det (1 - F T ∣ H_c²))`
  have hprod : HasProd (W.eulerFactor l ρ ι) (PowerSeries.map ι
      (((F.compactlySupportedCohomology 1).localPolynomial : PowerSeries (PadicAlgCl l)) *
        ((F.compactlySupportedCohomology 2).localPolynomial : PowerSeries (PadicAlgCl l))⁻¹)) := by
    rw [HasProd, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [Filter.eventually_ge_atTop (p.finite_setOf_degreeOver_le n).toFinset]
      with s hs
    rw [PowerSeries.coeff_map, ← WeilSheaf.coeff_prod_inv_localPolynomial_stalk_eq F hF n s
      fun x hx ↦ hs ((p.finite_setOf_degreeOver_le n).mem_toFinset.2 hx), ← PowerSeries.coeff_map,
      map_prod (PowerSeries.map ι)]
    refine congrArg (PowerSeries.coeff n) (Finset.prod_congr rfl fun x _ ↦ ?_)
    have hx : (F.stalk x).localPolynomial = W.localPolynomial l ρ x := by
      rw [FrobeniusModule.localPolynomial, localPolynomial, LinearMap.charpolyRev_def,
        LinearMap.charpolyRev_def, hst x]
    rw [eulerFactor, PowerSeries.map_inv, ← Polynomial.polynomial_map_coe, hx,
      Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
    rfl
  refine ⟨(F.compactlySupportedCohomology 1).localPolynomial.map ι, ?_⟩
  have h₀ : PowerSeries.constantCoeff
      ((F.compactlySupportedCohomology 2).localPolynomial : PowerSeries (PadicAlgCl l)) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      FrobeniusModule.localPolynomial, LinearMap.coeff_zero_charpolyRev]
    exact one_ne_zero
  rw [eulerSeries, hprod.tprod_eq, ← h₂, Polynomial.polynomial_map_coe,
    Polynomial.polynomial_map_coe, ← map_mul, mul_assoc, PowerSeries.inv_mul_cancel _ h₀,
    mul_one]

end TopCohomology

end WeilGroup

end AlgebraicGeometry
