/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.Matrix
public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Weights
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import WeilConjectures.Mathlib.Algebra.Polynomial.FieldDivision
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Irreducible

/-!
# Linear-algebra operations on lisse Weil sheaves

The operations of `definition-weil-representation` and `proposition-weights-under-usual-operations`
on lisse Weil representations: subquotients, finite direct sums, exterior powers and the determinant
line of a lisse Weil representation are again lisse, and an exterior power of a Weil representation
whose local characteristic polynomials are those of an `ι`-real one is again `ι`-real.

Lisseness is checked on the coefficients `g ↦ φ (ρ g v)` of the geometric part
(`AlgebraicGeometry.WeilGroup.IsLisse.continuous_apply` and
`AlgebraicGeometry.WeilGroup.IsLisse.of_continuous_apply`); reality is checked on the local
eigenvalues (`AlgebraicGeometry.WeilGroup.IsReal.map_conj_localEigenvalues` and
`AlgebraicGeometry.WeilGroup.isReal_of_map_conj_localEigenvalues`): `ι P_x` has real
coefficients exactly when the multiset of complex local eigenvalues is stable under complex
conjugation.

## Main statements

- `AlgebraicGeometry.WeilGroup.IsLisse.subquotient`, `IsLisse.directSum`,
  `IsLisse.exteriorPower`, `IsLisse.ofCharacter_detCharacter`, `IsLisse.of_equiv`.
- `AlgebraicGeometry.WeilGroup.IsReal.exteriorPower_of_charpoly_eq`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilGroup

section FrobeniusWeight

variable {E : Type*} [Field E] (ι : E →+* ℂ)

/-- The `ι`-weight of a product of nonzero elements is the sum of the weights. -/
theorem frobeniusWeight_mul (qx : ℕ) {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    frobeniusWeight ι qx (a * b) = frobeniusWeight ι qx a + frobeniusWeight ι qx b := by
  have ha' : ‖ι a‖ ≠ 0 := by simpa using ha
  have hb' : ‖ι b‖ ≠ 0 := by simpa using hb
  simp only [frobeniusWeight, map_mul, norm_mul, Real.log_mul ha' hb']
  ring

/-- For `qx > 1` and `ι α ≠ 0`, the weight bound `wt_{ι, qx} (α) ≤ β` is the bound
`|ι α| ^ 2 ≤ qx ^ β`. -/
theorem frobeniusWeight_le_iff {qx : ℕ} (hq : 1 < qx) {α : E} (hα : ι α ≠ 0) {β : ℝ} :
    frobeniusWeight ι qx α ≤ β ↔ ‖ι α‖ ^ 2 ≤ (qx : ℝ) ^ β := by
  have hq' : (1 : ℝ) < qx := by exact_mod_cast hq
  have h1 : 0 < ‖ι α‖ ^ 2 := by positivity
  have h2 : (0 : ℝ) < (qx : ℝ) ^ β := by positivity
  rw [frobeniusWeight, div_le_iff₀ (Real.log_pos hq'), ← Real.log_le_log_iff h1 h2,
    Real.log_pow, Real.log_rpow (by positivity)]
  push_cast
  constructor <;> intro h <;> linarith

/-- The weight of a power is the multiple of the weight. -/
theorem frobeniusWeight_pow (qx : ℕ) (α : E) (n : ℕ) :
    frobeniusWeight ι qx (α ^ n) = n * frobeniusWeight ι qx α := by
  simp only [frobeniusWeight, map_pow, norm_pow, Real.log_pow]
  ring

/-- The weight of an inverse is the negative of the weight; in particular duality negates
weights (blueprint `proposition-weights-under-usual-operations`). -/
theorem frobeniusWeight_inv (qx : ℕ) (α : E) :
    frobeniusWeight ι qx α⁻¹ = -frobeniusWeight ι qx α := by
  simp only [frobeniusWeight, map_inv₀, norm_inv, Real.log_inv]
  ring

/-- The `ι`-weight of a product of nonzero elements is the sum of the weights. -/
theorem frobeniusWeight_multiset_prod (qx : ℕ) {s : Multiset E} (hs : (0 : E) ∉ s) :
    frobeniusWeight ι qx s.prod = (s.map (frobeniusWeight ι qx)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [frobeniusWeight]
  | cons a s ih =>
    rw [Multiset.mem_cons, not_or] at hs
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      frobeniusWeight_mul ι qx (Ne.symm hs.1) (Multiset.prod_ne_zero hs.2), ih hs.2]

/-- The `ι`-weight of a finite product of nonzero elements is the sum of the weights. -/
theorem frobeniusWeight_prod (qx : ℕ) {ι' : Type*} (s : Finset ι') {f : ι' → E}
    (hf : ∀ i ∈ s, f i ≠ 0) :
    frobeniusWeight ι qx (∏ i ∈ s, f i) = ∑ i ∈ s, frobeniusWeight ι qx (f i) := by
  rw [Finset.prod_eq_multiset_prod, frobeniusWeight_multiset_prod, Multiset.map_map]
  · rfl
  · simp only [Multiset.mem_map, not_exists, not_and]
    exact fun i hi h ↦ hf i hi h

/-- Blueprint `definition-determinant-weight--1`: the real weight character `a ↦ wt_{ι, q}(a)` of
`definition-determinant-weight--1`, whose determinant weights (`Representation.detWeight`) are the
determinant weights `dw_ι` of `definition-determinant-weight--1`. -/
noncomputable def weightCharacter (q : ℕ) : Representation.RealCharacter E where
  toFun a := Multiplicative.ofAdd (frobeniusWeight ι q (a : E))
  map_one' := by simp [frobeniusWeight]
  map_mul' a b := by
    rw [Units.val_mul, frobeniusWeight_mul ι q a.ne_zero b.ne_zero, ofAdd_add]

/-- The determinant weight for `AlgebraicGeometry.WeilGroup.weightCharacter` is
`wt_{ι, q}(det ρ(g)) / rank ρ`. -/
theorem detWeight_weightCharacter {G V : Type*} [Group G] [AddCommGroup V] [Module E V]
    (ρ : Representation E G V) (q : ℕ) (g : G) :
    ρ.detWeight (weightCharacter ι q) g =
      frobeniusWeight ι q (LinearMap.det (ρ g)) / Module.finrank E V := by
  simp [Representation.detWeight, weightCharacter, Representation.coe_detCharacter_apply]

end FrobeniusWeight

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {W : WeilGroup p} {l : ℕ} [Fact l.Prime]

section Lisse

variable {V V' : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V] [AddCommGroup V']
  [Module (PadicAlgCl l) V'] {ρ : Representation (PadicAlgCl l) W.carrier V}

/-- A representation equivalent to a lisse one is lisse. -/
theorem IsLisse.of_equiv [FiniteDimensional (PadicAlgCl l) V]
    {σ : Representation (PadicAlgCl l) W.carrier V'} (e : ρ.Equiv σ) (hρ : W.IsLisse l ρ) :
    W.IsLisse l σ :=
  IsLisse.of_continuous_apply fun φ v ↦ by
    have h := hρ.continuous_apply (φ ∘ₗ e.toLinearEquiv.toLinearMap) (e.symm v)
    refine h.congr fun g ↦ ?_
    simp only [LinearMap.comp_apply]
    congr 1
    have h₁ := LinearMap.congr_fun (e.isIntertwining' (g : W.carrier)) (e.symm v)
    simp only [LinearMap.comp_apply] at h₁
    rw [h₁]
    exact congrArg _ (e.apply_symm_apply v)

/-- A subquotient of a lisse representation is lisse. -/
theorem IsLisse.subquotient [FiniteDimensional (PadicAlgCl l) V] (hρ : W.IsLisse l ρ)
    (M N : Subrepresentation ρ) : W.IsLisse l (M.subquotient N) :=
  IsLisse.of_continuous_apply fun φ v ↦ by
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ v
    obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend
      (φ ∘ₗ (N.toSubmodule.comap M.toSubmodule.subtype).mkQ) (p := M.toSubmodule)
    refine (hρ.continuous_apply ψ v).congr fun g ↦ ?_
    rw [show ψ (ρ g v) = (ψ ∘ₗ M.toSubmodule.subtype) ((ρ g).restrict
      (M.apply_mem_toSubmodule g) v) from rfl, hψ]
    rfl

/-- A finite direct sum of lisse representations is lisse. -/
theorem IsLisse.directSum {ι : Type} [Finite ι] {V : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module (PadicAlgCl l) (V i)]
    [∀ i, FiniteDimensional (PadicAlgCl l) (V i)]
    {ρ : ∀ i, Representation (PadicAlgCl l) W.carrier (V i)} (hρ : ∀ i, W.IsLisse l (ρ i)) :
    W.IsLisse l (Representation.directSum ρ) :=
  IsLisse.of_continuous_apply fun φ v ↦ by
    classical
    have := Fintype.ofFinite ι
    have hv (g : W.geometric) : φ (Representation.directSum ρ g v) =
        ∑ i, (φ ∘ₗ DirectSum.lof (PadicAlgCl l) ι V i) (ρ i g (v i)) := by
      conv_lhs => rw [← DirectSum.sum_univ_of v]
      simp [map_sum, DirectSum.lof_eq_of]
    simp_rw [hv]
    exact continuous_finsetSum _ fun i _ ↦ (hρ i).continuous_apply _ _

/-- An exterior power of a lisse representation is lisse. -/
theorem IsLisse.exteriorPower [FiniteDimensional (PadicAlgCl l) V] (hρ : W.IsLisse l ρ)
    (s : ℕ) : W.IsLisse l (ρ.exteriorPower s) :=
  IsLisse.of_continuous_apply fun φ x ↦ by
    have hx : x ∈ Submodule.span (PadicAlgCl l)
        (Set.range (exteriorPower.ιMulti (PadicAlgCl l) s (M := V))) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      let b := Module.finBasis (PadicAlgCl l) V
      have key (g : W.geometric) : φ (ρ.exteriorPower s g (exteriorPower.ιMulti _ s m)) =
          ∑ r : Fin s → Fin (Module.finrank (PadicAlgCl l) V),
            (∏ i, b.coord (r i) (ρ g (m i))) *
              φ (exteriorPower.ιMulti _ s fun i ↦ b (r i)) := by
        change φ (_root_.exteriorPower.map s (ρ g) (exteriorPower.ιMulti _ s m)) = _
        rw [exteriorPower.map_apply_ιMulti]
        have hm : (fun i ↦ ρ g (m i)) = fun i ↦ ∑ j, b.coord j (ρ g (m i)) • b j :=
          funext fun i ↦ (b.sum_repr (ρ g (m i))).symm
        rw [Function.comp_def, hm]
        let A := (φ.compAlternatingMap (exteriorPower.ιMulti (PadicAlgCl l) s (M := V)))
        change A.toMultilinearMap _ = _
        rw [MultilinearMap.map_sum]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [MultilinearMap.map_smul_univ, smul_eq_mul]
        rfl
      simp_rw [key]
      exact continuous_finsetSum _ fun r _ ↦ (continuous_finsetProd _ fun i _ ↦
        hρ.continuous_apply _ _).mul continuous_const
    | zero => simpa using continuous_const
    | add x y _ _ hx hy => exact (hx.add hy).congr fun g ↦ by simp
    | smul a x _ hx =>
      exact ((continuous_const : Continuous fun _ : W.geometric ↦ a).mul hx).congr fun g ↦ by
        simp

/-- The determinant line `g ↦ det ρ(g)` of a lisse representation, realised on any module, is
lisse. -/
theorem IsLisse.ofCharacter_detCharacter [FiniteDimensional (PadicAlgCl l) V]
    (hρ : W.IsLisse l ρ) (M : Type u) [AddCommGroup M] [Module (PadicAlgCl l) M] :
    W.IsLisse l (Representation.ofCharacter ρ.detCharacter M) := by
  have hdet : Continuous fun g : W.geometric ↦ LinearMap.det (ρ g) := by
    let b := Module.finBasis (PadicAlgCl l) V
    have h : Continuous fun g : W.geometric ↦ LinearMap.toMatrix b b (ρ g) :=
      continuous_pi fun i ↦ continuous_pi fun j ↦ hρ.continuous_toMatrix b i j
    simpa only [LinearMap.det_toMatrix] using h.matrix_det
  refine IsLisse.of_continuous_apply fun φ v ↦ ?_
  simp only [Representation.ofCharacter_apply, Representation.coe_detCharacter_apply, map_smul,
    smul_eq_mul]
  exact hdet.mul continuous_const

/-- The dual of a lisse Weil sheaf is lisse: its matrix coefficients are those of `ρ (g⁻¹)`. -/
theorem IsLisse.dual [FiniteDimensional (PadicAlgCl l) V] (hρ : W.IsLisse l ρ) :
    W.IsLisse l ρ.dual := by
  refine IsLisse.of_continuous_apply fun φ f ↦ ?_
  obtain ⟨w, rfl⟩ := (Module.evalEquiv (PadicAlgCl l) V).surjective φ
  have h : (fun g : W.geometric ↦ Module.evalEquiv (PadicAlgCl l) V w (ρ.dual g f)) =
      fun g ↦ f (ρ (g⁻¹ : W.geometric) w) := by
    funext g
    simp [Representation.dual_apply, Module.Dual.transpose_apply]
  rw [h]
  exact (hρ.continuous_apply f w).comp continuous_inv

end Lisse

section Real

variable {V V' : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V] [AddCommGroup V'] [Module (PadicAlgCl l) V']
  [FiniteDimensional (PadicAlgCl l) V'] {ρ : Representation (PadicAlgCl l) W.carrier V}
  (ι : PadicAlgCl l →+* ℂ)

/-- The local eigenvalues are nonzero, since the local Frobenius acts invertibly. -/
theorem zero_notMem_localEigenvalues (x : C.finitePoints) :
    (0 : PadicAlgCl l) ∉ W.localEigenvalues l ρ x := by
  intro h
  rw [localEigenvalues, Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at h
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have h0 : ρ (W.frobenius x) v = 0 := by rw [hv.apply_eq_smul, zero_smul]
  have : v = 0 := by
    have hv' : v = ρ (W.frobenius x)⁻¹ (ρ (W.frobenius x) v) := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hv', h0, map_zero]
  exact hv.2 this

/-- The complex local polynomial `ι P_x(ρ, T)` is `∏ (1 - (ι α) T)` over the local eigenvalues
`α`. -/
theorem map_localPolynomial (x : C.finitePoints) :
    (W.localPolynomial l ρ x).map ι =
      (((W.localEigenvalues l ρ x).map ι).map
        fun β ↦ 1 - Polynomial.C β * Polynomial.X).prod := by
  rw [localPolynomial_eq_prod_localEigenvalues, Polynomial.map_multiset_prod_one_sub_C_mul_X]

/-- The complex local eigenvalues are nonzero. -/
theorem zero_notMem_map_localEigenvalues (x : C.finitePoints) :
    (0 : ℂ) ∉ (W.localEigenvalues l ρ x).map ι := by
  simp only [Multiset.mem_map, map_eq_zero, not_exists, not_and]
  rintro α hα rfl
  exact zero_notMem_localEigenvalues x hα

/-- Blueprint `definition-weights`: an `ι`-real representation has a conjugation-stable
multiset of complex local eigenvalues at every closed point. -/
theorem IsReal.map_conj_localEigenvalues (h : W.IsReal l ρ ι) (x : C.finitePoints) :
    ((W.localEigenvalues l ρ x).map ι).map (starRingEnd ℂ) =
      (W.localEigenvalues l ρ x).map ι := by
  set M := (W.localEigenvalues l ρ x).map ι
  have hM : (0 : ℂ) ∉ M := zero_notMem_map_localEigenvalues ι x
  have hM' : (0 : ℂ) ∉ M.map (starRingEnd ℂ) := by simpa using hM
  have h₁ : ((W.localPolynomial l ρ x).map ι).map (starRingEnd ℂ) =
      (W.localPolynomial l ρ x).map ι := by
    ext n
    simpa [Polynomial.coeff_map] using h x n
  rw [map_localPolynomial, Polynomial.map_multiset_prod_one_sub_C_mul_X] at h₁
  have := congrArg Polynomial.roots h₁
  rw [Polynomial.roots_multiset_prod_one_sub_C_mul_X hM',
    Polynomial.roots_multiset_prod_one_sub_C_mul_X hM] at this
  exact Multiset.map_injective inv_injective this

/-- Blueprint `definition-weights`: a representation whose multisets of complex local
eigenvalues are stable under complex conjugation is `ι`-real. -/
theorem isReal_of_map_conj_localEigenvalues
    (h : ∀ x, ((W.localEigenvalues l ρ x).map ι).map (starRingEnd ℂ) =
      (W.localEigenvalues l ρ x).map ι) :
    W.IsReal l ρ ι := by
  intro x n
  have h₁ : ((W.localPolynomial l ρ x).map ι).map (starRingEnd ℂ) =
      (W.localPolynomial l ρ x).map ι := by
    rw [map_localPolynomial, Polynomial.map_multiset_prod_one_sub_C_mul_X, h x]
  simpa [Polynomial.coeff_map] using congrArg (Polynomial.coeff · n) h₁

/-- Blueprint `proposition-weights-under-usual-operations`: if the local characteristic polynomials
of `σ` are those of an `ι`-real representation `ρ`, then every exterior power of `σ` is `ι`-real:
its local eigenvalues are the products of the `s`-element sub-multisets of those of `ρ`, by
`LinearMap.charpoly_roots_exteriorPower`. -/
theorem IsReal.exteriorPower_of_charpoly_eq {σ : Representation (PadicAlgCl l) W.carrier V'}
    (hreal : W.IsReal l ρ ι)
    (h : ∀ x, (σ (W.frobenius x)).charpoly = (ρ (W.frobenius x)).charpoly) (s : ℕ) :
    W.IsReal l (σ.exteriorPower s) ι := by
  refine isReal_of_map_conj_localEigenvalues ι fun x ↦ ?_
  have hE : W.localEigenvalues l (σ.exteriorPower s) x =
      ((W.localEigenvalues l ρ x).powersetCard s).map Multiset.prod := by
    change (_root_.exteriorPower.map s (σ (W.frobenius x))).charpoly.roots = _
    rw [LinearMap.charpoly_roots_exteriorPower, h x]
    rfl
  have hmap (f : PadicAlgCl l →+* ℂ) (M : Multiset (PadicAlgCl l)) :
      ((M.powersetCard s).map Multiset.prod).map f =
        ((M.map f).powersetCard s).map Multiset.prod := by
    rw [Multiset.powersetCard_map, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun t _ ↦ map_multiset_prod f t
  have hconj (M : Multiset ℂ) :
      ((M.powersetCard s).map Multiset.prod).map (starRingEnd ℂ) =
        ((M.map (starRingEnd ℂ)).powersetCard s).map Multiset.prod := by
    rw [Multiset.powersetCard_map, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun t _ ↦ map_multiset_prod (starRingEnd ℂ) t
  rw [hE, hmap, hconj, hreal.map_conj_localEigenvalues ι x]

/-- Blueprint `proposition-weights-under-usual-operations--4`: Weight of the linear dual.

The dual of a sheaf punctually pure of weight `w` is punctually pure of weight `-w`: the
local eigenvalues of the dual are the inverses of those of `ρ` (`lemma-filtrations-spectra`), and
inverses have the negative weight (`proposition-weights-under-usual-operations--3`). -/
theorem IsPunctuallyPure.dual {w : ℝ} (h : W.IsPunctuallyPure l ρ ι w) :
    W.IsPunctuallyPure l ρ.dual ι (-w) := by
  intro x γ hγ
  rw [localEigenvalues, Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly, Representation.hasEigenvalue_dual_iff] at hγ
  have hγ' := ρ.hasEigenvalue_inv hγ
  rw [inv_inv] at hγ'
  have hmem : γ⁻¹ ∈ W.localEigenvalues l ρ x := by
    rw [localEigenvalues, Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hγ'
  have := h x _ hmem
  rw [frobeniusWeight_inv] at this
  linarith

end Real

end WeilGroup

end AlgebraicGeometry
