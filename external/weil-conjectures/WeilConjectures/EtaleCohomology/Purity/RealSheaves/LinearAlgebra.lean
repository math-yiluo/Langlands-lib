/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations
public import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Weights of eigenvalues, Frobenius modules, reality and semisimplification

This file collects the finite-dimensional linear algebra of weights used in the purity theorem
for real lisse Weil sheaves (blueprint subsections `situation-weil`,
`proposition-weights-under-usual-operations` and `proposition-weights-j-boundary-points`).

* An element `α` of a field `E` with an embedding `ι : E →+* ℂ` has *weight* `w` relative to
  `q` if `|ι α| = q ^ (w / 2)` (`AlgebraicGeometry.WeilGroup.IsOfWeight`); weights add under
  products and change sign under inverses.
* A finite-dimensional vector space with an automorphism `F` is `ι`-pure of weight `w` if every
  eigenvalue of `F` has weight `w`, and `ι`-mixed of weights at most `w` if it has an
  `F`-stable filtration whose graded pieces are pure of weights `≤ w`
  (`AlgebraicGeometry.WeilGroup.IsPureFrobeniusModule`,
  `AlgebraicGeometry.WeilGroup.IsMixedFrobeniusModule`).
* The determinant line and the semisimplification of a Weil representation
  (`AlgebraicGeometry.WeilGroup.detLine`, `AlgebraicGeometry.WeilGroup.semisimplification`).
* Exterior powers of `ι`-real sheaves are `ι`-real, and the semisimplification of a Weil
  representation has the same local polynomials, hence the same reality.

## Main definitions

- `AlgebraicGeometry.WeilGroup.IsOfWeight`
- `AlgebraicGeometry.WeilGroup.IsPureFrobeniusModule`,
  `AlgebraicGeometry.WeilGroup.IsMixedFrobeniusModule`
- `AlgebraicGeometry.WeilGroup.detLine`, `AlgebraicGeometry.WeilGroup.semisimplification`

## Main statements

- `AlgebraicGeometry.WeilGroup.IsOfWeight.mul`, `AlgebraicGeometry.WeilGroup.IsOfWeight.inv`
- `AlgebraicGeometry.WeilGroup.IsReal.exteriorPower`
- `AlgebraicGeometry.WeilGroup.localPolynomial_semisimplification`,
  `AlgebraicGeometry.WeilGroup.IsReal.semisimplification`,
  `AlgebraicGeometry.WeilGroup.isPunctuallyPure_semisimplification_iff`,
  `AlgebraicGeometry.WeilGroup.hasWeightsAtMost_semisimplification_iff`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilGroup

section EigenvalueWeight

variable {E : Type*} [Field E] (ι : E →+* ℂ) (q : ℕ)

/-- Blueprint `definition-weights--1`: weights of eigenvalues.

An element `α` (typically an eigenvalue of a Frobenius operator) has *weight* `w` relative to
the prime power `q` if `|ι α| = q ^ (w / 2)`, the absolute value being read through the fixed
embedding `ι` into `ℂ`; so `|q| = q` and `q` itself has weight `2`. This is the convention of
`definition-weights`; it is related to the `ι`-weight
`AlgebraicGeometry.WeilGroup.frobeniusWeight` by
`AlgebraicGeometry.WeilGroup.isOfWeight_iff_frobeniusWeight_eq`. The weight `w` is allowed
to be any real number. -/
def IsOfWeight (w : ℝ) (α : E) : Prop :=
  ‖ι α‖ = (q : ℝ) ^ (w / 2)

variable {ι q}

/-- For `q > 1`, a nonzero `α` has weight `w` if and only if its `ι`-weight
`2 log |ι α| / log q` is `w`. -/
theorem isOfWeight_iff_frobeniusWeight_eq (hq : 1 < q) {α : E} (hα : α ≠ 0) {w : ℝ} :
    IsOfWeight ι q w α ↔ frobeniusWeight ι q α = w := by
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : 0 < Real.log q := Real.log_pos hq'
  have hpos : 0 < ‖ι α‖ := by simpa using hα
  rw [IsOfWeight, frobeniusWeight, div_eq_iff hlog.ne', ← Real.exp_log hpos,
    Real.rpow_def_of_pos (by linarith), Real.exp_eq_exp, Real.log_exp]
  constructor <;> intro h <;> linarith

/-- Blueprint `proposition-weights-under-usual-operations--3`: Weights multiply under tensor
product.

If `α` and `β` have weights `w₁` and `w₂`, then `α β` has weight `w₁ + w₂`: the absolute value
is multiplicative. -/
theorem IsOfWeight.mul (hq : 0 < q) {w₁ w₂ : ℝ} {α β : E} (hα : IsOfWeight ι q w₁ α)
    (hβ : IsOfWeight ι q w₂ β) : IsOfWeight ι q (w₁ + w₂) (α * β) := by
  rw [IsOfWeight, map_mul, norm_mul, hα, hβ, ← Real.rpow_add (by exact_mod_cast hq), add_div]

/-- Blueprint `proposition-weights-under-usual-operations--3`: Weights multiply under tensor
product.

If `α ≠ 0` has weight `w`, then `α⁻¹` has weight `-w`: `|α⁻¹| = |α|⁻¹`. -/
theorem IsOfWeight.inv {w : ℝ} {α : E} (hα : IsOfWeight ι q w α) :
    IsOfWeight ι q (-w) α⁻¹ := by
  rw [IsOfWeight, map_inv₀, norm_inv, hα, neg_div, Real.rpow_neg (Nat.cast_nonneg q)]

end EigenvalueWeight

section FrobeniusModule

variable {E : Type*} [Field E] (ι : E →+* ℂ) (q : ℕ) {V : Type*} [AddCommGroup V] [Module E V]

/-- Blueprint `definition-weights`: Weights of finite-dimensional Frobenius
modules.

A vector space `V` with an automorphism `F` is `ι`-pure of weight `w` if every eigenvalue `α`
of `F` satisfies `|ι α| = q ^ (w / 2)`. The field `E` is algebraically closed, so that every
eigenvalue of `F` lies in `E`. -/
def IsPureFrobeniusModule [IsAlgClosed E] (F : V ≃ₗ[E] V) (w : ℝ) : Prop :=
  ∀ α : E, Module.End.HasEigenvalue (F : Module.End E V) α → IsOfWeight ι q w α

/-- Blueprint `definition-weights`: Weights of finite-dimensional Frobenius
modules.

A vector space `V` with an automorphism `F` is `ι`-mixed of weights at most `w` if there are an
integer `m ≥ 0`, an `F`-stable filtration `0 = V₀ ⊆ V₁ ⊆ ⋯ ⊆ V_m = V` and real numbers
`w₁, …, w_m ≤ w` such that each `(V_r / V_{r-1}, F)` is `ι`-pure of weight `w_r`. Here
`α` is an eigenvalue of the automorphism induced by `F` on `V_r / V_{r-1}` exactly when there
is `v ∈ V_r` outside `V_{r-1}` with `F v - α v ∈ V_{r-1}`; the filtration is indexed by `ℕ`,
with `V i` and `w (i + 1)` for `i < m`. -/
def IsMixedFrobeniusModule [IsAlgClosed E] (F : V ≃ₗ[E] V) (w : ℝ) : Prop :=
  ∃ (m : ℕ) (Fil : ℕ → Submodule E V) (wt : ℕ → ℝ), Fil 0 = ⊥ ∧ Fil m = ⊤ ∧
    (∀ i < m, Fil i ≤ Fil (i + 1)) ∧ (∀ i, ∀ v ∈ Fil i, F v ∈ Fil i) ∧
    ∀ i < m, wt (i + 1) ≤ w ∧ ∀ (α : E) (v : V), v ∈ Fil (i + 1) → v ∉ Fil i →
      F v - α • v ∈ Fil i → IsOfWeight ι q (wt (i + 1)) α

variable {ι q}

/-- A pure Frobenius module of weight `w` is mixed of weights at most `w`, with the filtration
`0 ⊆ V`. -/
theorem IsPureFrobeniusModule.isMixedFrobeniusModule [IsAlgClosed E] {F : V ≃ₗ[E] V} {w : ℝ}
    (h : IsPureFrobeniusModule ι q F w) : IsMixedFrobeniusModule ι q F w := by
  refine ⟨1, fun i ↦ if i = 0 then ⊥ else ⊤, fun _ ↦ w, rfl, rfl, fun i hi ↦ ?_, fun i v hv ↦ ?_,
    fun i hi ↦ ⟨le_rfl, fun α v _ hv0 hFv ↦ h α ?_⟩⟩
  · obtain rfl : i = 0 := by omega
    exact bot_le
  · dsimp only at hv ⊢
    split_ifs at hv ⊢ with hi
    · rw [(Submodule.mem_bot E).1 hv, map_zero]
      exact zero_mem _
    · exact Submodule.mem_top
  · obtain rfl : i = 0 := by omega
    simp only [ite_true] at hv0 hFv
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff]
    exact sub_eq_zero.1 ((Submodule.mem_bot E).1 hFv)

/-- Being mixed of weights at most `w` is monotone in `w`. -/
theorem IsMixedFrobeniusModule.mono [IsAlgClosed E] {F : V ≃ₗ[E] V} {w w' : ℝ}
    (h : IsMixedFrobeniusModule ι q F w) (hw : w ≤ w') : IsMixedFrobeniusModule ι q F w' := by
  obtain ⟨m, Fil, wt, h0, hm, hle, hF, hw'⟩ := h
  exact ⟨m, Fil, wt, h0, hm, hle, hF, fun i hi ↦ ⟨(hw' i hi).1.trans hw, (hw' i hi).2⟩⟩

/-- Every eigenvalue `α` of an `ι`-mixed Frobenius module of weights at most `w` satisfies
`|ι α| ≤ q ^ (w / 2)`, for `q ≥ 1`: an eigenvector lies in a first step `V_r` of the
filtration, and then `α` is an eigenvalue on `V_r / V_{r-1}`. -/
theorem IsMixedFrobeniusModule.norm_le [IsAlgClosed E] (hq : 1 ≤ q) {F : V ≃ₗ[E] V} {w : ℝ}
    (h : IsMixedFrobeniusModule ι q F w) {α : E}
    (hα : Module.End.HasEigenvalue (F : Module.End E V) α) :
    ‖ι α‖ ≤ (q : ℝ) ^ (w / 2) := by
  classical
  obtain ⟨m, Fil, wt, h0, hm, hle, -, hw⟩ := h
  obtain ⟨v, hv, hv0⟩ := hα.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hv
  have hex : ∃ i, v ∈ Fil i := ⟨m, hm ▸ Submodule.mem_top⟩
  let i := Nat.find hex
  have hi : v ∈ Fil i := Nat.find_spec hex
  have hi0 : i ≠ 0 := fun h ↦ hv0 ((Submodule.mem_bot E).1 (h0 ▸ h ▸ hi))
  obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := Nat.exists_eq_succ_of_ne_zero hi0
  have hvj : v ∉ Fil j := Nat.find_min hex (by omega)
  have hjm : j < m := by
    have : i ≤ m := Nat.find_min' hex (hm ▸ Submodule.mem_top)
    omega
  have hwt := (hw j hjm).2 α v (hj ▸ hi) hvj (by rw [LinearEquiv.coe_coe] at hv; simp [hv])
  rw [IsOfWeight] at hwt
  rw [hwt]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq) (by linarith [(hw j hjm).1])

end FrobeniusModule

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {W : WeilGroup p} {l : ℕ} [Fact l.Prime]

section Operations

variable (W l) {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V)

/-- Blueprint `definition-weil-representation`: Operations on Weil representations.

The determinant line `det V = ⋀^{dim V} V` of a Weil representation, with `g` acting by
`g (v₁ ∧ ⋯ ∧ v_r) = g v₁ ∧ ⋯ ∧ g v_r`. The other operations of the blueprint are
`Representation.directSum`, `Representation.tprod`, `Representation.exteriorPower`,
`Representation.dual` (with `(g λ)(v) = λ (g⁻¹ v)`), the irreducible representations
`Representation.IsIrreducible`, the constituents `Representation.IsConstituent`, the
semisimplification `AlgebraicGeometry.WeilGroup.semisimplification` of a composition series, and,
for a subgroup `I`, the invariants `V^I = (ρ.comp I.subtype).invariants` and coinvariants
`V_I = (ρ.comp I.subtype).Coinvariants`. -/
noncomputable abbrev detLine : Representation (PadicAlgCl l) W.carrier
    ↥(⋀[PadicAlgCl l]^(Module.finrank (PadicAlgCl l) V) V) :=
  ρ.exteriorPower (Module.finrank (PadicAlgCl l) V)

variable {ρ} in
/-- Blueprint `definition-weil-representation`: Operations on Weil representations.

The semisimplification `V^{ss} = ⨁_{i < n} F (i + 1) / F i` of a Weil representation along a
chain of subrepresentations `F 0 ≤ F 1 ≤ ⋯ ≤ F n`; when `F` is a composition series these are
the constituents of `V`, counted with multiplicity. -/
noncomputable abbrev semisimplification (F : ℕ → Subrepresentation ρ) (n : ℕ) :
    Representation (PadicAlgCl l) W.carrier
      (DirectSum (Fin n) fun i ↦
        (F (i + 1)).toSubmodule ⧸ (F i).toSubmodule.comap (F (i + 1)).toSubmodule.subtype) :=
  Representation.directSum fun i : Fin n ↦ (F (i + 1)).subquotient (F i)

end Operations

section Real

variable {V : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V] {ρ : Representation (PadicAlgCl l) W.carrier V}
  (ι : PadicAlgCl l →+* ℂ)

/-- Blueprint `situation-weil`: Local Frobenius polynomials.

The local polynomial of a Weil representation at a closed point `x` is
`P_x(ρ, T) = det (1 - T ρ(F_x) ∣ V)`, the reverse characteristic polynomial of the local
Frobenius element; by `AlgebraicGeometry.WeilGroup.localPolynomial_eq_charpolyRev_of_isConj`
the same holds for every element of the Frobenius conjugacy class of `x`. -/
theorem localPolynomial_eq_charpolyRev (x : C.finitePoints) :
    W.localPolynomial l ρ x = (ρ (W.frobenius x)).charpolyRev :=
  rfl

/-- Blueprint `theorem-purity-real-sheaves-curves`: Reality of exterior powers.

If `ρ` is `ι`-real, then every exterior power `⋀^r ρ` is `ι`-real: its local eigenvalues are
the products of `r`-element sub-multisets of those of `ρ`, which complex conjugation
permutes. -/
theorem IsReal.exteriorPower (hreal : W.IsReal l ρ ι) (r : ℕ) :
    W.IsReal l (ρ.exteriorPower r) ι :=
  hreal.exteriorPower_of_charpoly_eq ι (fun _ ↦ rfl) r

/-- The characteristic polynomials of the semisimplification along a filtration
`0 = F 0 ≤ ⋯ ≤ F n = V` by subrepresentations are those of `ρ`. -/
theorem charpoly_semisimplification {F : ℕ → Subrepresentation ρ} {n : ℕ} (h0 : F 0 = ⊥)
    (hn : F n = ⊤) (hF : ∀ i < n, F i ≤ F (i + 1)) (g : W.carrier) :
    (semisimplification W l F n g).charpoly = (ρ g).charpoly := by
  rw [Representation.charpoly_directSum, LinearMap.charpoly_eq_prod_charpoly_mapQ_of_le (ρ g)
    (fun i ↦ (F i).toSubmodule) n (by rw [h0]; rfl) (by rw [hn]; rfl) hF
    (fun i ↦ (F i).apply_mem_toSubmodule g)]
  exact Fin.prod_univ_eq_prod_range (fun i ↦ ((F (i + 1)).subquotient (F i) g).charpoly) n

/-- Blueprint `theorem-purity-real-sheaves-curves`: Reality survives semisimplification.

The semisimplification `⨁ F (i + 1) / F i` of a Weil representation along a filtration by
subrepresentations (for instance a composition series) has the same local characteristic
polynomials as `ρ`: in a basis adapted to the filtration the local Frobenius is block upper
triangular. -/
theorem localPolynomial_semisimplification {F : ℕ → Subrepresentation ρ} {n : ℕ}
    (h0 : F 0 = ⊥) (hn : F n = ⊤) (hF : ∀ i < n, F i ≤ F (i + 1)) (x : C.finitePoints) :
    W.localPolynomial l (semisimplification W l F n) x = W.localPolynomial l ρ x := by
  rw [localPolynomial, localPolynomial, LinearMap.charpolyRev, LinearMap.charpolyRev,
    charpoly_semisimplification h0 hn hF]

/-- Blueprint `theorem-purity-real-sheaves-curves`: Reality survives semisimplification.

The semisimplification of an `ι`-real Weil representation along a filtration by
subrepresentations (for instance a composition series) is `ι`-real, since it has the same local
characteristic polynomials
(`AlgebraicGeometry.WeilGroup.localPolynomial_semisimplification`). -/
theorem IsReal.semisimplification (hreal : W.IsReal l ρ ι) {F : ℕ → Subrepresentation ρ}
    {n : ℕ} (h0 : F 0 = ⊥) (hn : F n = ⊤) (hF : ∀ i < n, F i ≤ F (i + 1)) :
    W.IsReal l (semisimplification W l F n) ι := fun x m ↦ by
  rw [localPolynomial_semisimplification h0 hn hF]
  exact hreal x m

/-- Blueprint `proposition-weights-under-usual-operations`: Weights, reality and semisimplification.

The semisimplification `⨁ F (i + 1) / F i` along a filtration by subrepresentations has the same
local eigenvalues as `ρ`, since it has the same local characteristic polynomials. -/
theorem localEigenvalues_semisimplification {F : ℕ → Subrepresentation ρ} {n : ℕ}
    (h0 : F 0 = ⊥) (hn : F n = ⊤) (hF : ∀ i < n, F i ≤ F (i + 1)) (x : C.finitePoints) :
    W.localEigenvalues l (semisimplification W l F n) x = W.localEigenvalues l ρ x := by
  rw [localEigenvalues, localEigenvalues, charpoly_semisimplification h0 hn hF]

/-- Blueprint `proposition-weights-under-usual-operations`: Weights, reality and semisimplification.

The semisimplification along a filtration by subrepresentations is punctually `ι`-pure of
weight `w` exactly when `ρ` is. -/
theorem isPunctuallyPure_semisimplification_iff {F : ℕ → Subrepresentation ρ} {n : ℕ}
    (h0 : F 0 = ⊥) (hn : F n = ⊤) (hF : ∀ i < n, F i ≤ F (i + 1)) {w : ℝ} :
    W.IsPunctuallyPure l (semisimplification W l F n) ι w ↔ W.IsPunctuallyPure l ρ ι w := by
  simp only [IsPunctuallyPure, localEigenvalues_semisimplification h0 hn hF]

/-- Blueprint `proposition-weights-under-usual-operations`: Weights, reality and semisimplification.

The semisimplification along a filtration by subrepresentations has `ι`-weights at most `w`
exactly when `ρ` has. -/
theorem hasWeightsAtMost_semisimplification_iff {F : ℕ → Subrepresentation ρ} {n : ℕ}
    (h0 : F 0 = ⊥) (hn : F n = ⊤) (hF : ∀ i < n, F i ≤ F (i + 1)) {w : ℝ} :
    W.HasWeightsAtMost l (semisimplification W l F n) ι w ↔ W.HasWeightsAtMost l ρ ι w := by
  simp only [HasWeightsAtMost, localEigenvalues_semisimplification h0 hn hF]

end Real

end WeilGroup

end AlgebraicGeometry
