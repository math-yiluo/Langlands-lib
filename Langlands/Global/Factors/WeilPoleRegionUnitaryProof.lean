import Langlands.LocalFactor.WeilDeligne
import Langlands.Global.Factors.WeilPoleRegionStatement
import Langlands.LocalField.Normalization.Proof
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The essentially unitary case of the Weil-side pole-region noncancellation

Proof of `Langlands.Global.EssentiallyUnitaryPoleRegionStatement`, the first case of
Henniart 1986, Proposition 4.5(i), Weil side.

A common zero gives Frobenius eigenvectors on `A ⊗ B` and `A^∨ ⊗ B^∨` whose eigenvalues
multiply to `q`. Each eigenvalue factors as a product of eigenvalues of `Φ` or `Φ⁻¹`
on `A` and `B`. Essential unitarity forces the product to have modulus `1`, while
`q > 1`.
-/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.Global.WeilPoleRegionUnitary

/-! ### Zeros of Euler polynomials and eigenvectors -/

section Linear

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A nonzero zero `z` of `det(1 - X T)` gives an eigenvector of `T` with eigenvalue `z⁻¹`. -/
theorem exists_eigenvector_of_eulerPolynomial_eval_eq_zero
    (T : Module.End ℂ V) {z : ℂ} (hz : z ≠ 0)
    (h : (LocalFactor.eulerPolynomial T).eval z = 0) :
    ∃ x : V, x ≠ 0 ∧ T x = z⁻¹ • x := by
  rw [LocalFactor.eulerPolynomial_eval] at h
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.bot_lt_ker_of_det_eq_zero h).ne'
  refine ⟨x, hx0, ?_⟩
  have hx' : x - z • T x = 0 := hx
  have h1 : z • T x = x := (sub_eq_zero.mp hx').symm
  calc T x = z⁻¹ • (z • T x) := by rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
    _ = z⁻¹ • x := by rw [h1]

end Linear

section WeilDeligne

variable {G : Type*} [Group G] {ν : G →* ℂˣ}

/-- A nonzero zero `z` of the Weil–Deligne Euler polynomial `det(1 - X g | (ker N)^I)`
gives a nonzero vector `x` with `N x = 0`, fixed by every element of `I`, and with
`g x = z⁻¹ x`. -/
theorem exists_kernel_eigenvector_of_eulerPolynomial_eval_eq_zero
    (A : WeilDeligneRepresentation ℂ G ν) (I : Subgroup G) [I.Normal] (g : G)
    {z : ℂ} (hz : z ≠ 0)
    (h : (LocalFactor.WeilDeligne.eulerPolynomial A I g).eval z = 0) :
    ∃ x : A, x ≠ 0 ∧ A.monodromy x = 0 ∧ (∀ i ∈ I, A.representation i x = x) ∧
      A.representation g x = z⁻¹ • x := by
  obtain ⟨y, hy0, hy⟩ := exists_eigenvector_of_eulerPolynomial_eval_eq_zero
    (LocalFactor.WeilDeligne.kernelOperator A I g) hz h
  refine ⟨y.val.val, ?_, y.val.property, ?_, ?_⟩
  · intro h0
    apply hy0
    apply Subtype.ext
    apply Subtype.ext
    exact h0
  · intro i hi
    exact congrArg Subtype.val (y.property ⟨i, hi⟩)
  · exact congrArg (fun t => t.val.val) hy

end WeilDeligne

/-! ### Eigenvalues on tensor products and duals -/

section TensorLinear

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- If `S ⊗ 1` has an eigenvector with eigenvalue `c`, then `S` has eigenvalue `c`. -/
theorem exists_eigenvector_of_rTensor_apply_eq {S : Module.End ℂ V} {c : ℂ}
    {u : V ⊗[ℂ] W} (hu : u ≠ 0) (h : LinearMap.rTensor W S u = c • u) :
    ∃ a : V, a ≠ 0 ∧ S a = c • a := by
  by_contra hne
  push Not at hne
  have hinj : Function.Injective ⇑(S - c • (1 : Module.End ℂ V)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    apply hne a ha0
    have h0 : S a - c • a = 0 := by simpa using ha
    exact sub_eq_zero.mp h0
  apply hu
  apply Module.Flat.rTensor_preserves_injective_linearMap (M := W) _ hinj
  rw [map_zero, LinearMap.rTensor_sub, LinearMap.rTensor_smul, Module.End.one_eq_id, LinearMap.rTensor_id,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, h, sub_self]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- If `1 ⊗ T` has an eigenvector with eigenvalue `c`, then `T` has eigenvalue `c`. -/
theorem exists_eigenvector_of_lTensor_apply_eq {T : Module.End ℂ W} {c : ℂ}
    {u : V ⊗[ℂ] W} (hu : u ≠ 0) (h : LinearMap.lTensor V T u = c • u) :
    ∃ b : W, b ≠ 0 ∧ T b = c • b := by
  by_contra hne
  push Not at hne
  have hinj : Function.Injective ⇑(T - c • (1 : Module.End ℂ W)) := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    apply hne b hb0
    have h0 : T b - c • b = 0 := by simpa using hb
    exact sub_eq_zero.mp h0
  apply hu
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ hinj
  rw [map_zero, LinearMap.lTensor_sub, LinearMap.lTensor_smul, Module.End.one_eq_id, LinearMap.lTensor_id,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, h, sub_self]

/-- An eigenvalue `c` of `S ⊗ T`, with `S` injective, is a product `α β` of an
eigenvalue `α` of `S` and an eigenvalue `β` of `T`. -/
theorem exists_eigenvalues_of_map_apply_eq {S : Module.End ℂ V} {T : Module.End ℂ W}
    (hS : Function.Injective S) {c : ℂ} {v : V ⊗[ℂ] W} (hv : v ≠ 0)
    (h : TensorProduct.map S T v = c • v) :
    ∃ α β : ℂ, (∃ a : V, a ≠ 0 ∧ S a = α • a) ∧ (∃ b : W, b ≠ 0 ∧ T b = β • b) ∧
      c = α * β := by
  set M : Module.End ℂ (V ⊗[ℂ] W) := TensorProduct.map S T with hM
  set R : Module.End ℂ (V ⊗[ℂ] W) := LinearMap.rTensor W S with hR
  let U : Submodule ℂ (V ⊗[ℂ] W) := LinearMap.ker (M - c • (1 : Module.End ℂ (V ⊗[ℂ] W)))
  have hcomm : ∀ x, M (R x) = R (M x) := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hM, hR,
      LinearMap.map_comp_rTensor, LinearMap.rTensor_comp_map]
  have hmemU : ∀ x, x ∈ U ↔ M x = c • x := by
    intro x
    simp only [U, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have hU : ∀ x ∈ U, R x ∈ U := by
    intro x hx
    rw [hmemU] at hx ⊢
    rw [hcomm, hx, map_smul]
  let R' : Module.End ℂ U := R.restrict hU
  have hvU : v ∈ U := (hmemU v).mpr h
  have hUne : U ≠ ⊥ := by
    intro hb
    apply hv
    have : v ∈ (⊥ : Submodule ℂ (V ⊗[ℂ] W)) := hb ▸ hvU
    exact (Submodule.mem_bot ℂ).mp this
  have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hUne
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue R'
  obtain ⟨u, hu⟩ := hα.exists_hasEigenvector
  have hu0 : (u : V ⊗[ℂ] W) ≠ 0 := by
    intro h0
    exact hu.2 (Subtype.ext h0)
  have hRu : R u = α • (u : V ⊗[ℂ] W) := by
    have h1 : R' u = α • u := Module.End.mem_eigenspace_iff.mp hu.1
    exact congrArg Subtype.val h1
  have hMu : M u = c • (u : V ⊗[ℂ] W) := (hmemU u).mp u.property
  have hα0 : α ≠ 0 := by
    rintro rfl
    apply hu0
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := W) S hS
    change R u = R 0
    rw [hRu, zero_smul, map_zero]
  have hLu : LinearMap.lTensor V T u = (c / α) • (u : V ⊗[ℂ] W) := by
    have hML : M u = LinearMap.lTensor V T (R u) := by
      rw [← LinearMap.comp_apply (LinearMap.lTensor V T), hR, LinearMap.lTensor_comp_rTensor]
    rw [hRu, map_smul, hMu] at hML
    calc LinearMap.lTensor V T u
        = α⁻¹ • (α • LinearMap.lTensor V T u) := by
          rw [smul_smul, inv_mul_cancel₀ hα0, one_smul]
      _ = α⁻¹ • (c • (u : V ⊗[ℂ] W)) := by rw [hML]
      _ = (c / α) • (u : V ⊗[ℂ] W) := by rw [smul_smul, div_eq_inv_mul]
  refine ⟨α, c / α, exists_eigenvector_of_rTensor_apply_eq hu0 hRu,
    exists_eigenvector_of_lTensor_apply_eq hu0 hLu, ?_⟩
  field_simp

/-- An eigenvalue of the transpose `f.dualMap` is an eigenvalue of `f`. -/
theorem exists_eigenvector_of_dualMap_apply_eq {f : Module.End ℂ V} {c : ℂ}
    {ℓ : Module.Dual ℂ V} (hℓ : ℓ ≠ 0) (h : f.dualMap ℓ = c • ℓ) :
    ∃ a : V, a ≠ 0 ∧ f a = c • a := by
  by_contra hne
  push Not at hne
  have hinj : Function.Injective ⇑(f - c • (1 : Module.End ℂ V)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    apply hne a ha0
    have h0 : f a - c • a = 0 := by simpa using ha
    exact sub_eq_zero.mp h0
  have hsurj : Function.Surjective ⇑(f - c • (1 : Module.End ℂ V)) :=
    LinearMap.injective_iff_surjective.mp hinj
  apply hℓ
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  have hy := LinearMap.congr_fun h y
  simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul] at hy
  simp [hy]

end TensorLinear

/-! ### Eigenvalues of unitary operators -/

section Unitary

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- If scaling a nonzero vector by `c` preserves its inner product with itself, then
`‖c‖ = 1`. -/
theorem norm_eq_one_of_inner_smul_self (h : InnerProductSpace.Core ℂ V) {c : ℂ} {a : V}
    (ha : a ≠ 0) (hc : h.inner (c • a) (c • a) = h.inner a a) : ‖c‖ = 1 := by
  have e1 : h.inner (c • a) a = (starRingEnd ℂ) c * h.inner a a := h.smul_left a a c
  have e2 : h.inner a (c • a) = c * h.inner a a := by
    rw [← h.conj_inner_symm a (c • a), e1, map_mul, Complex.conj_conj, h.conj_inner_symm]
  have e3 : h.inner (c • a) (c • a) = (starRingEnd ℂ) c * c * h.inner a a := by
    rw [h.smul_left, e2, mul_assoc]
  have hne : h.inner a a ≠ 0 := fun h0 => ha (h.definite a h0)
  rw [e3] at hc
  have hcc : (starRingEnd ℂ) c * c = 1 := by
    apply mul_right_cancel₀ hne
    rw [hc, one_mul]
  have hn : ‖c‖ * ‖c‖ = 1 := by
    have := congrArg norm hcc
    rwa [norm_mul, Complex.norm_conj, norm_one] at this
  nlinarith [norm_nonneg c]

/-- In a representation whose twist by `χ` is unitary, every eigenvalue `c` of `g`
satisfies `‖χ(g) c‖ = 1`. -/
theorem norm_character_mul_eigenvalue_eq_one {G : Type*} [Group G]
    (A : FiniteRepresentation ℂ G) (χ : G →* ℂˣ)
    (hA : (FiniteRepresentation.twist χ A).IsUnitary) (g : G) {c : ℂ} {a : A}
    (ha : a ≠ 0) (hga : A.representation g a = c • a) : ‖(χ g : ℂ) * c‖ = 1 := by
  obtain ⟨h, hh⟩ := hA
  have h1 := hh g a a
  change h.inner ((χ g : ℂ) • A.representation g a) ((χ g : ℂ) • A.representation g a) =
    h.inner a a at h1
  rw [hga, smul_smul] at h1
  exact norm_eq_one_of_inner_smul_self h ha h1

end Unitary

/-! ### Eigenvalues on tensor products of representations -/

section Representations

variable {G : Type*} [Group G]

/-- An eigenvalue `c` of `g` on `A ⊗ B` is a product of an eigenvalue of `g` on `A` and
an eigenvalue of `g` on `B`. -/
theorem exists_eigenvalues_of_tensor_apply_eq (A : FiniteRepresentation ℂ G)
    (B : FiniteRepresentation ℂ G) (g : G) {c : ℂ} {x : FiniteRepresentation.tensor A B}
    (hx : x ≠ 0) (h : (FiniteRepresentation.tensor A B).representation g x = c • x) :
    ∃ α β : ℂ, (∃ a : A, a ≠ 0 ∧ A.representation g a = α • a) ∧
      (∃ b : B, b ≠ 0 ∧ B.representation g b = β • b) ∧ c = α * β :=
  exists_eigenvalues_of_map_apply_eq (A.representation.apply_bijective g).1 hx h

/-- An eigenvalue `c` of `g` on the dual `A^∨` is an eigenvalue of `g⁻¹` on `A`. -/
theorem exists_eigenvector_of_dual_apply_eq (A : FiniteRepresentation ℂ G) (g : G) {c : ℂ}
    {ℓ : FiniteRepresentation.dual A} (hℓ : ℓ ≠ 0)
    (h : (FiniteRepresentation.dual A).representation g ℓ = c • ℓ) :
    ∃ a : A, a ≠ 0 ∧ A.representation g⁻¹ a = c • a :=
  exists_eigenvector_of_dualMap_apply_eq (f := A.representation g⁻¹) hℓ h

end Representations

end Langlands.Global.WeilPoleRegionUnitary

/-! ### The essentially unitary case -/

namespace Langlands.Global

open Langlands.Weil.Local WeilPoleRegion WeilPoleRegionUnitary

/-- Henniart 1986, Proposition 4.5(i), first case (Weil side, zero monodromy): for
essentially unitary `A` and `B`, the L-polynomial of `(A, 0) ⊗ (B, 0)` and the reflected
L-polynomial of `(A, 0)^∨ ⊗ (B, 0)^∨` have no common zero. -/
theorem essentiallyUnitaryPoleRegionStatement :
    EssentiallyUnitaryPoleRegionStatement.{u, v, w} := by
  intro p _ F A B hA hB σ σ' z hz hzz
  obtain ⟨h1, h2⟩ := hzz
  set Φ := localGeometricFrobenius F
  set q : ℕ := residueCardinality F with hqdef
  have hq1 : 1 < q := F.canonicalTopologicalData.residueCardinality_gt_one
  have hq0 : (q : ℂ) ≠ 0 := by
    have : (0 : ℕ) < q := lt_trans Nat.zero_lt_one hq1
    exact_mod_cast this.ne'
  have hz' : (q : ℂ)⁻¹ * z⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hq0) (inv_ne_zero hz)
  -- Frobenius eigenvectors from the two zeros.
  obtain ⟨x, hx0, -, -, hx⟩ := exists_kernel_eigenvector_of_eulerPolynomial_eval_eq_zero
    (localParameterTensor F σ σ').val (localInertia F) Φ hz h1
  obtain ⟨y, hy0, -, -, hy⟩ := exists_kernel_eigenvector_of_eulerPolynomial_eval_eq_zero
    (localParameterTensor F (localParameterDual F σ) (localParameterDual F σ')).val
    (localInertia F) Φ hz' h2
  -- Factor both eigenvalues.
  obtain ⟨α, β, ⟨a, ha0, ha⟩, ⟨b, hb0, hb⟩, hc⟩ :=
    exists_eigenvalues_of_tensor_apply_eq A.val B.val Φ (x := x) hx0 hx
  obtain ⟨α', β', ⟨ℓ, hℓ0, hℓ⟩, ⟨m, hm0, hm⟩, hc'⟩ :=
    exists_eigenvalues_of_tensor_apply_eq (FiniteRepresentation.dual A.val)
      (FiniteRepresentation.dual B.val) Φ (x := y) hy0 hy
  obtain ⟨a', ha'0, ha'⟩ := exists_eigenvector_of_dual_apply_eq A.val Φ hℓ0 hℓ
  obtain ⟨b', hb'0, hb'⟩ := exists_eigenvector_of_dual_apply_eq B.val Φ hm0 hm
  -- Unitarity bounds.
  obtain ⟨χA, hχA⟩ := hA
  obtain ⟨χB, hχB⟩ := hB
  have uA := norm_character_mul_eigenvalue_eq_one A.val χA.toMonoidHom hχA Φ ha0 ha
  have uB := norm_character_mul_eigenvalue_eq_one B.val χB.toMonoidHom hχB Φ hb0 hb
  have uA' := norm_character_mul_eigenvalue_eq_one A.val χA.toMonoidHom hχA Φ⁻¹ ha'0 ha'
  have uB' := norm_character_mul_eigenvalue_eq_one B.val χB.toMonoidHom hχB Φ⁻¹ hb'0 hb'
  rw [map_inv, Units.val_inv_eq_inv_val] at uA' uB'
  set cA : ℂ := ((χA.toMonoidHom Φ : ℂˣ) : ℂ)
  set cB : ℂ := ((χB.toMonoidHom Φ : ℂˣ) : ℂ)
  have hcA : cA ≠ 0 := Units.ne_zero _
  have hcB : cB ≠ 0 := Units.ne_zero _
  have key : (cA * α) * (cA⁻¹ * α') * (cB * β) * (cB⁻¹ * β') = (q : ℂ) := by
    calc (cA * α) * (cA⁻¹ * α') * (cB * β) * (cB⁻¹ * β')
        = (α * β) * (α' * β') * (cA * cA⁻¹) * (cB * cB⁻¹) := by ring
      _ = z⁻¹ * ((q : ℂ)⁻¹ * z⁻¹)⁻¹ := by
          rw [mul_inv_cancel₀ hcA, mul_inv_cancel₀ hcB, ← hc, ← hc', mul_one, mul_one]
      _ = (q : ℂ) := by field_simp
  have hnorm := congrArg norm key
  rw [norm_mul, norm_mul, norm_mul, uA, uA', uB, uB', Complex.norm_natCast] at hnorm
  have : (q : ℝ) = 1 := by linarith
  have : q = 1 := by exact_mod_cast this
  omega

end Langlands.Global
