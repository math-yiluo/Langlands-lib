import Langlands.Shimura.Unitary.ComplexMatrixSplitting
import Langlands.Algebra.LieEnvelopingEquiv
import Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter
import Langlands.Representation.Archimedean.GLProductWhittaker
import Langlands.Representation.Archimedean.ComplexGenericStandardInjectiveReduction

/-!
# Generic `(𝔤𝔩_n(ℂ), U(n))`-modules are large, given Kostant's theorem for `𝔤𝔩_n(ℂ)²`

`ComplexGenericLargeReductionStatement` says that Kostant's theorem for finite products of
`𝔤𝔩_n(ℂ)` (`GLProductWhittakerMaximallyFaithfulStatement`) implies
`ComplexGenericLargeStatement`; `complexGenericLargeReduction` proves it. The action `π` of
`ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` is transported along `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ) ≅ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`,
`z ⊗ X ↦ (zX, zX̄)`. There the infinitesimal character is proved (adapting
`RealGKInfinitesimalCharacter`) and the Whittaker identity holds with coefficients
`(i/2) a_p` and `(i/2) ā_p`. Kostant's theorem then applies, and maximal faithfulness is
transported back.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

universe uV

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open InfinitesimalCharacter

namespace ComplexGenericLarge

/-! ## Transport along an isomorphism of Lie algebras -/

section Transport

open Langlands.Algebra.LieEnvelopingEquiv (enveloping)

variable {L L' : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing L'] [LieAlgebra ℂ L']

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem envelopingAction_enveloping (e : L ≃ₗ⁅ℂ⁆ L') (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (u : UniversalEnvelopingAlgebra ℂ L) :
    envelopingAction (π.comp e.symm.toLieHom) (enveloping e u) = envelopingAction π u := by
  have h : (envelopingAction (π.comp e.symm.toLieHom)).comp (enveloping e).toAlgHom =
      envelopingAction π := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => ?_
    simp [enveloping, Langlands.Algebra.LieEnvelopingEquiv.map]
  exact AlgHom.congr_fun h u

/-- Maximal faithfulness transported back along an isomorphism of Lie algebras. -/
theorem isMaximallyFaithful_of_comp (e : L ≃ₗ⁅ℂ⁆ L') (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (h : IsMaximallyFaithful (π.comp e.symm.toLieHom)) : IsMaximallyFaithful π := by
  intro u hu
  have h1 := h (enveloping e u) (by rw [envelopingAction_enveloping, hu])
  have h2 : ∀ x ∈ Ideal.span {z | z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ L') ∧
      envelopingAction (π.comp e.symm.toLieHom) z = 0},
      (enveloping e).symm x ∈ Ideal.span {z | z ∈ Subalgebra.center ℂ
        (UniversalEnvelopingAlgebra ℂ L) ∧ envelopingAction π z = 0} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      refine Ideal.subset_span ⟨?_, ?_⟩
      · rw [Subalgebra.mem_center_iff]
        intro b
        have hc := (Subalgebra.mem_center_iff.1 hx.1) (enveloping e b)
        calc b * (enveloping e).symm x
            = (enveloping e).symm (enveloping e b * x) := by
              rw [map_mul, AlgEquiv.symm_apply_apply]
          _ = (enveloping e).symm (x * enveloping e b) := by rw [hc]
          _ = (enveloping e).symm x * b := by rw [map_mul, AlgEquiv.symm_apply_apply]
      · rw [← envelopingAction_enveloping e π, AlgEquiv.apply_symm_apply]
        exact hx.2
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Ideal.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_eq_mul, map_mul]
      exact Ideal.mul_mem_left _ _ hx
  simpa using h2 _ h1

end Transport

/-! ## The isomorphism `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ) ≅ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)` -/

section Iso

variable {n : ℕ}

/-- The entrywise complex conjugate of a matrix. -/
abbrev conjMat (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  X.map (starRingEnd ℂ)

theorem conjMat_apply (X : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    conjMat X p q = starRingEnd ℂ (X p q) :=
  rfl

/-- `X ↦ (X, X̄)`, an `ℝ`-algebra map `M_n(ℂ) → M_n(ℂ) × M_n(ℂ)`. -/
def pairHom : Matrix (Fin n) (Fin n) ℂ →ₐ[ℝ] (Fin 2 → Matrix (Fin n) (Fin n) ℂ) where
  toFun X := ![X, conjMat X]
  map_one' := by
    funext i
    fin_cases i
    · rfl
    · ext p q
      simp [Matrix.one_apply]
  map_mul' X Y := by
    funext i
    fin_cases i
    · rfl
    · simp [Matrix.map_mul]
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' X Y := by
    funext i
    fin_cases i
    · rfl
    · simp [Matrix.map_add]
  commutes' r := by
    funext i
    fin_cases i
    · rfl
    · ext p q
      simp [Matrix.algebraMap_matrix_apply]

theorem pairHom_zero (X : Matrix (Fin n) (Fin n) ℂ) : pairHom X 0 = X :=
  rfl

theorem pairHom_one (X : Matrix (Fin n) (Fin n) ℂ) : pairHom X 1 = conjMat X :=
  rfl

/-- The evident `ℂ`-algebra isomorphism `A × A ≃ (Fin 2 → A)` for `A = M_n(ℂ)`. -/
def prodFinTwo : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ≃ₐ[ℂ]
    (Fin 2 → Matrix (Fin n) (Fin n) ℂ) :=
  AlgEquiv.ofRingEquiv (f := (RingEquiv.piFinTwo fun _ : Fin 2 => Matrix (Fin n) (Fin n) ℂ).symm)
    fun c => by
      funext i
      fin_cases i <;> rfl

/-- The `ℂ`-algebra isomorphism `ℂ ⊗_ℝ M_n(ℂ) ≃ M_n(ℂ) × M_n(ℂ)`, `z ⊗ X ↦ (z X, z X̄)`:
the Library's `Langlands.Shimura.ComplexMatrix.complexEquiv`, with the product written as
functions on `Fin 2`. -/
def tensorEquiv : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] (Fin 2 → Matrix (Fin n) (Fin n) ℂ) :=
  (Langlands.Shimura.ComplexMatrix.complexEquiv n).trans prodFinTwo

theorem tensorEquiv_tmul (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    tensorEquiv (z ⊗ₜ[ℝ] X) = z • pairHom X := by
  rw [tensorEquiv, AlgEquiv.trans_apply, Langlands.Shimura.ComplexMatrix.complexEquiv_tmul]
  funext i
  fin_cases i
  · rfl
  · ext p q
    simp [prodFinTwo, pairHom_one]

/-- An explicit preimage of `(A, B)` under `tensorEquiv`:
`½ (1 ⊗ A - i ⊗ iA + 1 ⊗ B̄ + i ⊗ iB̄)`. -/
def tensorInv (Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] Y 0 - Complex.I • ((1 : ℂ) ⊗ₜ[ℝ] (Complex.I • Y 0)) +
    (1 : ℂ) ⊗ₜ[ℝ] conjMat (Y 1) + Complex.I • ((1 : ℂ) ⊗ₜ[ℝ] (Complex.I • conjMat (Y 1))))

theorem tensorEquiv_tensorInv (Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) :
    tensorEquiv (tensorInv Y) = Y := by
  rw [tensorInv, map_smul, map_add, map_add, map_sub, map_smul, map_smul, tensorEquiv_tmul,
    tensorEquiv_tmul, tensorEquiv_tmul, tensorEquiv_tmul]
  funext i
  fin_cases i
  · ext p q
    simp [pairHom_zero]
    ring_nf
    simp [Complex.I_sq]
    ring
  · ext p q
    simp [pairHom_one]
    ring_nf
    simp [Complex.I_sq]
    ring

theorem tensorEquiv_symm_apply (Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) :
    tensorEquiv.symm Y = tensorInv Y := by
  rw [AlgEquiv.symm_apply_eq, tensorEquiv_tensorInv]

theorem tensorEquiv_symm_pairHom (X : Matrix (Fin n) (Fin n) ℂ) :
    tensorEquiv.symm (pairHom X) = (1 : ℂ) ⊗ₜ[ℝ] X := by
  rw [AlgEquiv.symm_apply_eq, tensorEquiv_tmul, one_smul]

/-- The bracket of `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` (extension of scalars) is the commutator of the algebra
`ℂ ⊗_ℝ M_n(ℂ)`. -/
theorem lie_eq_mul_sub (x y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) : ⁅x, y⁆ = x * y - y * x := by
  induction x using TensorProduct.inductionOn with
  | tmul a X =>
    induction y using TensorProduct.inductionOn with
    | tmul b Y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Ring.lie_def, TensorProduct.tmul_sub, mul_comm b a]
    | add y y' hy hy' =>
      calc ⁅a ⊗ₜ[ℝ] X, y + y'⁆ = ⁅a ⊗ₜ[ℝ] X, y⁆ + ⁅a ⊗ₜ[ℝ] X, y'⁆ :=
          lie_add (L := ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) (M := ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)
            _ _ _
        _ = _ := by rw [hy, hy', mul_add, add_mul]; abel
  | add x x' hx hx' =>
    calc ⁅x + x', y⁆ = ⁅x, y⁆ + ⁅x', y⁆ :=
        add_lie (L := ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) (M := ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ)
          _ _ _
      _ = _ := by rw [hx, hx', mul_add, add_mul]; abel

/-- `tensorEquiv` as an isomorphism of complex Lie algebras
`ℂ ⊗_ℝ 𝔤𝔩_n(ℂ) ≃ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`. -/
def tensorLieEquiv :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) ≃ₗ⁅ℂ⁆ (Fin 2 → Matrix (Fin n) (Fin n) ℂ) where
  toFun := tensorEquiv
  map_add' := map_add tensorEquiv
  map_smul' := map_smul tensorEquiv
  map_lie' {x y} := by
    simp only [lie_eq_mul_sub, LieRing.of_associative_ring_bracket, map_sub, map_mul]
  invFun := tensorEquiv.symm
  left_inv := tensorEquiv.symm_apply_apply
  right_inv := tensorEquiv.apply_symm_apply

theorem tensorLieEquiv_symm_apply (Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) :
    tensorLieEquiv.symm Y = tensorEquiv.symm Y :=
  rfl

end Iso

/-! ## Inner automorphisms of an associative algebra fixing the center of `U` -/

section Assoc

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- Conjugation by a unit of `B`, as a Lie algebra automorphism of `B` (commutator bracket). -/
def conjLieB (w : Bˣ) : B →ₗ⁅ℂ⁆ B :=
  (unitConj w).toLieHom

theorem conjLieB_apply (w : Bˣ) (x : B) : conjLieB w x = (w : B) * x * ((w⁻¹ : Bˣ) : B) :=
  rfl

theorem conjLieB_mul (w₁ w₂ : Bˣ) : conjLieB (w₁ * w₂) = (conjLieB w₁).comp (conjLieB w₂) :=
  LieHom.ext fun x => by
    rw [LieHom.comp_apply]
    exact congrArg (fun f : B →ₐ[ℂ] B => f x) (unitConj_mul w₁ w₂)

theorem conjLieB_one : conjLieB (1 : Bˣ) = LieHom.id :=
  LieHom.ext fun x => by
    rw [LieHom.id_apply]
    exact congrArg (fun f : B →ₐ[ℂ] B => f x) unitConj_one

/-- Conjugation by `w = 1 + (c - 1) e`, `e` idempotent, fixes the center of `U(B)`: `B` is the
sum of the weight spaces of `ad e` with weights `0, ±1`, on which `Ad(w)` acts by `c ^ m`. -/
theorem envMap_conjLieB_idempotent {e : B} (he : e * e = e) {c : ℂ} (hc : c ≠ 0) (w : Bˣ)
    (hw : (w : B) = 1 + (c - 1) • e) {z : UniversalEnvelopingAlgebra ℂ B}
    (hz : z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ B)) :
    envMap (conjLieB w) z = z := by
  set W := (w : B)
  set W' := ((w⁻¹ : Bˣ) : B)
  have hw' : W' = 1 + (c⁻¹ - 1) • e := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    change W * _ = 1
    rw [hw]
    exact idempotent_unit_mul he hc
  have ee' : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have e'e : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have we : W * e = c • e := by
    rw [hw, add_mul, one_mul, smul_mul_assoc, he]; module
  have ew : e * W' = c⁻¹ • e := by
    rw [hw', mul_add, mul_one, mul_smul_comm, he]; module
  have we' : W * (1 - e) = 1 - e := by
    rw [hw, add_mul, one_mul, smul_mul_assoc, ee', smul_zero, add_zero]
  have ew' : (1 - e) * W' = 1 - e := by
    rw [hw', mul_add, mul_one, mul_smul_comm, e'e, smul_zero, add_zero]
  refine envMap_fixes_center (e := e) hc (fun x => ?_) hz
  have hx : x = e * x * e + e * x * (1 - e) + (1 - e) * x * e + (1 - e) * x * (1 - e) := by
    have h1 : e * x * e + e * x * (1 - e) = e * x := by rw [← mul_add, add_sub_cancel, mul_one]
    have h2 : (1 - e) * x * e + (1 - e) * x * (1 - e) = (1 - e) * x := by
      rw [← mul_add, add_sub_cancel, mul_one]
    rw [add_assoc (e * x * e + e * x * (1 - e)), h1, h2, ← add_mul, add_sub_cancel, one_mul]
  rw [hx]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
  · refine Submodule.mem_iSup_of_mem 0 ⟨?_, ?_⟩
    · rw [LieRing.of_associative_ring_bracket]
      have h1 : e * (e * x * e) = e * x * e := by rw [← mul_assoc, ← mul_assoc, he]
      have h2 : e * x * e * e = e * x * e := by rw [mul_assoc _ e e, he]
      rw [h1, h2, sub_self, Int.cast_zero, zero_smul]
    · rw [conjLieB_apply, zpow_zero, one_smul]
      calc W * (e * x * e) * W' = (W * e) * x * (e * W') := by noncomm_ring
        _ = e * x * e := by
          rw [we, ew, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
            mul_inv_cancel₀ hc, one_smul]
  · refine Submodule.mem_iSup_of_mem 1 ⟨?_, ?_⟩
    · rw [LieRing.of_associative_ring_bracket]
      have h1 : e * (e * x * (1 - e)) = e * x * (1 - e) := by
        rw [← mul_assoc, ← mul_assoc, he]
      have h2 : e * x * (1 - e) * e = 0 := by rw [mul_assoc _ (1 - e) e, e'e, mul_zero]
      rw [h1, h2, sub_zero, Int.cast_one, one_smul]
    · rw [conjLieB_apply, zpow_one]
      calc W * (e * x * (1 - e)) * W' = (W * e) * x * ((1 - e) * W') := by noncomm_ring
        _ = c • (e * x * (1 - e)) := by rw [we, ew', smul_mul_assoc, smul_mul_assoc]
  · refine Submodule.mem_iSup_of_mem (-1) ⟨?_, ?_⟩
    · rw [LieRing.of_associative_ring_bracket]
      have h1 : e * ((1 - e) * x * e) = 0 := by
        rw [← mul_assoc, ← mul_assoc, ee', zero_mul, zero_mul]
      have h2 : (1 - e) * x * e * e = (1 - e) * x * e := by rw [mul_assoc _ e e, he]
      rw [h1, h2, zero_sub, Int.cast_neg, Int.cast_one, neg_one_smul]
    · rw [conjLieB_apply, zpow_neg_one]
      calc W * ((1 - e) * x * e) * W' = (W * (1 - e)) * x * (e * W') := by noncomm_ring
        _ = c⁻¹ • ((1 - e) * x * e) := by rw [we', ew, mul_smul_comm]
  · refine Submodule.mem_iSup_of_mem 0 ⟨?_, ?_⟩
    · rw [LieRing.of_associative_ring_bracket]
      have h1 : e * ((1 - e) * x * (1 - e)) = 0 := by
        rw [← mul_assoc, ← mul_assoc, ee', zero_mul, zero_mul]
      have h2 : (1 - e) * x * (1 - e) * e = 0 := by rw [mul_assoc _ (1 - e) e, e'e, mul_zero]
      rw [h1, h2, sub_zero, Int.cast_zero, zero_smul]
    · rw [conjLieB_apply, zpow_zero, one_smul]
      calc W * ((1 - e) * x * (1 - e)) * W' = (W * (1 - e)) * x * ((1 - e) * W') := by
            noncomm_ring
        _ = (1 - e) * x * (1 - e) := by rw [we', ew']

/-- The elements `M` of `B` such that conjugation by any unit with underlying element `M` fixes
the center of `U(B)`. -/
def ConjFixesCenter (M : B) : Prop :=
  ∀ w : Bˣ, (w : B) = M →
    ∀ z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ B), envMap (conjLieB w) z = z

theorem conjFixesCenter_mul {M N : B} (hM : IsUnit M) (hMf : ConjFixesCenter M)
    (hNf : ConjFixesCenter N) : ConjFixesCenter (M * N) := by
  intro w hw z hz
  obtain ⟨u, hu⟩ := hM
  have h₂ : ((u⁻¹ * w : Bˣ) : B) = N := by
    rw [Units.val_mul, hw, ← hu, Units.inv_mul_cancel_left]
  have hw' : w = u * (u⁻¹ * w) := (mul_inv_cancel_left u w).symm
  rw [hw', conjLieB_mul, envMap_comp, AlgHom.comp_apply, hNf _ h₂ z hz, hMf _ hu z hz]

theorem conjFixesCenter_idempotent {e : B} (he : e * e = e) {c : ℂ} (hc : c ≠ 0) :
    ConjFixesCenter (1 + (c - 1) • e) :=
  fun w hw _ hz => envMap_conjLieB_idempotent he hc w hw hz

theorem isUnit_idempotent {e : B} (he : e * e = e) {c : ℂ} (hc : c ≠ 0) :
    IsUnit (1 + (c - 1) • e) :=
  ⟨⟨1 + (c - 1) • e, 1 + (c⁻¹ - 1) • e, idempotent_unit_mul he hc, by
    simpa [inv_inv] using idempotent_unit_mul he (inv_ne_zero hc)⟩, rfl⟩

end Assoc

/-! ## Invertible complex matrices `X` whose image `(X, X̄)` fixes the center -/

section Matrices

variable {n : ℕ}

/-- `(X, X̄)` (conjugation by any unit with this underlying element) fixes the center of
`U(𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ))`. -/
abbrev PairFixesCenter (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ConjFixesCenter (pairHom X)

theorem isUnit_pairHom {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.det ≠ 0) : IsUnit (pairHom X) :=
  ((Matrix.isUnit_iff_isUnit_det X).2 (isUnit_iff_ne_zero.2 hX)).map pairHom

theorem pairFixesCenter_mul {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X.det ≠ 0)
    (hXf : PairFixesCenter X) (hYf : PairFixesCenter Y) : PairFixesCenter (X * Y) := by
  unfold PairFixesCenter
  rw [map_mul]
  exact conjFixesCenter_mul (isUnit_pairHom hX) hXf hYf

theorem pairHom_idempotent {E : Matrix (Fin n) (Fin n) ℂ} (d : ℂ) :
    pairHom (1 + (d - 1) • E) =
      (1 + (d - 1) • (Pi.single 0 E : Fin 2 → Matrix (Fin n) (Fin n) ℂ)) *
        (1 + (starRingEnd ℂ d - 1) •
          (Pi.single 1 (conjMat E) : Fin 2 → Matrix (Fin n) (Fin n) ℂ)) := by
  funext i
  fin_cases i
  · simp [pairHom_zero]
  · show conjMat (1 + (d - 1) • E) = _
    ext p q
    simp [Matrix.one_apply]

theorem pairFixesCenter_idempotent {E : Matrix (Fin n) (Fin n) ℂ} (hE : E * E = E) {d : ℂ}
    (hd : d ≠ 0) : PairFixesCenter (1 + (d - 1) • E) := by
  have h0 : (Pi.single 0 E : Fin 2 → Matrix (Fin n) (Fin n) ℂ) * Pi.single 0 E =
      Pi.single 0 E := by
    rw [← Pi.single_mul, hE]
  have h1 : (Pi.single 1 (conjMat E) : Fin 2 → Matrix (Fin n) (Fin n) ℂ) *
      Pi.single 1 (conjMat E) = Pi.single 1 (conjMat E) := by
    rw [← Pi.single_mul, conjMat, ← Matrix.map_mul, hE]
  have hd' : starRingEnd ℂ d ≠ 0 := (map_ne_zero _).2 hd
  unfold PairFixesCenter
  rw [pairHom_idempotent]
  exact conjFixesCenter_mul (isUnit_idempotent h0 hd) (conjFixesCenter_idempotent h0 hd)
    (conjFixesCenter_idempotent h1 hd')

theorem det_ne_zero_of_idempotent {E : Matrix (Fin n) (Fin n) ℂ} (hE : E * E = E) {c : ℂ}
    (hc : c ≠ 0) : (1 + (c - 1) • E).det ≠ 0 :=
  (Matrix.isUnit_det_of_right_inverse (idempotent_unit_mul hE hc)).ne_zero

theorem diagonal_ite_eq (d : ℂ) (i : Fin n) :
    Matrix.diagonal (fun j => if j = i then d else 1) =
      1 + (d - 1) • Matrix.single i i (1 : ℂ) := by
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases hai : a = i
    · subst hai; simp
    · simp [hai, Ne.symm hai]
  · have h : ¬(i = a ∧ i = b) := fun h => hab (h.1.symm.trans h.2)
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab,
      Matrix.one_apply_ne hab, Matrix.single_apply, ite_eq_right_iff.2 (fun h' => absurd h' h),
      smul_zero, add_zero]

theorem pairFixesCenter_diagonal (D : Fin n → ℂ) (hD : ∀ i, D i ≠ 0) :
    PairFixesCenter (Matrix.diagonal D) := by
  classical
  have key : ∀ s : Finset (Fin n),
      PairFixesCenter (Matrix.diagonal fun j => if j ∈ s then D j else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro w hw z _
      have h1 : (Matrix.diagonal fun j => if j ∈ (∅ : Finset (Fin n)) then D j else 1) = 1 := by
        simp
      have : w = 1 := Units.ext (by rw [hw, h1, map_one, Units.val_one])
      rw [this, conjLieB_one, envMap_id, AlgHom.id_apply]
    | insert i s hi ih =>
      have hsplit : (Matrix.diagonal fun j => if j ∈ insert i s then D j else 1) =
          (Matrix.diagonal fun j => if j ∈ s then D j else 1) *
            Matrix.diagonal (fun j => if j = i then D i else 1) := by
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      rw [hsplit]
      refine pairFixesCenter_mul ?_ ih ?_
      · rw [Matrix.det_diagonal]
        refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
        split_ifs
        exacts [hD j, one_ne_zero]
      · rw [diagonal_ite_eq]
        exact pairFixesCenter_idempotent (by simp) (hD i)
  simpa using key Finset.univ

theorem pairFixesCenter_transvection (t : Matrix.TransvectionStruct (Fin n) ℂ) :
    PairFixesCenter t.toMatrix := by
  obtain ⟨i, j, hij, c⟩ := t
  set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single j j 1 with hE
  set F : Matrix (Fin n) (Fin n) ℂ := Matrix.single i j 1 with hF
  have hEE : E * E = E := by simp [E]
  have hEF : E * F = 0 := Matrix.single_mul_single_of_ne (1 : ℂ) j j i (Ne.symm hij) 1
  have hFE : F * E = F := by simp [E, F]
  have hFF : F * F = 0 := Matrix.single_mul_single_of_ne (1 : ℂ) i j i (Ne.symm hij) 1
  set Q : Matrix (Fin n) (Fin n) ℂ := E - (c / 2) • F with hQdef
  have hQ : Q * Q = Q := by
    simp only [Q, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hEE, hEF, hFE, hFF, smul_zero]
    module
  have ht : Matrix.TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ =
      (1 + ((-1 : ℂ) - 1) • E) * (1 + ((-1 : ℂ) - 1) • Q) := by
    rw [Matrix.TransvectionStruct.toMatrix_mk, Matrix.transvection]
    have : Matrix.single i j c = c • F := by simp [F, Matrix.smul_single]
    rw [this]
    simp only [Q, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, mul_sub,
      smul_sub, hEE, hEF, smul_zero]
    module
  rw [ht]
  exact pairFixesCenter_mul (det_ne_zero_of_idempotent hEE (by norm_num))
    (pairFixesCenter_idempotent hEE (by norm_num)) (pairFixesCenter_idempotent hQ (by norm_num))

/-- For every invertible complex matrix `X`, conjugation by `(X, X̄)` fixes the center of
`U(𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ))`. -/
theorem pairFixesCenter_of_det_ne_zero (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.det ≠ 0) :
    PairFixesCenter X :=
  Matrix.diagonal_transvection_induction_of_det_ne_zero _ X hX
    (fun D hD => pairFixesCenter_diagonal D fun i => by
      rw [Matrix.det_diagonal] at hD
      exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ _))
    pairFixesCenter_transvection (fun _ _ hA _ hAf hBf => pairFixesCenter_mul hA hAf hBf)

end Matrices

/-! ## Compatibility of the `U(n)`-action with the action of the product -/

section Compat

variable {n : ℕ}

/-- The unit `(k, k̄)` of `M_n(ℂ) × M_n(ℂ)` attached to `k ∈ U(n)`. -/
def pairUnit (k : Matrix.unitaryGroup (Fin n) ℂ) : (Fin 2 → Matrix (Fin n) (Fin n) ℂ)ˣ :=
  Units.map (pairHom : Matrix (Fin n) (Fin n) ℂ →ₐ[ℝ] (Fin 2 → Matrix (Fin n) (Fin n) ℂ)).toMonoidHom
    (Unitary.toUnits k)

theorem pairUnit_val (k : Matrix.unitaryGroup (Fin n) ℂ) :
    (pairUnit k : Fin 2 → Matrix (Fin n) (Fin n) ℂ) = pairHom (k : Matrix (Fin n) (Fin n) ℂ) :=
  rfl

theorem pairUnit_inv_val (k : Matrix.unitaryGroup (Fin n) ℂ) :
    (((pairUnit k)⁻¹ : (Fin 2 → Matrix (Fin n) (Fin n) ℂ)ˣ) : Fin 2 → Matrix (Fin n) (Fin n) ℂ) =
      pairHom (star (k : Matrix (Fin n) (Fin n) ℂ)) := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [pairUnit_val, ← map_mul, Unitary.mul_star_self_of_mem k.2, map_one]

theorem det_ne_zero_of_unitary (k : Matrix.unitaryGroup (Fin n) ℂ) :
    (k : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 :=
  (Matrix.isUnit_det_of_right_inverse (Unitary.mul_star_self_of_mem k.2)).ne_zero

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The action `π ∘ tensorLieEquiv⁻¹` of `𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)` attached to an action `π` of
`ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`. -/
abbrev prodAction (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V) :
    (Fin 2 → Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V :=
  π.comp tensorLieEquiv.symm.toLieHom

theorem prodAction_apply (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) : prodAction π Y = π (tensorEquiv.symm Y) :=
  rfl

variable {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- `ρ(k) π(x) = π((1 ⊗ k) x (1 ⊗ k*)) ρ(k)` for all `x ∈ ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`. -/
theorem rho_mul_pi
    (h4 : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (v : V),
      ρ k (π (1 ⊗ₜ X) v) =
        π (1 ⊗ₜ ((k : Matrix (Fin n) (Fin n) ℂ) * X * (star k : Matrix (Fin n) (Fin n) ℂ)))
          (ρ k v))
    (k : Matrix.unitaryGroup (Fin n) ℂ) (x : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    ρ k * π x = π (((1 : ℂ) ⊗ₜ[ℝ] (k : Matrix (Fin n) (Fin n) ℂ)) * x *
      ((1 : ℂ) ⊗ₜ[ℝ] star (k : Matrix (Fin n) (Fin n) ℂ))) * ρ k := by
  induction x using TensorProduct.inductionOn with
  | tmul a X =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one]
    have hx : ∀ Y : Matrix (Fin n) (Fin n) ℂ,
        a ⊗ₜ[ℝ] Y = a • (1 ⊗ₜ[ℝ] Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) := by
      intro Y; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    ext v
    rw [hx X, hx, map_smul, map_smul]
    simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul, h4]
  | add x y hx hy =>
    simp only [map_add, mul_add, add_mul, hx, hy]

/-- `ρ(k) πB(u) = πB(Ad(k, k̄) u) ρ(k)` for all `u ∈ U(𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ))`. -/
theorem rho_mul_envelopingAction_prod
    (h4 : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (v : V),
      ρ k (π (1 ⊗ₜ X) v) =
        π (1 ⊗ₜ ((k : Matrix (Fin n) (Fin n) ℂ) * X * (star k : Matrix (Fin n) (Fin n) ℂ)))
          (ρ k v))
    (k : Matrix.unitaryGroup (Fin n) ℂ)
    (u : UniversalEnvelopingAlgebra ℂ (Fin 2 → Matrix (Fin n) (Fin n) ℂ)) :
    ρ k * envelopingAction (prodAction π) u =
      envelopingAction (prodAction π) (envMap (conjLieB (pairUnit k)) u) * ρ k := by
  induction u using envInduction with
  | algebraMap r =>
    simp only [AlgHom.commutes]
    exact (Algebra.commutes r (ρ k)).symm
  | ι Y =>
    rw [envMap_ι, conjLieB_apply, envelopingAction, UniversalEnvelopingAlgebra.lift_ι_apply,
      UniversalEnvelopingAlgebra.lift_ι_apply, prodAction_apply, prodAction_apply, pairUnit_val,
      pairUnit_inv_val, map_mul tensorEquiv.symm, map_mul tensorEquiv.symm, tensorEquiv_symm_pairHom,
      tensorEquiv_symm_pairHom]
    exact rho_mul_pi h4 k _
  | mul a b ha hb =>
    simp only [map_mul]
    rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
  | add a b ha hb =>
    simp only [map_add, mul_add, add_mul, ha, hb]

end Compat

/-! ## The infinitesimal character -/

section InfChar

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- **The product action of an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module has an
infinitesimal character.** A central element `z` of `U(𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ))` acts by an
operator `Z` commuting with `π` (as `z` is central) and with `ρ` (as `Ad(k, k̄)` fixes `z`). By
admissibility `Z` has an eigenvector; its eigenspace is a nonzero `(𝔤, K)`-submodule, hence
everything by irreducibility. -/
theorem prodAction_hasInfinitesimalCharacter (hgk : IsComplexGKModule n ρ π)
    (hirr : IsIrreducibleGKModule ρ π) (hadm : IsAdmissibleGKModule ρ) :
    HasInfinitesimalCharacter (prodAction π) := by
  intro z hz
  set Z := envelopingAction (prodAction π) z with hZdef
  have hZπ : ∀ x, π x * Z = Z * π x := by
    intro x
    have h := congrArg (envelopingAction (prodAction π))
      ((Subalgebra.mem_center_iff.1 hz) (UniversalEnvelopingAlgebra.ι ℂ (tensorEquiv x)))
    rwa [map_mul, map_mul, envelopingAction, UniversalEnvelopingAlgebra.lift_ι_apply,
      prodAction_apply, AlgEquiv.symm_apply_apply] at h
  have hZρ : ∀ k, ρ k * Z = Z * ρ k := by
    intro k
    rw [hZdef, rho_mul_envelopingAction_prod hgk.2.2.2 k z,
      pairFixesCenter_of_det_ne_zero _ (det_ne_zero_of_unitary k) (pairUnit k) (pairUnit_val k)
        z hz]
  have := hirr.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨c, x, hx, hZx⟩ := exists_eigenvector_of_commute ρ hgk.1 hgk.2.1 hadm Z hZρ hv
  refine ⟨c, ?_⟩
  set E := LinearMap.ker (Z - algebraMap ℂ (Module.End ℂ V) c) with hE
  have hmem : ∀ w, w ∈ E ↔ Z w = c • w := by
    intro w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero]
  have htop : E = ⊤ := by
    refine (hirr.2 E (fun k w hw => ?_) (fun X w hw => ?_)).resolve_left fun hbot => hx ?_
    · rw [hmem] at hw ⊢
      rw [← Module.End.mul_apply, ← hZρ k, Module.End.mul_apply, hw, map_smul]
    · rw [hmem] at hw ⊢
      rw [← Module.End.mul_apply, ← hZπ X, Module.End.mul_apply, hw, map_smul]
    · have : x ∈ E := (hmem x).2 hZx
      rw [hbot] at this
      exact (Submodule.mem_bot ℂ).1 this
  refine LinearMap.ext fun w => ?_
  rw [Module.algebraMap_end_apply]
  exact (hmem w).1 (by rw [htop]; exact Submodule.mem_top)

end InfChar

/-! ## The Whittaker vector for the product action -/

section Whittaker

variable {n : ℕ}

/-- `S_a(X) = ∑ₚ a_p X_{p,p+1}`. -/
def whitSum (a : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ p : Fin n, ∑ q : Fin n, if (q : ℕ) = p + 1 then a p * X p q else 0

theorem whitSum_smul (a : Fin n → ℂ) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    whitSum a (c • X) = c * whitSum a X := by
  simp only [whitSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem whitSum_conj (a : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    whitSum a (conjMat X) = starRingEnd ℂ (whitSum (fun p => starRingEnd ℂ (a p)) X) := by
  simp only [whitSum, map_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [conjMat_apply]
  split_ifs <;> simp

theorem whitSum_const_mul (a : Fin n → ℂ) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    whitSum (fun p => c * a p) X = c * whitSum a X := by
  simp only [whitSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> ring

theorem smul_strictUpper {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) (c : ℂ) :
    ∀ i j : Fin n, (j : ℕ) ≤ i → (c • X) i j = 0 := fun i j h => by
  rw [Matrix.smul_apply, hX i j h, smul_zero]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- If `ℓ(π(1 ⊗ X) v) = i Re(S_a(X)) ℓ(v)` for strictly upper triangular `X`, then for
blockwise strictly upper triangular `(Y₀, Y₁)`,
`ℓ(πB(Y₀, Y₁) v) = ((i/2) S_a(Y₀) + (i/2) S_ā(Y₁)) ℓ(v)`. -/
theorem prodAction_whittaker (ℓ : V →ₗ[ℂ] ℂ) (a : Fin n → ℂ)
    (hw : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) →
      ∀ v : V, ℓ (π (1 ⊗ₜ X) v) = (Complex.I * (((whitSum a X).re : ℝ) : ℂ)) * ℓ v)
    (Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ (i : Fin 2) (p q : Fin n), (q : ℕ) ≤ p → Y i p q = 0) (v : V) :
    ℓ (prodAction π Y v) = (Complex.I / 2 * whitSum a (Y 0) +
      Complex.I / 2 * whitSum (fun p => starRingEnd ℂ (a p)) (Y 1)) * ℓ v := by
  have h0 : ∀ i j : Fin n, (j : ℕ) ≤ i → Y 0 i j = 0 := hY 0
  have h1 : ∀ i j : Fin n, (j : ℕ) ≤ i → conjMat (Y 1) i j = 0 := fun i j h => by
    rw [conjMat_apply, hY 1 i j h, map_zero]
  rw [prodAction_apply, tensorEquiv_symm_apply, tensorInv]
  simp only [map_smul, map_add, map_sub, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply]
  rw [hw _ h0, hw _ (smul_strictUpper h0 _), hw _ h1, hw _ (smul_strictUpper h1 _),
    whitSum_smul, whitSum_smul, whitSum_conj]
  set s0 := whitSum a (Y 0)
  set s1 := whitSum (fun p => starRingEnd ℂ (a p)) (Y 1)
  have key : (1 / 2 : ℂ) * (Complex.I * ((s0.re : ℝ) : ℂ) -
      Complex.I * (Complex.I * (((Complex.I * s0).re : ℝ) : ℂ)) +
      Complex.I * (((starRingEnd ℂ s1).re : ℝ) : ℂ) +
      Complex.I * (Complex.I * (((Complex.I * starRingEnd ℂ s1).re : ℝ) : ℂ))) =
      Complex.I / 2 * s0 + Complex.I / 2 * s1 := by
    apply Complex.ext <;> simp <;> ring
  rw [← key]
  simp only [smul_eq_mul]
  ring

end Whittaker

/-! ## The reduction -/

/-- **Reduction of `ComplexGenericLargeStatement` to Kostant's theorem for
`𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`.** Kostant's theorem for finite products of `𝔤𝔩_n(ℂ)`
(`GLProductWhittakerMaximallyFaithfulStatement`) implies that every irreducible admissible
generic `(𝔤𝔩_n(ℂ), U(n))`-module is large. -/
def ComplexGenericLargeReductionStatement : Prop :=
  GLProductWhittakerMaximallyFaithfulStatement.{uV} → ComplexGenericLargeStatement.{uV}

/-- Proof of the reduction: transport `π` along `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ) ≅ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`, prove the
infinitesimal character and the Whittaker identity (coefficients `(i/2) a_p` and `(i/2) ā_p`)
on the product, apply Kostant's theorem there and transport maximal faithfulness back. -/
theorem complexGenericLargeReduction : ComplexGenericLargeReductionStatement.{uV} := by
  intro hK n V _ _ ρ π hgk hirr hadm hgen
  obtain ⟨ℓ, hℓ, a, ha, hw⟩ := hgen
  have hinf := prodAction_hasInfinitesimalCharacter hgk hirr hadm
  let a' : ∀ i : Fin 2, Fin ((fun _ : Fin 2 => n) i) → ℂ :=
    ![fun p => Complex.I / 2 * a p, fun p => Complex.I / 2 * starRingEnd ℂ (a p)]
  have hI : Complex.I / 2 ≠ 0 := div_ne_zero Complex.I_ne_zero two_ne_zero
  have ha' : ∀ (i : Fin 2) (p : Fin ((fun _ : Fin 2 => n) i)),
      (p : ℕ) + 1 < (fun _ : Fin 2 => n) i → a' i p ≠ 0 := by
    intro i p hp
    fin_cases i
    · exact mul_ne_zero hI (ha p hp)
    · exact mul_ne_zero hI ((map_ne_zero _).2 (ha p hp))
  have hw' : ∀ X : Fin 2 → Matrix (Fin n) (Fin n) ℂ,
      (∀ (i : Fin 2) (p q : Fin n), (q : ℕ) ≤ p → X i p q = 0) → ∀ v : V,
        ℓ (prodAction π X v) = (∑ i : Fin 2, ∑ p : Fin n, ∑ q : Fin n,
          if (q : ℕ) = p + 1 then a' i p * X i p q else 0) * ℓ v := by
    intro X hX v
    rw [prodAction_whittaker ℓ a hw X hX v, Fin.sum_univ_two]
    show _ = (whitSum (fun p => Complex.I / 2 * a p) (X 0) +
      whitSum (fun p => Complex.I / 2 * starRingEnd ℂ (a p)) (X 1)) * ℓ v
    rw [whitSum_const_mul, whitSum_const_mul]
  exact isMaximallyFaithful_of_comp tensorLieEquiv π
    (hK (Fin 2) (fun _ => n) V (prodAction π) hinf ℓ hℓ a' ha' hw')

end ComplexGenericLarge

end Langlands.Archimedean
