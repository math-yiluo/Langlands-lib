import Mathlib

/-! # Fibres of polynomial extensions -/

namespace Langlands.CommutativeAlgebra.FiniteTypeIntGRing

open MvPolynomial TensorProduct

attribute [local instance] RingHom.ker_isPrime

section Residue

variable {P : Type*} [CommRing P] {K : Type*} [Field K] (ψ : P →+* K)

/-- The residue field of `P` at `ker ψ` maps to `K`. -/
noncomputable def residueFieldKerLift : (RingHom.ker ψ).ResidueField →+* K :=
  Ideal.ResidueField.lift _ ψ le_rfl fun x hx => by
    rw [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    exact fun h => (Ideal.mem_primeCompl_iff.mp hx) (RingHom.mem_ker.mpr h)

theorem residueFieldKerLift_algebraMap (p : P) :
    residueFieldKerLift ψ (algebraMap P _ p) = ψ p :=
  Ideal.ResidueField.lift_algebraMap _ _ _ _ _

theorem residueFieldKerLift_bijective (hψ : ∀ z : K, ∃ u v, ψ v ≠ 0 ∧ z = ψ u / ψ v) :
    Function.Bijective (residueFieldKerLift ψ) := by
  refine ⟨RingHom.injective _, fun z => ?_⟩
  obtain ⟨u, v, -, rfl⟩ := hψ z
  exact ⟨algebraMap P _ u / algebraMap P _ v, by
    rw [map_div₀, residueFieldKerLift_algebraMap, residueFieldKerLift_algebraMap]⟩

/-- If every element of the field `K` is a quotient of values of `ψ : P → K`, then the residue
field of `P` at `ker ψ` is identified with `K`. -/
noncomputable def residueFieldKerEquiv (hψ : ∀ z : K, ∃ u v, ψ v ≠ 0 ∧ z = ψ u / ψ v) :
    (RingHom.ker ψ).ResidueField ≃+* K :=
  RingEquiv.ofBijective (residueFieldKerLift ψ) (residueFieldKerLift_bijective ψ hψ)

@[simp]
theorem residueFieldKerEquiv_algebraMap (hψ : ∀ z : K, ∃ u v, ψ v ≠ 0 ∧ z = ψ u / ψ v) (p : P) :
    residueFieldKerEquiv ψ hψ (algebraMap P _ p) = ψ p := by
  rw [residueFieldKerEquiv, RingEquiv.ofBijective_apply, residueFieldKerLift_algebraMap]

@[simp]
theorem residueFieldKerEquiv_symm_apply (hψ : ∀ z : K, ∃ u v, ψ v ≠ 0 ∧ z = ψ u / ψ v) (p : P) :
    (residueFieldKerEquiv ψ hψ).symm (ψ p) = algebraMap P _ p := by
  rw [RingEquiv.symm_apply_eq, residueFieldKerEquiv_algebraMap]

end Residue

section Fiber

variable {R₀ : Type*} [CommRing R₀] {σ μ : Type*}
  {A₀ : Type*} [CommRing A₀] [Algebra (MvPolynomial σ R₀) A₀]
  {B₀ : Type*} [CommRing B₀] [Algebra A₀ B₀]
  {K : Type*} [Field K] [Algebra A₀ K]
  [Algebra (MvPolynomial (σ ⊕ μ) R₀) (MvPolynomial μ B₀)]
  (ψ : MvPolynomial (σ ⊕ μ) R₀ →+* K)
  (hψ : ∀ p, ψ (rename Sum.inl p) = algebraMap A₀ K (algebraMap _ A₀ p))
  (hB₁ : ∀ p, algebraMap (MvPolynomial (σ ⊕ μ) R₀) (MvPolynomial μ B₀) (rename Sum.inl p) =
    C (algebraMap A₀ B₀ (algebraMap _ A₀ p)))
  (hB₂ : ∀ j, algebraMap (MvPolynomial (σ ⊕ μ) R₀) (MvPolynomial μ B₀) (X (Sum.inr j)) = X j)
  (hsurj : ∀ z : K, ∃ u v, ψ v ≠ 0 ∧ z = ψ u / ψ v)

variable (A₀ B₀) in
/-- The map `B₀[Y_μ] → K ⊗[A₀] B₀` sending `Y_j` to `ψ(Y_j) ⊗ 1`. -/
noncomputable abbrev polyToTensor : MvPolynomial μ B₀ →+* K ⊗[A₀] B₀ :=
  eval₂Hom (Algebra.TensorProduct.includeRight : B₀ →ₐ[A₀] K ⊗[A₀] B₀).toRingHom
    fun j => ψ (X (Sum.inr j)) ⊗ₜ 1

include hψ hB₁ hB₂ in
theorem polyToTensor_algebraMap (p : MvPolynomial (σ ⊕ μ) R₀) :
    polyToTensor A₀ B₀ ψ (algebraMap _ (MvPolynomial μ B₀) p) = ψ p ⊗ₜ 1 := by
  have key : ∀ q, polyToTensor A₀ B₀ ψ (algebraMap _ (MvPolynomial μ B₀) (rename Sum.inl q)) =
      ψ (rename Sum.inl q) ⊗ₜ 1 := fun q => by
    rw [hB₁, hψ, eval₂Hom_C]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm
  have : (polyToTensor A₀ B₀ ψ).comp (algebraMap _ (MvPolynomial μ B₀)) =
      Algebra.TensorProduct.includeLeftRingHom.comp ψ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
    · simpa using key (C r)
    · rcases v with i | j
      · simpa using key (X i)
      · simp [hB₂]
  exact RingHom.congr_fun this p

include hψ hB₁ hB₂ hsurj in
/-- The forward map `κ(ker ψ) ⊗ B₀[Y_μ] → K ⊗[A₀] B₀`. -/
noncomputable def fiberToTensor :
    (RingHom.ker ψ).Fiber (MvPolynomial μ B₀) →+* K ⊗[A₀] B₀ :=
  letI : Algebra (MvPolynomial (σ ⊕ μ) R₀) (K ⊗[A₀] B₀) :=
    (Algebra.TensorProduct.includeLeftRingHom.comp ψ).toAlgebra
  (Algebra.TensorProduct.lift (S := MvPolynomial (σ ⊕ μ) R₀)
    { toRingHom := Algebra.TensorProduct.includeLeftRingHom.comp
        (residueFieldKerEquiv ψ hsurj).toRingHom
      commutes' := fun p => by simp [RingHom.algebraMap_toAlgebra] }
    { toRingHom := polyToTensor A₀ B₀ ψ
      commutes' := fun p => by
        rw [RingHom.algebraMap_toAlgebra]
        exact polyToTensor_algebraMap ψ hψ hB₁ hB₂ p }
    fun _ _ => Commute.all _ _).toRingHom

theorem fiberToTensor_tmul (c : (RingHom.ker ψ).ResidueField) (f : MvPolynomial μ B₀) :
    fiberToTensor ψ hψ hB₁ hB₂ hsurj (c ⊗ₜ f) =
      (residueFieldKerEquiv ψ hsurj c ⊗ₜ 1) * polyToTensor A₀ B₀ ψ f := by
  simp [fiberToTensor]

variable (M : Submonoid (MvPolynomial σ R₀)) [IsLocalization M A₀]

include hψ hB₁ hsurj M in
/-- The inverse map `K ⊗[A₀] B₀ → κ(ker ψ) ⊗ B₀[Y_μ]`. -/
noncomputable def tensorToFiber :
    K ⊗[A₀] B₀ →+* (RingHom.ker ψ).Fiber (MvPolynomial μ B₀) :=
  letI : Algebra A₀ ((RingHom.ker ψ).Fiber (MvPolynomial μ B₀)) :=
    (Algebra.TensorProduct.includeLeftRingHom.comp
      ((residueFieldKerEquiv ψ hsurj).symm.toRingHom.comp (algebraMap A₀ K))).toAlgebra
  (Algebra.TensorProduct.lift (S := A₀)
    { toRingHom := Algebra.TensorProduct.includeLeftRingHom.comp
        (residueFieldKerEquiv ψ hsurj).symm.toRingHom
      commutes' := fun _ => rfl }
    { toRingHom := (Algebra.TensorProduct.includeRight (R := MvPolynomial (σ ⊕ μ) R₀)
          (A := (RingHom.ker ψ).ResidueField) (B := MvPolynomial μ B₀)).toRingHom.comp C
      commutes' := fun a => by
        rw [RingHom.algebraMap_toAlgebra]
        have : ((Algebra.TensorProduct.includeRight (R := MvPolynomial (σ ⊕ μ) R₀)
            (A := (RingHom.ker ψ).ResidueField) (B := MvPolynomial μ B₀)).toRingHom.comp
              C).comp (algebraMap A₀ B₀) =
            Algebra.TensorProduct.includeLeftRingHom.comp
              ((residueFieldKerEquiv ψ hsurj).symm.toRingHom.comp (algebraMap A₀ K)) := by
          refine IsLocalization.ringHom_ext M (RingHom.ext fun p => ?_)
          simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
          rw [← hψ p, residueFieldKerEquiv_symm_apply, ← hB₁ p]
          simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.includeLeftRingHom_apply]
          exact (Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm
        exact RingHom.congr_fun this a }
    fun _ _ => Commute.all _ _).toRingHom

theorem tensorToFiber_tmul (k : K) (b : B₀) :
    tensorToFiber ψ hψ hB₁ hsurj M (k ⊗ₜ b) =
      (residueFieldKerEquiv ψ hsurj).symm k ⊗ₜ C b := by
  let : Algebra A₀ ((RingHom.ker ψ).Fiber (MvPolynomial μ B₀)) :=
    (Algebra.TensorProduct.includeLeftRingHom.comp
      ((residueFieldKerEquiv ψ hsurj).symm.toRingHom.comp (algebraMap A₀ K))).toAlgebra
  simp only [tensorToFiber, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  erw [Algebra.TensorProduct.lift_tmul]
  change ((residueFieldKerEquiv ψ hsurj).symm k ⊗ₜ 1) * (1 ⊗ₜ C b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- **Fibres of polynomial extensions.** Let `A₀` be a localization of `R₀[X_σ]`, `B₀` an
`A₀`-algebra, `K` a field which is an `A₀`-algebra, and `ψ : R₀[X_σ, Y_μ] → K` a ring map extending
`R₀[X_σ] → A₀ → K` such that every element of `K` is a quotient of values of `ψ`. Make `B₀[Y_μ]` an
`R₀[X_σ, Y_μ]`-algebra by `X_i ↦ X_i`, `Y_j ↦ Y_j`. Then the fibre of `B₀[Y_μ]` over `ker ψ` is
isomorphic to `K ⊗[A₀] B₀`. -/
noncomputable def fiberEquivTensor :
    (RingHom.ker ψ).Fiber (MvPolynomial μ B₀) ≃+* K ⊗[A₀] B₀ :=
  RingEquiv.ofRingHom (fiberToTensor ψ hψ hB₁ hB₂ hsurj) (tensorToFiber ψ hψ hB₁ hsurj M)
    (RingHom.ext fun x => by
      induction x using TensorProduct.inductionOn with
      | tmul k b =>
        rw [RingHom.comp_apply, tensorToFiber_tmul, fiberToTensor_tmul]
        simp
      | add x y hx hy => simp_all)
    (RingHom.ext fun x => by
      induction x using TensorProduct.inductionOn with
      | tmul c f =>
        have hpoly : (tensorToFiber ψ hψ hB₁ hsurj M).comp (polyToTensor A₀ B₀ ψ) =
            (Algebra.TensorProduct.includeRight (R := MvPolynomial (σ ⊕ μ) R₀)
              (A := (RingHom.ker ψ).ResidueField) (B := MvPolynomial μ B₀)).toRingHom := by
          refine MvPolynomial.ringHom_ext (fun b => ?_) (fun j => ?_)
          · simp [tensorToFiber_tmul]
          · simp only [RingHom.comp_apply, eval₂Hom_X', tensorToFiber_tmul,
              residueFieldKerEquiv_symm_apply, map_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
              Algebra.TensorProduct.includeRight_apply]
            rw [← hB₂ j]
            exact Algebra.TensorProduct.tmul_one_eq_one_tmul _
        have hf := RingHom.congr_fun hpoly f
        rw [RingHom.comp_apply] at hf
        rw [RingHom.comp_apply, fiberToTensor_tmul, map_mul, tensorToFiber_tmul, hf]
        simp
      | add x y hx hy => simp_all)

theorem fiberEquivTensor_tmul (c : (RingHom.ker ψ).ResidueField) (f : MvPolynomial μ B₀) :
    fiberEquivTensor ψ hψ hB₁ hB₂ hsurj M (c ⊗ₜ f) =
      (residueFieldKerEquiv ψ hsurj c ⊗ₜ 1) * polyToTensor A₀ B₀ ψ f :=
  fiberToTensor_tmul ψ hψ hB₁ hB₂ hsurj c f

end Fiber

end Langlands.CommutativeAlgebra.FiniteTypeIntGRing
