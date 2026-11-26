import Langlands.AlgebraicGeometry.SmoothThickeningLiftingProof
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Lifting and rigidity along nilpotent thickenings of affine schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AffineNilpotentThickening

section Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- An `R`-linear endomorphism congruent to the identity modulo a nilpotent ideal of `R` is
bijective. -/
theorem bijective_of_sub_mem (I : Ideal R) (hI : IsNilpotent I) (φ : A →ₗ[R] A)
    (h : ∀ a, φ a - a ∈ I.map (algebraMap R A)) : Function.Bijective φ := by
  let δ : Module.End R A := φ - LinearMap.id
  have hδ : ∀ n : ℕ, ∀ a ∈ I ^ n • (⊤ : Submodule R A), δ a ∈ I ^ (n + 1) • (⊤ : Submodule R A) := by
    intro n a ha
    refine Submodule.smul_induction_on ha (fun r hr x _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [LinearMap.map_smul, pow_succ, mul_smul]
      refine Submodule.smul_mem_smul hr ?_
      have : φ x - x ∈ I • (⊤ : Submodule R A) := by
        rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
        exact h x
      simpa [δ] using this
    · rw [map_add]
      exact Submodule.add_mem _ hx hy
  have hpow : ∀ n : ℕ, ∀ a : A, (δ ^ n) a ∈ I ^ n • (⊤ : Submodule R A) := by
    intro n
    induction n with
    | zero =>
      intro a
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      trivial
    | succ n ih =>
      intro a
      rw [pow_succ' δ n, Module.End.mul_apply]
      exact hδ n _ (ih a)
  obtain ⟨N, hN⟩ := hI
  have hnil : IsNilpotent δ := by
    refine ⟨N, LinearMap.ext fun a ↦ ?_⟩
    have := hpow N a
    rw [hN, Submodule.zero_eq_bot, Submodule.bot_smul] at this
    simpa using this
  have hunit : IsUnit (1 + δ) := hnil.isUnit_one_add
  have hφ : φ = 1 + δ := by
    ext a
    simp [δ]
  rw [hφ]
  exact (Module.End.isUnit_iff _).mp hunit

end Algebra

section Spec

variable {R R₀ : Type u} [CommRing R] [CommRing R₀] [Algebra R R₀]

/-- The kernel of `A → A ⊗[R] R₀` lies in the extension of the kernel of `R → R₀`. -/
theorem ker_includeLeft_le (hsurj : Function.Surjective (algebraMap R R₀))
    (A : Type u) [CommRing A] [Algebra R A] :
    RingHom.ker (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R₀) ≤
      (RingHom.ker (algebraMap R R₀)).map (algebraMap R A) := by
  intro x hx
  let K := RingHom.ker (Algebra.ofId R R₀)
  let f : R₀ →ₐ[R] R ⧸ K := (Ideal.quotientKerAlgEquivOfSurjective
    (f := Algebra.ofId R R₀) hsurj).symm.toAlgHom
  let g : A ⊗[R] R₀ →ₐ[R] A ⊗[R] (R ⧸ K) := Algebra.TensorProduct.map (AlgHom.id R A) f
  have h₁ : g (x ⊗ₜ[R] 1) = x ⊗ₜ[R] 1 := by
    simp [g]
  have h₂ : x ⊗ₜ[R] (1 : R₀) = 0 := hx
  have h₃ : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A K).symm (x ⊗ₜ[R] 1) = 0 := by
    rw [← h₁, h₂, map_zero, map_zero]
  rw [← map_one (Ideal.Quotient.mk K), Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul,
    one_smul] at h₃
  exact (Submodule.Quotient.mk_eq_zero _).mp h₃

theorem isNilpotent_ker_includeLeft (hsurj : Function.Surjective (algebraMap R R₀))
    (hnil : IsNilpotent (RingHom.ker (algebraMap R R₀))) (A : Type u) [CommRing A] [Algebra R A] :
    IsNilpotent (RingHom.ker (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R₀)) := by
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, eq_bot_iff.mpr ?_⟩
  calc RingHom.ker (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R₀) ^ n
      ≤ ((RingHom.ker (algebraMap R R₀)).map (algebraMap R A)) ^ n :=
        Ideal.pow_right_mono (ker_includeLeft_le hsurj A) n
    _ = ((RingHom.ker (algebraMap R R₀)) ^ n).map (algebraMap R A) := (Ideal.map_pow _ _ _).symm
    _ = ⊥ := by rw [hn, Ideal.zero_eq_bot, Ideal.map_bot]

/-- An endomorphism of `Spec A` over `Spec R` that restricts to the identity on the closed
subscheme `Spec (A ⊗[R] R₀)` is an isomorphism, when `R → R₀` is surjective with nilpotent
kernel. -/
theorem isIso_of_restrict_eq (hsurj : Function.Surjective (algebraMap R R₀))
    (hnil : IsNilpotent (RingHom.ker (algebraMap R R₀))) (A : Type u) [CommRing A] [Algebra R A]
    (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hb : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R₀)) ≫ g =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) :
    IsIso g := by
  rw [← Spec.map_preimage g] at hg hb ⊢
  set φ := Spec.preimage g
  rw [← Spec.map_comp, Spec.map_inj] at hg hb
  let φ' : A →ₐ[R] A :=
    { toRingHom := φ.hom
      commutes' := fun r ↦ congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of A ↦ f.hom r) hg }
  have hbij : Function.Bijective φ' := by
    refine bijective_of_sub_mem _ hnil φ'.toLinearMap fun a ↦ ?_
    apply ker_includeLeft_le (R₀ := R₀) (by exact hsurj) A
    rw [RingHom.mem_ker, map_sub]
    have := congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of (A ⊗[R] R₀) ↦ f.hom a) hb
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    change Algebra.TensorProduct.includeLeftRingHom (φ.hom a) -
      Algebra.TensorProduct.includeLeftRingHom a = 0
    rw [this, sub_self]
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr hbij
  infer_instance

end Spec

section Scheme

variable {R R₀ : Type u} [CommRing R] [CommRing R₀] [Algebra R R₀]

local notation "S" => Spec (CommRingCat.of R)
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap R R₀))

/-- The algebra structure on the global sections of an affine scheme over `Spec R`. -/
@[instance_reducible]
def globalAlgebra {U : Scheme.{u}} [IsAffine U] (p : U ⟶ S) : Algebra R Γ(U, ⊤) :=
  (Spec.preimage (U.isoSpec.inv ≫ p)).hom.toAlgebra

theorem specMap_globalAlgebra {U : Scheme.{u}} [IsAffine U] (p : U ⟶ S) :
    letI := globalAlgebra p
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(U, ⊤))) = U.isoSpec.inv ≫ p :=
  Spec.map_preimage _

/-- The fibre of an affine scheme over `Spec R₀`, as the spectrum of a tensor product. -/
theorem exists_fibreIso {U W : Scheme.{u}} [IsAffine U] (p : U ⟶ S) (a : W ⟶ U)
    (w : W ⟶ Spec (CommRingCat.of R₀)) (hW : IsPullback a w p c) :
    letI := globalAlgebra p
    ∃ e : W ≅ Spec (CommRingCat.of (Γ(U, ⊤) ⊗[R] R₀)),
      e.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : Γ(U, ⊤) →+* Γ(U, ⊤) ⊗[R] R₀)) ≫
          U.isoSpec.inv = a := by
  let := globalAlgebra p
  have h₀ := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R Γ(U, ⊤) R₀)
  have h₁ : IsPullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : Γ(U, ⊤) →+* Γ(U, ⊤) ⊗[R] R₀)) ≫ U.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        R₀ →+* Γ(U, ⊤) ⊗[R] R₀))) p c := by
    refine IsPullback.of_iso h₀ (Iso.refl _) U.isoSpec.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [specMap_globalAlgebra]
    · simp
  exact ⟨hW.isoIsPullback _ _ h₁, hW.isoIsPullback_hom_fst _ _ h₁⟩

/-- Lifting along the fibre of an affine scheme into a smooth scheme. -/
theorem exists_lift (hsurj : Function.Surjective (algebraMap R R₀))
    (hnil : IsNilpotent (RingHom.ker (algebraMap R R₀)))
    {U W Z : Scheme.{u}} [IsAffine U] (p : U ⟶ S) (a : W ⟶ U)
    (w : W ⟶ Spec (CommRingCat.of R₀)) (hW : IsPullback a w p c) (f : Z ⟶ S) [Smooth f]
    (z : W ⟶ Z) (hz : z ≫ f = a ≫ p) :
    ∃ y : U ⟶ Z, y ≫ f = p ∧ a ≫ y = z := by
  let := globalAlgebra p
  obtain ⟨e, he⟩ := exists_fibreIso p a w hW
  let q : CommRingCat.of Γ(U, ⊤) ⟶ CommRingCat.of (Γ(U, ⊤) ⊗[R] R₀) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  have hq : Function.Surjective q.hom :=
    Algebra.TensorProduct.includeLeft_surjective (R := R) R Γ(U, ⊤) hsurj
  have hqn : IsNilpotent (RingHom.ker q.hom) := isNilpotent_ker_includeLeft hsurj hnil _
  have he' : e.inv ≫ a = Spec.map q ≫ U.isoSpec.inv := by
    rw [Iso.inv_comp_eq, ← he]
  obtain ⟨x, hx₁, hx₂⟩ := smoothThickeningLifting f q hq hqn (e.inv ≫ z) (U.isoSpec.inv ≫ p) (by
    rw [Category.assoc, hz, ← Category.assoc, he', Category.assoc])
  refine ⟨U.isoSpec.hom ≫ x, by rw [Category.assoc, hx₂, Iso.hom_inv_id_assoc], ?_⟩
  rw [← he]
  change e.hom ≫ Spec.map q ≫ U.isoSpec.inv ≫ U.isoSpec.hom ≫ x = z
  rw [Iso.inv_hom_id_assoc, hx₁, Iso.hom_inv_id_assoc]

/-- An endomorphism of an affine scheme over `Spec R` that is the identity on the fibre over
`Spec R₀` is an isomorphism. -/
theorem isIso_of_fibre (hsurj : Function.Surjective (algebraMap R R₀))
    (hnil : IsNilpotent (RingHom.ker (algebraMap R R₀)))
    {U W : Scheme.{u}} [IsAffine U] (p : U ⟶ S) (a : W ⟶ U)
    (w : W ⟶ Spec (CommRingCat.of R₀)) (hW : IsPullback a w p c) (g : U ⟶ U)
    (hg : g ≫ p = p) (hag : a ≫ g = a) : IsIso g := by
  let := globalAlgebra p
  obtain ⟨e, he⟩ := exists_fibreIso p a w hW
  have he' : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : Γ(U, ⊤) →+* Γ(U, ⊤) ⊗[R] R₀)) ≫
        U.isoSpec.inv = e.inv ≫ a := by
    rw [Iso.eq_inv_comp, he]
  have h' : IsIso (U.isoSpec.inv ≫ g ≫ U.isoSpec.hom) := by
    apply isIso_of_restrict_eq hsurj hnil
    · rw [specMap_globalAlgebra, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, hg]
    · rw [reassoc_of% he', reassoc_of% hag, ← reassoc_of% he', Iso.inv_hom_id,
        Category.comp_id]
  have : g = U.isoSpec.hom ≫ (U.isoSpec.inv ≫ g ≫ U.isoSpec.hom) ≫ U.isoSpec.inv := by simp
  rw [this]
  infer_instance

/-- Two affine schemes over `Spec R` that are smooth and have the same fibre over `Spec R₀` are
isomorphic, compatibly with the fibre. -/
theorem exists_iso_of_fibre (hsurj : Function.Surjective (algebraMap R R₀))
    (hnil : IsNilpotent (RingHom.ker (algebraMap R R₀)))
    {U U' W : Scheme.{u}} [IsAffine U] [IsAffine U'] (p : U ⟶ S) (p' : U' ⟶ S)
    [Smooth p] [Smooth p'] (a : W ⟶ U) (a' : W ⟶ U')
    (w : W ⟶ Spec (CommRingCat.of R₀)) (hW : IsPullback a w p c) (hW' : IsPullback a' w p' c) :
    ∃ h : U' ≅ U, h.hom ≫ p = p' ∧ a' ≫ h.hom = a := by
  obtain ⟨y, hy₁, hy₂⟩ := exists_lift hsurj hnil p' a' w hW' p a (by rw [hW.w, hW'.w])
  obtain ⟨y', hy'₁, hy'₂⟩ := exists_lift hsurj hnil p a w hW p' a' (by rw [hW.w, hW'.w])
  have h₁ : IsIso (y' ≫ y) := isIso_of_fibre hsurj hnil p a w hW _
    (by rw [Category.assoc, hy₁, hy'₁]) (by rw [reassoc_of% hy'₂, hy₂])
  have h₂ : IsIso (y ≫ y') := isIso_of_fibre hsurj hnil p' a' w hW' _
    (by rw [Category.assoc, hy'₁, hy₁]) (by rw [reassoc_of% hy₂, hy'₂])
  have : Epi y := epi_of_epi y' y
  have : IsSplitMono y := IsSplitMono.mk' ⟨y' ≫ inv (y ≫ y'), by
    rw [← Category.assoc, IsIso.hom_inv_id]⟩
  have : IsIso y := isIso_of_epi_of_isSplitMono y
  exact ⟨asIso y, hy₁, hy₂⟩

end Scheme

end Langlands.AlgebraicGeometry.AffineNilpotentThickening
