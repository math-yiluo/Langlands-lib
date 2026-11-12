import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.BaseLifting
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Polynomial.Basic

/-! # The first-order thickening of a presentation, its derivation and its lifting property -/

universe u

open CategoryTheory

set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Presentation

open MvPolynomial

variable {R : Type u} [CommRing R] {n : ℕ} {A₀ : Type u} [CommRing A₀] [Algebra R A₀]
  (s : MvPolynomial (Fin n) R →ₐ[R] A₀)

/-- The kernel `J` of a presentation `s : R[x₁, …, xₙ] → A₀`. -/
abbrev J : Ideal (MvPolynomial (Fin n) R) := RingHom.ker s.toRingHom

/-- The first-order thickening `R[x₁, …, xₙ] / J²` of the presentation. -/
abbrev Pres := MvPolynomial (Fin n) R ⧸ J s ^ 2

/-- `J² ≤ J`. -/
lemma sq_le_ker : J s ^ 2 ≤ RingHom.ker s.toRingHom := Ideal.pow_le_self two_ne_zero

/-- The map `R[x₁, …, xₙ] / J² → A₀` induced by the presentation. -/
def presMap : Pres s →ₐ[R] A₀ :=
  Ideal.Quotient.liftₐ (J s ^ 2) s (fun _ ha => sq_le_ker s ha)

@[simp]
lemma presMap_mk (a : MvPolynomial (Fin n) R) : presMap s (Ideal.Quotient.mk _ a) = s a := rfl

instance : Algebra (Pres s) A₀ := (presMap s).toRingHom.toAlgebra

/-- The structure map of the `A₀`-algebra structure is `presMap`. -/
lemma algebraMap_pres (x : Pres s) : algebraMap (Pres s) A₀ x = presMap s x := rfl

instance : IsScalarTower R (Pres s) A₀ :=
  IsScalarTower.of_algebraMap_eq (fun r => ((presMap s).commutes r).symm)

variable {s}

/-- `R[x]/J² → A₀` is surjective when the presentation is. -/
lemma presMap_surjective (hs : Function.Surjective s) :
    Function.Surjective (algebraMap (Pres s) A₀) := by
  intro a
  obtain ⟨b, rfl⟩ := hs a
  exact ⟨Ideal.Quotient.mk _ b, rfl⟩

variable (s)

/-- The class of `a` lies in the kernel of `R[x]/J² → A₀` iff `a ∈ J`. -/
lemma mem_ker_iff (a : MvPolynomial (Fin n) R) :
    Ideal.Quotient.mk (J s ^ 2) a ∈ RingHom.ker (algebraMap (Pres s) A₀) ↔ a ∈ J s :=
  Iff.rfl

/-- The kernel of `R[x₁, …, xₙ] / J² → A₀` has square zero. -/
lemma ker_mul_eq_zero (x : Pres s) (hx : x ∈ RingHom.ker (algebraMap (Pres s) A₀))
    (y : Pres s) (hy : y ∈ RingHom.ker (algebraMap (Pres s) A₀)) : x * y = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
  exact Ideal.mul_mem_mul hx hy

/-- The kernel of `R[x]/J² → A₀` is nilpotent. -/
lemma ker_isNilpotent : IsNilpotent (RingHom.ker (algebraMap (Pres s) A₀)) := by
  refine ⟨2, ?_⟩
  rw [Submodule.zero_eq_bot, eq_bot_iff, pow_two (RingHom.ker (algebraMap (Pres s) A₀))]
  refine Ideal.mul_le.mpr fun a ha c hc => ?_
  rw [ker_mul_eq_zero s a ha c hc]
  exact Submodule.zero_mem _

section Lift

/-- **Lifting property.** Along a surjection `q : A → B` with square-zero kernel, every
`R`-algebra map `A₀ → B` composed with `R[x]/J² → A₀` lifts to `R[x]/J² → A`. -/
lemma exists_lift {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (q : A →ₐ[R] B) (hq : Function.Surjective q)
    (hsq : ∀ a ∈ RingHom.ker q.toRingHom, ∀ b ∈ RingHom.ker q.toRingHom, a * b = 0)
    (χ : A₀ →ₐ[R] B) :
    ∃ ρ : Pres s →ₐ[R] A, q.comp ρ = χ.comp (IsScalarTower.toAlgHom R (Pres s) A₀) := by
  let ρ₁ : MvPolynomial (Fin n) R →ₐ[R] A :=
    aeval fun k => Function.surjInv hq (χ (s (X k)))
  have hρ₁ : q.comp ρ₁ = χ.comp s := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, ρ₁, aeval_X]
    exact Function.surjInv_eq hq _
  have hker : ∀ a ∈ J s, ρ₁ a ∈ RingHom.ker q.toRingHom := by
    intro a ha
    rw [RingHom.mem_ker]
    change (q.comp ρ₁) a = 0
    rw [hρ₁, AlgHom.comp_apply]
    change χ (s.toRingHom a) = 0
    rw [RingHom.mem_ker.mp ha, map_zero]
  have hJ : ∀ a ∈ J s ^ 2, ρ₁ a = 0 := by
    intro a ha
    rw [pow_two] at ha
    refine Submodule.mul_induction_on (C := fun a => ρ₁ a = 0) ha ?_ ?_
    · intro a ha b hb
      rw [map_mul]
      exact hsq _ (hker a ha) _ (hker b hb)
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
  refine ⟨Ideal.Quotient.liftₐ (J s ^ 2) ρ₁ hJ, ?_⟩
  apply Ideal.Quotient.algHom_ext
  ext k
  change q (ρ₁ (X k)) = χ (s (X k))
  exact DFunLike.congr_fun hρ₁ (X k)

end Lift

section Derivation

/-- The partial derivatives followed by the presentation. -/
def d₁ : MvPolynomial (Fin n) R →ₗ[R] (Fin n → A₀) :=
  LinearMap.pi fun k => s.toLinearMap ∘ₗ (pderiv k).toLinearMap

/-- The components of `d₁`. -/
@[simp]
lemma d₁_apply (a : MvPolynomial (Fin n) R) (k : Fin n) : d₁ s a k = s (pderiv k a) := rfl

/-- The Leibniz rule for `d₁`, with values in the `A₀`-module `A₀ⁿ`. -/
lemma d₁_mul (a b : MvPolynomial (Fin n) R) : d₁ s (a * b) = s a • d₁ s b + s b • d₁ s a := by
  funext k
  simp only [d₁_apply, Derivation.leibniz, smul_eq_mul, map_add, map_mul, Pi.add_apply,
    Pi.smul_apply]

/-- `d₁` vanishes on `J²`. -/
lemma d₁_eq_zero (a : MvPolynomial (Fin n) R) (ha : a ∈ J s ^ 2) : d₁ s a = 0 := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on (C := fun a => d₁ s a = 0) ha ?_ ?_
  · intro a ha b hb
    rw [d₁_mul]
    change s.toRingHom a • _ + s.toRingHom b • _ = 0
    rw [RingHom.mem_ker.mp ha, RingHom.mem_ker.mp hb, zero_smul, zero_smul, add_zero]
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-- The derivation `D : R[x]/J² → A₀ⁿ`, `D x = (∂ₖ x mod J)ₖ`. -/
def presDer : Derivation R (Pres s) (Fin n → A₀) :=
  Derivation.mk'
    (((J s ^ 2).restrictScalars R).liftQ (d₁ s) (fun a ha => LinearMap.mem_ker.mpr
        (d₁_eq_zero s a ((Submodule.restrictScalars_mem R _ a).mp ha))) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv R (J s ^ 2)).symm.toLinearMap)
    (by
      intro x y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_mul]
      change d₁ s (a * b) = Ideal.Quotient.mk _ a • d₁ s b + Ideal.Quotient.mk _ b • d₁ s a
      rw [d₁_mul]
      rfl)

/-- `presDer` on classes of polynomials. -/
@[simp]
lemma presDer_mk (a : MvPolynomial (Fin n) R) :
    presDer s (Ideal.Quotient.mk _ a) = d₁ s a := rfl

/-- **Universality.** Every `R`-derivation of `R[x]/J²` into an `A₀`-module factors through
`presDer` by an `A₀`-linear map. -/
lemma exists_presDer_factor {M : Type u} [AddCommGroup M] [Module A₀ M] [Module (Pres s) M]
    [IsScalarTower (Pres s) A₀ M] [Module R M] [IsScalarTower R (Pres s) M]
    (δ : Derivation R (Pres s) M) :
    ∃ D' : (Fin n → A₀) →ₗ[A₀] M, ∀ x, δ x = D' (presDer s x) := by
  classical
  refine ⟨Fintype.linearCombination A₀ (fun k => δ (Ideal.Quotient.mk _ (X k))), ?_⟩
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction a using MvPolynomial.induction_on with
  | C r =>
    rw [presDer_mk]
    have h1 : d₁ s (C r) = 0 := by funext k; simp
    have h2 : (Ideal.Quotient.mk (J s ^ 2) (C r)) = algebraMap R (Pres s) r := rfl
    rw [h1, map_zero, h2, Derivation.map_algebraMap]
  | add a b ha hb =>
    simp only [map_add]
    rw [ha, hb]
  | mul_X a k ha =>
    have hX : Fintype.linearCombination A₀ (fun k => δ (Ideal.Quotient.mk (J s ^ 2) (X k)))
        (d₁ s (X k)) = δ (Ideal.Quotient.mk _ (X k)) := by
      rw [Fintype.linearCombination_apply]
      simp [Pi.single_apply]
    have e1 : presDer s (Ideal.Quotient.mk _ (a * X k)) = s a • d₁ s (X k) + s (X k) • d₁ s a := by
      rw [presDer_mk, d₁_mul]
    rw [e1, map_add, map_smul, map_smul, hX, ← presDer_mk, ← ha, map_mul, Derivation.leibniz,
      ← algebraMap_smul A₀ (Ideal.Quotient.mk (J s ^ 2) a) (δ (Ideal.Quotient.mk _ (X k))),
      ← algebraMap_smul A₀ (Ideal.Quotient.mk (J s ^ 2) (X k)) (δ (Ideal.Quotient.mk _ a))]
    rfl

end Derivation

section Kernel

variable {s}

/-- The `A₀`-module structure on the kernel `J/J²` of `R[x]/J² → A₀`. -/
abbrev qModule (hs : Function.Surjective s) : Module A₀ (RingHom.ker (algebraMap (Pres s) A₀)) :=
  kerModule (algebraMap (Pres s) A₀) (presMap_surjective hs) (ker_mul_eq_zero s)

/-- The `R[x]/J²`- and `A₀`-module structures on the kernel form a scalar tower. -/
lemma qModule_isScalarTower (hs : Function.Surjective s) :
    letI := qModule hs
    IsScalarTower (Pres s) A₀ (RingHom.ker (algebraMap (Pres s) A₀)) := by
  letI := qModule hs
  refine ⟨fun x a m => ?_⟩
  obtain ⟨a', rfl⟩ := presMap_surjective hs a
  rw [Algebra.smul_def, ← map_mul]
  change (kerModule _ (presMap_surjective hs) (ker_mul_eq_zero s)).smul
      (algebraMap (Pres s) A₀ (x * a')) m =
    x • (kerModule _ (presMap_surjective hs) (ker_mul_eq_zero s)).smul
      (algebraMap (Pres s) A₀ a') m
  rw [kerModule_smul, kerModule_smul, mul_smul]

/-- The kernel is a finite `A₀`-module when `R` is noetherian. -/
lemma qModule_finite [IsNoetherianRing R] (hs : Function.Surjective s) :
    letI := qModule hs
    Module.Finite A₀ (RingHom.ker (algebraMap (Pres s) A₀)) := by
  letI := qModule hs
  haveI := qModule_isScalarTower hs
  exact Module.Finite.of_restrictScalars_finite (Pres s) A₀ _

end Kernel

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Presentation
