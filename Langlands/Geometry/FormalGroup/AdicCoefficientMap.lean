import Langlands.Geometry.FormalGroup.NilpotentReduction
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Maps from an adic coefficient ring to a nilpotent test algebra -/

noncomputable section

universe u v w

open CategoryTheory

namespace Langlands.FormalGroup.Nilp

variable {O : Type u} [CommRing O] {π : O}
variable {C : Type w} [CommRing C] [Algebra O C]

/-- The completion of a coefficient algebra in the image of the distinguished scalar. -/
abbrev AdicCoefficients (π : O) (C : Type w) [CommRing C] [Algebra O C] :=
  AdicCompletion (Ideal.span {algebraMap O C π}) C

/-- The actual map from coefficients to their completion. -/
def toAdicCoefficients (π : O) (C : Type w) [CommRing C] [Algebra O C] :
    C →ₐ[O] AdicCoefficients π C :=
  IsScalarTower.toAlgHom O C _

local notation "J" => (Ideal.span {algebraMap O C π})

private theorem coeff_pow_mem_ker {A : Type*} [CommRing A] [Algebra O A]
    (g : C →ₐ[O] A) {n : ℕ} (hn : (algebraMap O A π) ^ n = 0) {x : C}
    (hx : x ∈ J ^ n) : g x = 0 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, g.commutes, hn, zero_mul]

private theorem completion_pow_mem_ker (B : Nilp.{u, v} O π)
    (g : AdicCoefficients π C →ₐ[O] B.obj) {n : ℕ}
    (hn : (algebraMap O B.obj π) ^ n = 0) {x : AdicCoefficients π C}
    (hx : AdicCompletion.evalₐ J n x = 0) : g x = 0 := by
  have hle : J ^ n ≤ J ^ n • (⊤ : Ideal C) := by simp
  have hx' : x ∈ (AdicCompletion.eval J C n).ker := by
    rw [LinearMap.mem_ker, ← AdicCompletion.factor_evalₐ_eq_eval J x hle, hx, map_zero]
  have hf : (J).FG := Submodule.fg_span_singleton _
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval hf,
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at hx'
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx'
  rw [← hy, Algebra.smul_def, map_mul, map_pow, map_pow,
    ← IsScalarTower.algebraMap_apply O C (AdicCoefficients π C), g.commutes, hn, zero_mul]

variable (B : Nilp.{u, v} O π)

/-- Restriction to the original coefficient algebra is injective on maps into every
nilpotent test algebra. At an exponent killing π the test map factors through reduction. -/
theorem adicCoefficient_restrict_injective :
    Function.Injective (fun g : AdicCoefficients π C →ₐ[O] B.obj =>
      g.comp (toAdicCoefficients π C)) := by
  intro g h hgh
  obtain ⟨n, hn⟩ := B.nilpotent
  apply AlgHom.ext
  intro x
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  let z := toAdicCoefficients π C y
  have hz : AdicCompletion.evalₐ J n z = AdicCompletion.evalₐ J n x :=
    (AdicCompletion.evalₐ_of J n y).trans hy
  have he : AdicCompletion.evalₐ J n (x - z) = 0 := by rw [map_sub, hz, sub_self]
  have hg := completion_pow_mem_ker B g hn he
  have hh := completion_pow_mem_ker B h hn he
  rw [map_sub, sub_eq_zero] at hg hh
  exact hg.trans ((AlgHom.congr_fun hgh y).trans hh.symm)

/-- Completion in the distinguished scalar does not change maps to Nilp tests. -/
def adicCoefficientMapEquiv :
    (AdicCoefficients π C →ₐ[O] B.obj) ≃ (C →ₐ[O] B.obj) :=
  Equiv.ofBijective (fun g => g.comp (toAdicCoefficients π C))
    ⟨B.adicCoefficient_restrict_injective, fun g => by
      let n := B.nilpotent.choose
      have hn := B.nilpotent.choose_spec
      refine ⟨(Ideal.Quotient.liftₐ (J ^ n) g
        (fun _ hx => coeff_pow_mem_ker g hn hx)).comp ((AdicCompletion.evalₐ J n).restrictScalars O), ?_⟩
      apply AlgHom.ext
      intro x
      change Ideal.Quotient.liftₐ (J ^ n) g (fun _ hx => coeff_pow_mem_ker g hn hx)
        (AdicCompletion.evalₐ J n (AdicCompletion.of J C x)) = g x
      rw [AdicCompletion.evalₐ_of]
      rfl⟩

@[simp]
theorem adicCoefficientMapEquiv_apply (g : AdicCoefficients π C →ₐ[O] B.obj) :
    B.adicCoefficientMapEquiv g = g.comp (toAdicCoefficients π C) := rfl

/-- The canonical lift to the completion commutes with every morphism of Nilp tests. -/
theorem adicCoefficientMapEquiv_symm_natural {B' : Nilp.{u, v} O π}
    (f : B ⟶ B') (g : C →ₐ[O] B.obj) :
    f.hom.hom.comp (B.adicCoefficientMapEquiv.symm g) =
      B'.adicCoefficientMapEquiv.symm (f.hom.hom.comp g) := by
  apply B'.adicCoefficientMapEquiv.injective
  have h := B.adicCoefficientMapEquiv.apply_symm_apply g
  change (B.adicCoefficientMapEquiv.symm g).comp (toAdicCoefficients π C) = g at h
  change (f.hom.hom.comp (B.adicCoefficientMapEquiv.symm g)).comp (toAdicCoefficients π C) = _
  rw [AlgHom.comp_assoc, h]
  exact (B'.adicCoefficientMapEquiv.apply_symm_apply (f.hom.hom.comp g)).symm

end Langlands.FormalGroup.Nilp
