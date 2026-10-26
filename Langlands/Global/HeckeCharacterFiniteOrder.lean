import Langlands.Global.HeckeCharacter
import Langlands.Global.AdelicGL
import Langlands.Global.AdelicFunctoriality.IdeleNormLift
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-! # Finite-order Hecke characters and norm-triviality -/

noncomputable section

universe u v w

namespace Langlands.Global

/-- A continuous complex-unit-valued function of bounded positive exponent is
locally constant, by factoring through the finite roots of unity. -/
theorem isLocallyConstant_of_complexUnits_pow_eq_one
    {X : Type w} [TopologicalSpace X] {f : X → ℂˣ} (hf : Continuous f)
    {m : ℕ} (hm : 0 < m) (hpow : ∀ x, f x ^ m = 1) :
    IsLocallyConstant f := by
  let : NeZero m := ⟨hm.ne'⟩
  let g : X → rootsOfUnity m ℂ :=
    fun x => ⟨f x, (mem_rootsOfUnity m (f x)).mpr (hpow x)⟩
  have hg : Continuous g := hf.subtype_mk _
  have hgc : IsLocallyConstant g := (IsLocallyConstant.iff_continuous g).mpr hg
  exact hgc.comp (fun z : rootsOfUnity m ℂ => (z : ℂˣ))

namespace HeckeCharacter

variable {F : Type u} [Field F] [NumberField F]

theorem hasFiniteOrder_one : (1 : HeckeCharacter F).HasFiniteOrder :=
  ⟨1, Nat.one_pos, by
    apply ContinuousMonoidHom.ext
    intro x
    simp only [pow_one]⟩

theorem HasFiniteOrder.mul {χ ψ : HeckeCharacter F}
    (hχ : χ.HasFiniteOrder) (hψ : ψ.HasFiniteOrder) : (χ * ψ).HasFiniteOrder := by
  rcases hχ with ⟨m, hm, hχ⟩
  rcases hψ with ⟨n, hn, hψ⟩
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  apply ContinuousMonoidHom.ext
  intro x
  have hx := congrArg (fun η : HeckeCharacter F => η x) hχ
  have hy := congrArg (fun η : HeckeCharacter F => η x) hψ
  simp only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun] at hx hy ⊢
  rw [ContinuousMonoidHom.mul_apply]
  rw [mul_pow, pow_mul, hx, one_pow, Nat.mul_comm m n, pow_mul, hy, one_pow, one_mul]

theorem HasFiniteOrder.inv {χ : HeckeCharacter F} (hχ : χ.HasFiniteOrder) :
    χ⁻¹.HasFiniteOrder := by
  rcases hχ with ⟨m, hm, hχ⟩
  refine ⟨m, hm, ?_⟩
  apply ContinuousMonoidHom.ext
  intro x
  have hx := congrArg (fun η : HeckeCharacter F => η x) hχ
  simp only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun] at hx ⊢
  change (χ x)⁻¹ ^ m = 1
  rw [inv_pow, hx, inv_one]

theorem HasFiniteOrder.isLocallyConstant {χ : HeckeCharacter F} (hχ : χ.HasFiniteOrder) :
    IsLocallyConstant χ := by
  rcases hχ with ⟨m, hm, hp⟩
  apply isLocallyConstant_of_complexUnits_pow_eq_one (f := fun x => χ x) χ.continuous_toFun hm
  intro x
  simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun,
    Pi.one_apply] using congrArg (fun η : HeckeCharacter F => η x) hp

/-- Pullback along any continuous map, including any actual adelic embedding. -/
theorem HasFiniteOrder.isLocallyConstant_pullback {χ : HeckeCharacter F}
    (hχ : χ.HasFiniteOrder) {X : Type w} [TopologicalSpace X]
    {f : X → IdeleClasses F} (hf : Continuous f) :
    IsLocallyConstant (fun x => χ (f x)) :=
  hχ.isLocallyConstant.comp_continuous hf

/-- The scalar determinant character on the actual full adelic matrix group. -/
theorem HasFiniteOrder.isLocallyConstant_determinant {χ : HeckeCharacter F}
    (hχ : χ.HasFiniteOrder) (n : ℕ) :
    IsLocallyConstant (fun g : AdelicGL F n =>
      (χ.onIdeles (AdelicGL.determinant F n g) : ℂ)) :=
  (hχ.isLocallyConstant_pullback
    ((ideleClassMap F).continuous.comp (AdelicGL.determinant F n).continuous)).comp
      (fun z : ℂˣ => (z : ℂ))

/-- In particular the whole archimedean determinant factor is locally constant. -/
theorem HasFiniteOrder.isLocallyConstant_infiniteDeterminant {χ : HeckeCharacter F}
    (hχ : χ.HasFiniteOrder) (n : ℕ) :
    IsLocallyConstant (fun g : InfiniteAdelicGL F n =>
      (χ.onIdeles (AdelicGL.determinant F n (AdelicGL.ofInfinite F n g)) : ℂ)) :=
  (hχ.isLocallyConstant_determinant n).comp_continuous
    (AdelicGL.ofInfinite F n).continuous

section Norm

variable (E : Type v) [Field E] [NumberField E] [Algebra F E]

/-- Triviality on the image of the actual quotient norm from the specified extension. -/
def IsTrivialOnNorm (χ : HeckeCharacter F) : Prop :=
  ∀ x : IdeleClasses E, χ (AdelicFunctoriality.ideleClassNorm (K := F) (L := E) x) = 1

theorem IsTrivialOnNorm.pow_finrank_eq_one {χ : HeckeCharacter F}
    (hχ : χ.IsTrivialOnNorm E) : χ ^ Module.finrank F E = 1 := by
  apply ContinuousMonoidHom.ext
  intro x
  have h := hχ (AdelicFunctoriality.ideleClassInclusion (K := F) (L := E) x)
  rw [AdelicFunctoriality.ideleClassNormInclusionPower F E x, map_pow] at h
  simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun,
    Pi.one_apply] using h

/-- The degree is positive, so norm-triviality supplies precisely the finite-order
hypothesis used by the full determinant-twist relation. -/
theorem IsTrivialOnNorm.hasFiniteOrder {χ : HeckeCharacter F}
    (hχ : χ.IsTrivialOnNorm E) : χ.HasFiniteOrder :=
  ⟨Module.finrank F E, Module.finrank_pos, hχ.pow_finrank_eq_one E⟩

end Norm
end HeckeCharacter
end Langlands.Global
