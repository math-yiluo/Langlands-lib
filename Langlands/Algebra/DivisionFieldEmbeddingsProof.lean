import Langlands.Algebra.DivisionFieldEmbeddingsStatement
import Langlands.Algebra.CentralSimpleScalarExtension
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-! Field embeddings into a finite-dimensional central division algebra are conjugate. -/

noncomputable section

namespace Langlands.CentralDivision

universe uK uL uD

open scoped TensorProduct

variable (K : Type uK) [Field K] (D : Type uD) [DivisionRing D] [Algebra K D]
  (L : Type uL) [Field L] [Algebra K L]

/-- Right multiplication by the image of an element of the commutative algebra `L`. -/
def rightMulHom (h : L →ₐ[K] D) : L →ₐ[K] Module.End K D where
  toFun a := LinearMap.mulRight K (h a)
  map_one' := by ext x; simp
  map_mul' a b := by
    ext x
    rw [mul_comm a b]
    simp [mul_assoc]
  map_zero' := by ext x; simp
  map_add' a b := by ext x; simp [mul_add]
  commutes' k := by
    ext x
    simp only [AlgHom.commutes, LinearMap.mulRight_apply, Module.algebraMap_end_apply]
    rw [Algebra.smul_def, Algebra.commutes]

/-- The action of `L ⊗[K] D` on `D` with `(a ⊗ d) • x = d * x * h a`. -/
def twistRep (h : L →ₐ[K] D) : L ⊗[K] D →ₐ[K] Module.End K D :=
  Algebra.TensorProduct.lift (rightMulHom K D L h) (Algebra.lmul K D)
    (fun a d => (LinearMap.commute_mulLeft_right d (h a)).symm)

@[simp] theorem twistRep_tmul_apply (h : L →ₐ[K] D) (a : L) (d x : D) :
    twistRep K D L h (a ⊗ₜ[K] d) x = d * x * h a := by
  simp [twistRep, rightMulHom]

/-- The type `D`, regarded as an `L ⊗[K] D`-module through `twistRep K D L h`. -/
@[nolint unusedArguments]
def Twist (_h : L →ₐ[K] D) : Type uD := D

namespace Twist

variable {K D L} (h : L →ₐ[K] D)

instance : AddCommGroup (Twist K D L h) := inferInstanceAs (AddCommGroup D)

instance : Module K (Twist K D L h) := inferInstanceAs (Module K D)

instance : Nontrivial (Twist K D L h) := inferInstanceAs (Nontrivial D)

instance [FiniteDimensional K D] : FiniteDimensional K (Twist K D L h) :=
  inferInstanceAs (FiniteDimensional K D)

instance : Module (L ⊗[K] D) (Twist K D L h) :=
  Module.compHom D (twistRep K D L h).toRingHom

theorem smul_def (b : L ⊗[K] D) (x : Twist K D L h) :
    b • x = (twistRep K D L h b : Module.End K D) (x : D) := rfl


instance : IsScalarTower K (L ⊗[K] D) (Twist K D L h) where
  smul_assoc k b x := by
    rw [smul_def, smul_def, map_smul]
    rfl

end Twist

variable [FiniteDimensional K D] [Algebra.IsCentral K D] [FiniteDimensional K L]

/-- There is a nonzero `L ⊗[K] D`-linear map between the two twisted copies of `D`. -/
theorem exists_twist_linearMap_ne_zero (f g : L →ₐ[K] D) :
    ∃ φ : Twist K D L f →ₗ[L ⊗[K] D] Twist K D L g, φ ≠ 0 := by
  have : IsSimpleRing (L ⊗[K] D) := Langlands.CentralSimple.isSimpleRing_baseChange K D L
  have : IsArtinianRing (L ⊗[K] D) := IsArtinianRing.of_finite K (L ⊗[K] D)
  have : Module.Finite (L ⊗[K] D) (Twist K D L f) :=
    Module.Finite.of_restrictScalars_finite K (L ⊗[K] D) _
  have : Module.Finite (L ⊗[K] D) (Twist K D L g) :=
    Module.Finite.of_restrictScalars_finite K (L ⊗[K] D) _
  have hP := IsSimpleRing.isIsotypic (L ⊗[K] D) (Twist K D L f × Twist K D L g)
  obtain ⟨-, -, S, hS, -⟩ := hP.linearEquiv_fun
  have hf : IsIsotypicOfType (L ⊗[K] D) (Twist K D L f) S :=
    (hP S).of_injective (LinearMap.inl (L ⊗[K] D) _ _) LinearMap.inl_injective
  have hg : IsIsotypicOfType (L ⊗[K] D) (Twist K D L g) S :=
    (hP S).of_injective (LinearMap.inr (L ⊗[K] D) _ _) LinearMap.inr_injective
  obtain ⟨p, ⟨ef⟩⟩ := hf.linearEquiv_fun
  obtain ⟨q, ⟨eg⟩⟩ := hg.linearEquiv_fun
  have hp : 0 < p := by
    refine Nat.pos_of_ne_zero fun hp => ?_
    subst hp
    exact not_subsingleton (Twist K D L f) ef.toEquiv.subsingleton
  have hq : 0 < q := by
    refine Nat.pos_of_ne_zero fun hq => ?_
    subst hq
    exact not_subsingleton (Twist K D L g) eg.toEquiv.subsingleton
  have := IsSimpleModule.nontrivial (L ⊗[K] D) S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  refine ⟨eg.symm.toLinearMap ∘ₗ LinearMap.single (L ⊗[K] D) (fun _ : Fin q => S) ⟨0, hq⟩ ∘ₗ
    LinearMap.proj (R := L ⊗[K] D) (φ := fun _ : Fin p => S) ⟨0, hp⟩ ∘ₗ ef.toLinearMap, ?_⟩
  intro h0
  have h1 := LinearMap.congr_fun h0 (ef.symm (fun _ => s))
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.proj_apply, LinearMap.zero_apply,
    LinearEquiv.map_eq_zero_iff] at h1
  exact hs (by simpa using h1)

/-- Two `K`-algebra maps from `L` to `D` are conjugate by an explicit unit of `D`. -/
theorem exists_unit_conj (f g : L →ₐ[K] D) :
    ∃ u : Dˣ, ∀ a : L, f a = (u : D) * g a * ((u⁻¹ : Dˣ) : D) := by
  obtain ⟨φ, hφ⟩ := exists_twist_linearMap_ne_zero K D L f g
  let u : D := φ (1 : D)
  have hleft (d : D) : (φ d : D) = d * u := by
    have h1 : φ (twistRep K D L f ((1 : L) ⊗ₜ[K] d) 1) = d * u * g 1 :=
      (φ.map_smul ((1 : L) ⊗ₜ[K] d) (1 : D)).trans (twistRep_tmul_apply K D L g 1 d u)
    simpa using h1
  have hright (a : L) : (φ (f a) : D) = u * g a := by
    have h1 : φ (twistRep K D L f (a ⊗ₜ[K] (1 : D)) 1) = 1 * u * g a :=
      (φ.map_smul (a ⊗ₜ[K] (1 : D)) (1 : D)).trans (twistRep_tmul_apply K D L g a 1 u)
    simpa using h1
  have hu : u ≠ 0 := by
    intro hu
    apply hφ
    refine LinearMap.ext fun (d : D) => ?_
    change (φ d : D) = (0 : D)
    have hd : d * u = 0 := by rw [hu]; exact mul_zero d
    exact (hleft d).trans hd
  refine ⟨Units.mk0 u hu, fun a => ?_⟩
  have h2 : f a * u = u * g a := (hleft (f a)).symm.trans (hright a)
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, ← h2, mul_assoc, mul_inv_cancel₀ hu, mul_one]

/-- Field-embedding conjugacy in a finite-dimensional central division algebra. -/
theorem fieldEmbeddingsConjugate : FieldEmbeddingsConjugateStatement.{uK, uL, uD} :=
  fun K _ D _ _ _ _ L _ _ _ f g => exists_unit_conj K D L f g

end Langlands.CentralDivision
