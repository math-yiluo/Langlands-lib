import Langlands.GroupScheme.IntegralModel.Smoothening.IntegralFunctionsBasic
import Langlands.GroupScheme.IntegralModel.Smoothening.TensorDensity
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.DedekindDomain.Basic

/-! # The Hopf algebra of integral functions

Let `R` be a discrete valuation ring with fraction field `K` and `A` a flat
commutative Hopf algebra over `R`. The integral functions on the generic fibre form a
flat `R`-algebra containing `A` to which the comultiplication, counit and antipode of
`A` extend. The comultiplication extends because an element of `B ⊗ B` all of whose
values at pairs of `R`-points are divisible by `s` is divisible by `s`
(`DetectsMaximal.tensor`). The Hopf axioms follow from those of `A` by uniqueness of
extensions to flat targets. The inclusion `A → B` is a bialgebra homomorphism. -/

noncomputable section

universe u

open scoped TensorProduct
open Coalgebra Bialgebra TensorProduct

namespace Langlands.GroupScheme.IntegralModel.Smoothening

variable {R : Type u} {K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Type u} [CommRing A]

section Ext

variable [Algebra R A] {D : Type u} [CommRing D] [Algebra R D] [Module.Flat R D]

/-- Algebra maps from the integral functions to a flat algebra are determined by their
restriction to `A`. -/
theorem algHom_ext_incl {g₁ g₂ : integralFunctions R K A →ₐ[R] D}
    (h : g₁.comp (incl R K A) = g₂.comp (incl R K A)) : g₁ = g₂ :=
  algHom_ext _ g₁ g₂ fun a _ => AlgHom.congr_fun h a

theorem extend_incl (f : A →ₐ[R] D)
    (hf : ∀ (a : A) (s : R), s ≠ 0 → (∃ b ∈ integralFunctions R K A, s • b = (1 : K) ⊗ₜ a) →
      ∃ d : D, f a = s • d) (a : A) :
    extend f hf (incl R K A a) = f a :=
  extend_apply f hf a (one_tmul_mem_integralFunctions R K A a)

theorem extend_comp_incl (f : A →ₐ[R] D)
    (hf : ∀ (a : A) (s : R), s ≠ 0 → (∃ b ∈ integralFunctions R K A, s • b = (1 : K) ⊗ₜ a) →
      ∃ d : D, f a = s • d) :
    (extend f hf).comp (incl R K A) = f :=
  AlgHom.ext (extend_incl f hf)

end Ext

omit [IsDomain R] in
/-- If `s⁻¹ (1 ⊗ a)` is integral then `s` divides every value of `a`. -/
theorem dvd_of_exists_smul_eq [Algebra R A] {s : R} {a : A}
    (h : ∃ b ∈ integralFunctions R K A, s • b = (1 : K) ⊗ₜ a) (χ : A →ₐ[R] R) : s ∣ χ a := by
  obtain ⟨b, hb, hsb⟩ := h
  refine ⟨point χ ⟨b, hb⟩, ?_⟩
  have : incl R K A a = s • (⟨b, hb⟩ : integralFunctions R K A) := Subtype.ext hsb.symm
  rw [← point_incl (K := K) χ a, this, point_smul]

section DVR

variable [IsDiscreteValuationRing R]

/-- Over a discrete valuation ring the integral functions are flat, being torsion-free. -/
instance instFlat [Algebra R A] : Module.Flat R (integralFunctions R K A) :=
  inferInstance

/-- The values at `R`-points detect the maximal ideal on the integral functions. -/
theorem detectsMaximal_point [Algebra R A] :
    DetectsMaximal (fun φ : A →ₐ[R] R => (point (K := K) φ).toLinearMap) := by
  intro b hb
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨b', rfl⟩ := exists_eq_smul_of_dvd hϖ.ne_zero b fun φ => by
    have := hb φ
    rw [hm, Ideal.mem_span_singleton] at this
    exact this
  exact Submodule.smul_mem_smul (by rw [hm]; exact Ideal.mem_span_singleton_self ϖ)
    Submodule.mem_top

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem productForm_point_map_incl [Algebra R A] (φ ψ : A →ₐ[R] R) (x : A ⊗[R] A) :
    productForm (point (K := K) φ).toLinearMap (point (K := K) ψ).toLinearMap
        (Algebra.TensorProduct.map (incl R K A) (incl R K A) x) =
      Algebra.TensorProduct.lift φ ψ (fun _ _ => .all _ _) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a a' => simp [point_incl]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

section Bialgebra

variable [Bialgebra R A]

/-- The comultiplication of `A` followed by the inclusion into `B ⊗ B`. -/
def comulAux : A →ₐ[R] integralFunctions R K A ⊗[R] integralFunctions R K A :=
  (Algebra.TensorProduct.map (incl R K A) (incl R K A)).comp (comulAlgHom R A)

theorem comulAux_divisible (a : A) (s : R) (hs : s ≠ 0)
    (h : ∃ b ∈ integralFunctions R K A, s • b = (1 : K) ⊗ₜ a) :
    ∃ d, comulAux (R := R) (K := K) a = s • d := by
  refine (detectsMaximal_point.tensor detectsMaximal_point).exists_eq_smul hs _ fun p => ?_
  change s ∣ productForm (point (K := K) p.1).toLinearMap (point (K := K) p.2).toLinearMap
    (Algebra.TensorProduct.map (incl R K A) (incl R K A) (comulAlgHom R A a))
  rw [productForm_point_map_incl]
  exact dvd_of_exists_smul_eq h
    ((Algebra.TensorProduct.lift p.1 p.2 fun _ _ => .all _ _).comp (comulAlgHom R A))

/-- The comultiplication of the integral functions. -/
def comulInt :
    integralFunctions R K A →ₐ[R] integralFunctions R K A ⊗[R] integralFunctions R K A :=
  extend (B := integralFunctions R K A)
    (D := integralFunctions R K A ⊗[R] integralFunctions R K A) comulAux
    fun a s hs h => comulAux_divisible a s hs h

theorem comulInt_incl (a : A) :
    comulInt (R := R) (K := K) (incl R K A a) = comulAux a :=
  extend_incl _ _ a

theorem comulInt_comp_incl :
    (comulInt (R := R) (K := K) (A := A)).comp (incl R K A) =
      (Algebra.TensorProduct.map (incl R K A) (incl R K A)).comp (comulAlgHom R A) :=
  AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, comulInt_incl]
    rfl

theorem comulInt_comp_incl' :
    (comulInt (R := R) (K := K) (A := A)).toLinearMap ∘ₗ (incl R K A).toLinearMap =
      map (incl R K A).toLinearMap (incl R K A).toLinearMap ∘ₗ comul :=
  congrArg AlgHom.toLinearMap (comulInt_comp_incl (K := K) (A := A))

/-- The counit of the integral functions: evaluation at the identity point. -/
def counitInt : integralFunctions R K A →ₐ[R] R :=
  point (counitAlgHom R A)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem counitInt_comp_incl :
    (counitInt (R := R) (K := K) (A := A)).comp (incl R K A) = counitAlgHom R A :=
  point_comp_incl _

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem counitInt_comp_incl' :
    (counitInt (R := R) (K := K) (A := A)).toLinearMap ∘ₗ (incl R K A).toLinearMap = counit :=
  congrArg AlgHom.toLinearMap (counitInt_comp_incl (K := K) (A := A))

/-- The bialgebra structure on the integral functions. -/
instance instBialgebra : Bialgebra R (integralFunctions R K A) := by
  refine .ofAlgHom comulInt counitInt ?_ ?_ ?_
  · refine algHom_ext_incl (D := integralFunctions R K A ⊗[R]
      (integralFunctions R K A ⊗[R] integralFunctions R K A)) ?_
    apply AlgHom.toLinearMap_injective
    simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comulInt_comp_incl']
    simp [coassoc_simps]
  · apply algHom_ext_incl
    apply AlgHom.toLinearMap_injective
    simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comulInt_comp_incl', counitInt_comp_incl']
    rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · refine algHom_ext_incl (D := integralFunctions R K A ⊗[R] R) ?_
    apply AlgHom.toLinearMap_injective
    simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comulInt_comp_incl', counitInt_comp_incl']
    rw [CoassocSimps.map_counit_comp_comul_right]; rfl

theorem comulAlgHom_int :
    comulAlgHom R (integralFunctions R K A) = comulInt (R := R) (K := K) (A := A) :=
  rfl

theorem counitAlgHom_int :
    counitAlgHom R (integralFunctions R K A) = counitInt (R := R) (K := K) (A := A) :=
  rfl

/-- The inclusion of `A` into the integral functions as a bialgebra map. -/
def inclBialgHom : A →ₐc[R] integralFunctions R K A :=
  .ofAlgHom (incl R K A) counitInt_comp_incl comulInt_comp_incl.symm

@[simp]
theorem inclBialgHom_apply (a : A) : inclBialgHom (R := R) (K := K) a = incl R K A a :=
  rfl

end Bialgebra

section Hopf

variable [HopfAlgebra R A]

/-- The antipode of `A` followed by the inclusion. -/
def antipodeAux : A →ₐ[R] integralFunctions R K A :=
  (incl R K A).comp (HopfAlgebra.antipodeAlgHom R A)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem antipodeAux_divisible (a : A) (s : R) (hs : s ≠ 0)
    (h : ∃ b ∈ integralFunctions R K A, s • b = (1 : K) ⊗ₜ a) :
    ∃ d, antipodeAux (R := R) (K := K) a = s • d :=
  exists_eq_smul_of_dvd hs _ fun φ => by
    simp only [antipodeAux, AlgHom.comp_apply, point_incl]
    exact dvd_of_exists_smul_eq h (φ.comp (HopfAlgebra.antipodeAlgHom R A))

/-- The antipode of the integral functions. -/
def antipodeInt : integralFunctions R K A →ₐ[R] integralFunctions R K A :=
  extend (B := integralFunctions R K A) (D := integralFunctions R K A) antipodeAux
    fun a s hs h => antipodeAux_divisible a s hs h

theorem antipodeInt_incl (a : A) :
    antipodeInt (R := R) (K := K) (incl R K A a) = incl R K A (HopfAlgebra.antipode R a) :=
  extend_incl _ _ a

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem lift_antipodeAlgHom_comp_comul :
    (Algebra.TensorProduct.lift (HopfAlgebra.antipodeAlgHom R A) (.id R A)
        fun _ _ => .all _ _).comp (comulAlgHom R A) =
      (Algebra.ofId R A).comp (counitAlgHom R A) := by
  apply AlgHom.toLinearMap_injective
  have h : (Algebra.TensorProduct.lift (HopfAlgebra.antipodeAlgHom R A) (.id R A)
      fun _ _ => .all _ _).toLinearMap =
      LinearMap.mul' R A ∘ₗ (HopfAlgebra.antipode R).rTensor A :=
    TensorProduct.ext' fun _ _ => by simp
  rw [AlgHom.comp_toLinearMap, h, LinearMap.comp_assoc, toLinearMap_comulAlgHom,
    HopfAlgebra.mul_antipode_rTensor_comul]
  rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem lift_id_antipodeAlgHom_comp_comul :
    (Algebra.TensorProduct.lift (.id R A) (HopfAlgebra.antipodeAlgHom R A)
        fun _ _ => .all _ _).comp (comulAlgHom R A) =
      (Algebra.ofId R A).comp (counitAlgHom R A) := by
  apply AlgHom.toLinearMap_injective
  have h : (Algebra.TensorProduct.lift (.id R A) (HopfAlgebra.antipodeAlgHom R A)
      fun _ _ => .all _ _).toLinearMap =
      LinearMap.mul' R A ∘ₗ (HopfAlgebra.antipode R).lTensor A :=
    TensorProduct.ext' fun _ _ => by simp
  rw [AlgHom.comp_toLinearMap, h, LinearMap.comp_assoc, toLinearMap_comulAlgHom,
    HopfAlgebra.mul_antipode_lTensor_comul]
  rfl

/-- The Hopf algebra structure on the integral functions. -/
instance instHopfAlgebra : HopfAlgebra R (integralFunctions R K A) := by
  refine .ofAlgHom antipodeInt ?_ ?_
  · refine algHom_ext_incl (AlgHom.ext fun a => ?_)
    have h := AlgHom.congr_fun (lift_antipodeAlgHom_comp_comul (R := R) (A := A)) a
    simp only [AlgHom.comp_apply, comulAlgHom_int, counitAlgHom_int] at h ⊢
    rw [← AlgHom.comp_apply comulInt, comulInt_comp_incl, AlgHom.comp_apply,
      ← AlgHom.comp_apply counitInt, counitInt_comp_incl]
    have key : ∀ x : A ⊗[R] A,
        Algebra.TensorProduct.lift antipodeInt (.id R _) (fun _ _ => .all _ _)
          (Algebra.TensorProduct.map (incl R K A) (incl R K A) x) =
        incl R K A (Algebra.TensorProduct.lift (HopfAlgebra.antipodeAlgHom R A) (.id R A)
          (fun _ _ => .all _ _) x) := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul x y => simp [antipodeInt_incl]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    rw [key, h]
    simp
  · refine algHom_ext_incl (AlgHom.ext fun a => ?_)
    have h := AlgHom.congr_fun (lift_id_antipodeAlgHom_comp_comul (R := R) (A := A)) a
    simp only [AlgHom.comp_apply, comulAlgHom_int, counitAlgHom_int] at h ⊢
    rw [← AlgHom.comp_apply comulInt, comulInt_comp_incl, AlgHom.comp_apply,
      ← AlgHom.comp_apply counitInt, counitInt_comp_incl]
    have key : ∀ x : A ⊗[R] A,
        Algebra.TensorProduct.lift (.id R _) antipodeInt (fun _ _ => .all _ _)
          (Algebra.TensorProduct.map (incl R K A) (incl R K A) x) =
        incl R K A (Algebra.TensorProduct.lift (.id R A) (HopfAlgebra.antipodeAlgHom R A)
          (fun _ _ => .all _ _) x) := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul x y => simp [antipodeInt_incl]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    rw [key, h]
    simp

end Hopf

end DVR

end Langlands.GroupScheme.IntegralModel.Smoothening
