import Langlands.Geometry.FormalGroup.DrinfeldCoefficientSplitting

/-! # The cyclic grading of the Drinfeld tangent representation -/

noncomputable section

open scoped BigOperators TensorProduct

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision

universe u v s

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable {π : 𝒪[K]} {B B' : Nilp.{u, v} 𝒪[K] π}

private local instance : IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) :=
  subfieldIntegerAlgebra_isLocalHom ι

local notation "d" => CentralSimple.reducedDegree K D
local notation "C" => SubfieldIntegerRing K D ι

/-- The successor of a lifted cyclic character precomposes it with inverse Frobenius. -/
theorem subfieldCoefficientLift_succ [NeZero d] (σ : L ≃ₐ[K] L)
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (hσ : ∀ a : C,
      localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)
    (j : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
    (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj) (i : Fin d) (a : C) :
    subfieldCoefficientLift hL (subfieldCyclicCharacter ι hL j (i + 1)) ψ a =
      subfieldCoefficientLift hL (subfieldCyclicCharacter ι hL j i) ψ
        ((subfieldIntegerFrobenius ι σ hL).symm a) := by
  let : Algebra.Etale 𝒪[K] C := hL.2.2.1
  let χ := subfieldCyclicCharacter ι hL j
  let φ := subfieldCoefficientLift hL (χ i) ψ
  let f := (subfieldIntegerFrobenius ι σ hL).symm
  have h : φ.comp f.toAlgHom = B.liftEtale (ψ.comp (χ (i + 1))) := by
    apply Nilp.liftEtale_unique
    ext b
    change Nilp.reductionQuotient π B.obj (φ (f b)) = ψ (χ (i + 1) b)
    rw [subfieldCyclicCharacter_succ ι σ hL hσ j i b]
    exact AlgHom.congr_fun (reductionQuotient_comp_subfieldCoefficientLift hL (χ i) ψ) (f b)
  exact (AlgHom.congr_fun h a).symm

namespace SpecialModule

variable (X : SpecialModule K D ι B.obj)

/-- The actual tangent representation restricted to the coefficient integer ring. -/
def subfieldTangent : C →ₐ[𝒪[K]] Module.End B.obj (Fin d → B.obj) where
  __ := (X.order.fiberTangent (RingHom.id B.obj)).comp
    (subfieldIntegerInclusion K D ι).toRingHom
  commutes' a := by
    change X.order.fiberTangent (RingHom.id B.obj)
      (subfieldIntegerInclusion K D ι (algebraMap 𝒪[K] C a)) = _
    rw [AlgHom.commutes]
    apply LinearMap.ext
    intro x
    rw [X.order.fiberTangent_scalar, RingHom.id_apply, Module.algebraMap_end_apply, algebraMap_smul]

@[simp]
theorem subfieldTangent_apply (a : C) :
    X.subfieldTangent a =
      X.order.fiberTangent (RingHom.id B.obj) (subfieldIntegerInclusion K D ι a) := rfl

/-- Extend the actual coefficient action by the scalars of the test algebra. -/
def subfieldTangentTensor : B.obj ⊗[𝒪[K]] C →ₐ[B.obj] Module.End B.obj (Fin d → B.obj) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) X.subfieldTangent
    (fun b a => Algebra.commutes (R := B.obj) b (X.subfieldTangent a))

@[simp]
theorem subfieldTangentTensor_tmul (b : B.obj) (a : C) (x : Fin d → B.obj) :
    X.subfieldTangentTensor (b ⊗ₜ[𝒪[K]] a) x = b • X.subfieldTangent a x := rfl

/-- Transport the tangent action of the coefficient algebra to the split product. -/
def subfieldTangentSplit
    (j : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
    (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj) :
    (Fin d → B.obj) →ₐ[B.obj] Module.End B.obj (Fin d → B.obj) :=
  X.subfieldTangentTensor.comp (subfieldCyclicSplitting (B := B) X.unramified j ψ).symm.toAlgHom

/-- The tangent projector associated to the indexed cyclic character. -/
def tangentProjector
    (j : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
    (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj) (i : Fin d) :
    Module.End B.obj (Fin d → B.obj) :=
  X.subfieldTangentSplit j ψ (Pi.single i 1)

variable (j : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
  (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)

/-- The projector is idempotent. -/
theorem tangentProjector_idempotent (i : Fin d) :
    IsIdempotentElem (X.tangentProjector j ψ i) := by
  change X.tangentProjector j ψ i * X.tangentProjector j ψ i = X.tangentProjector j ψ i
  simp only [tangentProjector, ← map_mul, ← Pi.single_mul_right, Pi.single_eq_same, mul_one]

/-- Distinct character projectors are orthogonal. -/
theorem tangentProjector_mul_of_ne {i k : Fin d} (hik : i ≠ k) :
    X.tangentProjector j ψ i * X.tangentProjector j ψ k = 0 := by
  simp only [tangentProjector, ← map_mul, ← Pi.single_mul_left,
    Pi.single_eq_of_ne hik, one_mul, Pi.single_zero, map_zero]

/-- The character projectors sum to the identity. -/
theorem sum_tangentProjector : ∑ i, X.tangentProjector j ψ i = 1 := by
  have h : ∑ i, Pi.single i (1 : B.obj) = (1 : Fin d → B.obj) := by
    simpa only [Pi.one_apply] using Finset.univ_sum_single (1 : Fin d → B.obj)
  simp only [tangentProjector, ← map_sum, h, map_one]

/-- The homogeneous tangent summand for the indexed character. -/
def tangentComponent (i : Fin d) : Submodule B.obj (Fin d → B.obj) :=
  LinearMap.range (X.tangentProjector j ψ i)

/-- The image of the projector is its fixed submodule. -/
theorem mem_tangentComponent_iff_fixed (i : Fin d) (x : Fin d → B.obj) :
    x ∈ X.tangentComponent j ψ i ↔ X.tangentProjector j ψ i x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (X.tangentProjector_idempotent j ψ i) y
  · intro h
    exact ⟨x, h⟩

private theorem subfieldTangentSplit_mul_projector (g : Fin d → B.obj) (i : Fin d) :
    X.subfieldTangentSplit j ψ g * X.tangentProjector j ψ i =
      algebraMap B.obj _ (g i) * X.tangentProjector j ψ i := by
  rw [tangentProjector, ← AlgHom.commutes (X.subfieldTangentSplit j ψ), ← map_mul, ← map_mul]
  congr 1
  rw [← Pi.single_mul_right, ← Pi.single_mul_right]
  rfl

/-- The projector's image is exactly the simultaneous eigenspace of the lifted character. -/
theorem mem_tangentComponent_iff (i : Fin d) (x : Fin d → B.obj) :
    x ∈ X.tangentComponent j ψ i ↔
      ∀ a : C, X.subfieldTangent a x =
        subfieldCoefficientLift X.unramified (subfieldCyclicCharacter ι X.unramified j i) ψ a • x := by
  let ev := subfieldCyclicSplitting X.unramified j ψ
  constructor
  · intro hx a
    have hf := (X.mem_tangentComponent_iff_fixed j ψ i x).mp hx
    have h := congrArg (fun p : Module.End B.obj (Fin d → B.obj) => p x)
      (X.subfieldTangentSplit_mul_projector j ψ (ev (1 ⊗ₜ[𝒪[K]] a)) i)
    change X.subfieldTangentTensor (ev.symm (ev (1 ⊗ₜ[𝒪[K]] a)))
      (X.tangentProjector j ψ i x) = ev (1 ⊗ₜ[𝒪[K]] a) i • X.tangentProjector j ψ i x at h
    rw [ev.symm_apply_apply, subfieldTangentTensor_tmul, one_smul, hf] at h
    simpa [ev] using h
  · intro hx
    apply (X.mem_tangentComponent_iff_fixed j ψ i x).mpr
    have ht (t : B.obj ⊗[𝒪[K]] C) : X.subfieldTangentTensor t x = ev t i • x := by
      induction t using TensorProduct.inductionOn with
      | tmul b a =>
        rw [subfieldTangentTensor_tmul, hx, smul_smul]
        rfl
      | add t₁ t₂ h₁ h₂ =>
        simp only [map_add, LinearMap.add_apply, Pi.add_apply, h₁, h₂, add_smul]
    change X.subfieldTangentTensor (ev.symm (Pi.single i 1)) x = x
    simpa using ht (ev.symm (Pi.single i 1))

/-- The derivative of the division uniformizer sends each summand to its successor. -/
theorem fiberTangent_uniformizer_mem_tangentComponent [NeZero d]
    (uniformizer : Dˣ) (σ : L ≃ₐ[K] L)
    (hUniformizer : (uniformizer : D) ^ d = algebraMap K D (π : K))
    (hMul : ∀ a : L, (uniformizer : D) * ι a = ι (σ a) * (uniformizer : D))
    (hσ : ∀ a : C,
      localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)
    (i : Fin d) {x : Fin d → B.obj} (hx : x ∈ X.tangentComponent j ψ i) :
    X.order.fiberTangent (RingHom.id B.obj) (drinfeldIntegralUniformizer uniformizer hUniformizer)
        x ∈ X.tangentComponent j ψ (i + 1) := by
  apply (X.mem_tangentComponent_iff j ψ (i + 1) _).2
  intro a
  rw [subfieldCoefficientLift_succ σ X.unramified hσ j ψ i a]
  exact SpecialModule.fiberTangent_uniformizer_shift ι uniformizer σ X
    (RingHom.id B.obj) (subfieldCoefficientLift X.unramified
      (subfieldCyclicCharacter ι X.unramified j i) ψ).toRingHom hUniformizer hMul x
    ((X.mem_tangentComponent_iff j ψ i x).1 hx) a

private theorem subfieldTangentTensor_natural (f : B ⟶ B')
    (t : B.obj ⊗[𝒪[K]] C) (x : Fin d → B.obj) (k : Fin d) :
    (X.mapSameUniverse f.hom.hom).subfieldTangentTensor
        (Algebra.TensorProduct.map f.hom.hom (AlgHom.id 𝒪[K] _) t)
        (fun l => f.hom.hom (x l)) k =
      f.hom.hom (X.subfieldTangentTensor t x k) := by
  induction t using TensorProduct.inductionOn with
  | tmul b a =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, subfieldTangentTensor_tmul,
      Pi.smul_apply, smul_eq_mul, map_mul, subfieldTangent_apply]
    change f.hom.hom b * (X.order.map f.hom.hom).fiberTangent (RingHom.id B'.obj)
      (subfieldIntegerInclusion K D ι a) (fun l => f.hom.hom (x l)) k = _
    rw [X.order.fiberTangent_map]
    simp only [ModuleLaw.OrderAction.fiberTangent_apply_apply, RingHom.id_comp,
      RingHom.id_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sum, map_mul]
  | add t₁ t₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, h₁, h₂]

/-- The projectors commute with coefficient extension on tangent vectors. -/
theorem tangentProjector_natural (f : B ⟶ B') (i : Fin d) (x : Fin d → B.obj) (k : Fin d) :
    (X.mapSameUniverse f.hom.hom).tangentProjector j ((Nilp.reductionMap f.hom.hom).comp ψ) i
        (fun l => f.hom.hom (x l)) k =
      f.hom.hom (X.tangentProjector j ψ i x k) := by
  let t := (subfieldCyclicSplitting X.unramified j ψ).symm (Pi.single i 1)
  let ev' := subfieldCyclicSplitting (B := B') X.unramified j
    ((Nilp.reductionMap f.hom.hom).comp ψ)
  have ht : Algebra.TensorProduct.map f.hom.hom (AlgHom.id 𝒪[K] _) t = ev'.symm (Pi.single i 1) := by
    apply ev'.injective
    funext k
    rw [ev'.apply_symm_apply, subfieldCyclicSplitting_natural]
    by_cases hi : k = i
    · subst k
      simp [t]
    · simp [t, Pi.single_eq_of_ne hi]
  change (X.mapSameUniverse f.hom.hom).subfieldTangentTensor (ev'.symm (Pi.single i 1))
      (fun l => f.hom.hom (x l)) k = f.hom.hom (X.subfieldTangentTensor t x k)
  rw [← ht]
  exact X.subfieldTangentTensor_natural f t x k

end SpecialModule

end Langlands.FormalGroup.LocalDivision
