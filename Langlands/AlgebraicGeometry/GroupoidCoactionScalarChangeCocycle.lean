import Langlands.AlgebraicGeometry.GroupoidCoactionIdealRestriction
import Langlands.AlgebraicGeometry.GroupoidCoactionCocycleUniversal
import Langlands.AlgebraicGeometry.GroupoidCoactionIdealDevissage

/-! # Cocycle vanishing under surjective scalar change -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

section ScalarChange

variable {B S C D : Type u}
  [CommRing B] [CommRing S] [CommRing C] [CommRing D]
  [Algebra B S] [Algebra B C] [Algebra B D] [Algebra S D] [IsScalarTower B S D]
variable {M : Type v} [AddCommGroup M] [Module B M] [Module S M]
  [IsScalarTower B S M]
variable {t : B →+* C} {τ : S →+* D}

/-- Surjective scalar change sends flat-test cocycles to flat-test cocycles.
The original cocycle is specialized at arbitrary test algebras before changing
the tensor base, so no flatness of the scalar map is needed. -/
theorem IsOneCocycle.scalarChange {θ : GroupoidCoaction t M} {x : C ⊗[B] M}
    (hx : θ.IsOneCocycle x) (hE : RingEtaleEquivalenceRelation t)
    (f : C →ₐ[B] D) (hS : Function.Surjective (algebraMap B S))
    (hτ : τ.comp (algebraMap B S) = f.toRingHom.comp t) :
    (scalarChange θ f hS hτ).IsOneCocycle (scalarChangeTensor (S := S) f x) := by
  intro T _ _ _ φ₁ φ₂ φ₃ h h₃
  let : Algebra B T := ((algebraMap S T).comp (algebraMap B S)).toAlgebra
  let : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hB : (φ₁.comp f.toRingHom).comp (algebraMap B C) =
      ((φ₂.restrictScalars B).comp f).toRingHom.comp t := by
    ext b
    change φ₁ (f (algebraMap B C b)) = φ₂ (f (t b))
    rw [f.commutes, IsScalarTower.algebraMap_apply B S D,
      ← scalarChange_target_apply f hτ]
    exact congrArg (fun q : S →+* T => q (algebraMap B S b)) h
  have hB₃ : ((φ₃.restrictScalars B).comp f).toRingHom.comp t =
      (φ₁.comp f.toRingHom).comp t := by
    ext b
    change φ₃ (f (t b)) = φ₁ (f (t b))
    rw [← scalarChange_target_apply f hτ]
    exact congrArg (fun q : S →+* T => q (algebraMap B S b)) h₃
  change LinearMap.rTensor M φ₃.toLinearMap (scalarChangeTensor (S := S) f x) =
    LinearMap.rTensor M φ₂.toLinearMap (scalarChangeTensor (S := S) f x) + _
  rw [← scalarChangeTensor_rTensor,
    hx.specialize hE (φ₁.comp f.toRingHom) ((φ₂.restrictScalars B).comp f)
      ((φ₃.restrictScalars B).comp f) hB hB₃,
    map_add, scalarChangeTensor_rTensor,
    scalarChangeTensor_coactionCompose θ f hS hτ φ₁ φ₂ h hB]
  rfl

/-- Scalar change commutes with degree-zero coboundaries. -/
lemma scalarChange_coboundary (θ : GroupoidCoaction t M)
    (f : C →ₐ[B] D) (hS : Function.Surjective (algebraMap B S))
    (hτ : τ.comp (algebraMap B S) = f.toRingHom.comp t) (m : M) :
    (scalarChange θ f hS hτ).coboundary m =
      scalarChangeTensor (S := S) f (θ.coboundary m) := by
  simp [coboundary_apply]

/-- Vanishing reflects along scalar change when its map on the coefficient
tensor is injective. -/
theorem oneCohomologyVanishes_of_scalarChange (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M)
    (f : C →ₐ[B] D) (hS : Function.Surjective (algebraMap B S))
    (hτ : τ.comp (algebraMap B S) = f.toRingHom.comp t)
    (hinj : Function.Injective (scalarChangeTensor (M := M) (S := S) f))
    (hvan : (scalarChange θ f hS hτ).OneCohomologyVanishes) :
    θ.OneCohomologyVanishes := by
  intro x hx
  obtain ⟨m, hm⟩ := hvan _ (hx.scalarChange hE f hS hτ)
  refine ⟨m, hinj ?_⟩
  rw [← scalarChange_coboundary θ f hS hτ]
  exact hm

end ScalarChange

section Ideal

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M : Type v} [AddCommGroup M] [Module B M]

/-- The ideal-restricted quotient coaction reflects degree-one vanishing. -/
theorem idealQuotient_oneCohomologyVanishes_of_idealRestriction
    (hE : RingEtaleEquivalenceRelation t) (θ : GroupoidCoaction t M)
    (I : Ideal B) (hI : I.map (algebraMap B C) = I.map t)
    (hvan : (idealRestriction θ I hI).OneCohomologyVanishes) :
    (idealQuotient θ I hI.ge).OneCohomologyVanishes := by
  let : IsScalarTower B (B ⧸ I) (M ⧸ (I • ⊤ : Submodule B M)) :=
    quotientModule_scalarTower I
  exact oneCohomologyVanishes_of_scalarChange hE _ _ Ideal.Quotient.mk_surjective
    (RingEtaleEquivalenceRelation.quotientTarget_comp_mk I hI)
    (idealRestriction_tensor_injective (M := M) I) hvan

/-- Extension of an annihilating ideal annihilates the coefficient tensor. -/
lemma map_source_le_annihilator_tensor (I : Ideal B)
    (hI : I ≤ Module.annihilator B M) :
    I.map (algebraMap B C) ≤ Module.annihilator C (C ⊗[B] M) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  apply Module.mem_annihilator.mpr
  intro x
  induction x with
  | tmul c m =>
    change algebraMap B C a • (c ⊗ₜ[B] m) = 0
    rw [IsScalarTower.algebraMap_smul, ← tmul_smul,
      Module.mem_annihilator.mp (hI ha) m, tmul_zero]
  | add x y hx hy => simp only [smul_add, hx, hy, add_zero]

/-- Reducing the tensor ring and tensor base loses no information on any
module annihilated by the ideal. -/
lemma scalarChangeTensor_quotient_injective (I : Ideal B)
    [Module (B ⧸ I) M] [IsScalarTower B (B ⧸ I) M]
    (hI : I ≤ Module.annihilator B M) :
    Function.Injective (scalarChangeTensor (M := M) (S := B ⧸ I)
      (Ideal.Quotient.mkₐ B (I.map (algebraMap B C)))) := by
  let D := C ⧸ I.map (algebraMap B C)
  let f : C →ₐ[B] D := Ideal.Quotient.mkₐ B (I.map (algebraMap B C))
  let : TensorProduct.CompatibleSMul B (B ⧸ I) D M :=
    ⟨fun s c m => by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective s
      change (algebraMap B (B ⧸ I) b • c) ⊗ₜ[B] m =
        c ⊗ₜ[B] (algebraMap B (B ⧸ I) b • m)
      rw [IsScalarTower.algebraMap_smul (B ⧸ I),
        IsScalarTower.algebraMap_smul (B ⧸ I)]
      exact TensorProduct.smul_tmul b c m⟩
  let e : D ⊗[B] M ≃ₗ[B] D ⊗[B ⧸ I] M :=
    TensorProduct.equivOfCompatibleSMul (B ⧸ I) B B D M
  have hmap (x : C ⊗[B] M) :
      scalarChangeTensor (S := B ⧸ I) f x =
        e (LinearMap.rTensor M f.toLinearMap x) := by
    induction x with
    | tmul c m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  apply rTensor_quotient_injective_of_annihilator
    (I.map (algebraMap B C)) (map_source_le_annihilator_tensor I hI)
  apply e.injective
  exact (hmap x).symm.trans (hxy.trans (hmap y))

/-- A coaction on a module with a compatible quotient-ring action, viewed on
the quotient relation. -/
def annihilatorRestriction (θ : GroupoidCoaction t M) (I : Ideal B)
    (hI : IsInvariantIdeal t I)
    [Module (B ⧸ I) M] [IsScalarTower B (B ⧸ I) M] :
    GroupoidCoaction (RingEtaleEquivalenceRelation.quotientTarget I hI.symm) M :=
  scalarChange θ (Ideal.Quotient.mkₐ B (I.map (algebraMap B C)))
    Ideal.Quotient.mk_surjective
    (RingEtaleEquivalenceRelation.quotientTarget_comp_mk I hI.symm)

/-- Finite-module vanishing on the quotient relation implies vanishing for
finite coactions annihilated by its defining ideal. -/
theorem finiteAnnihilatorVanishing_of_quotient
    (hE : RingEtaleEquivalenceRelation t) (I : Ideal B) (hI : IsInvariantIdeal t I)
    (hvan : ∀ (N : Type v) [AddCommGroup N] [Module (B ⧸ I) N]
      [Module.Finite (B ⧸ I) N]
      (θN : GroupoidCoaction (RingEtaleEquivalenceRelation.quotientTarget I hI.symm) N),
      θN.OneCohomologyVanishes) :
    FiniteAnnihilatorVanishing.{u, v} t I := by
  intro M _ _ _ θ hM
  have htor : Module.IsTorsionBySet B M I :=
    (Module.isTorsionBySet_iff_subset_annihilator B M).mpr hM
  let : Module (B ⧸ I) M := htor.module
  let : IsScalarTower B (B ⧸ I) M := htor.isScalarTower
  let : Module.Finite (B ⧸ I) M := Module.Finite.of_restrictScalars_finite B (B ⧸ I) M
  exact oneCohomologyVanishes_of_scalarChange hE θ
    (Ideal.Quotient.mkₐ B (I.map (algebraMap B C))) Ideal.Quotient.mk_surjective
    (RingEtaleEquivalenceRelation.quotientTarget_comp_mk I hI.symm)
    (scalarChangeTensor_quotient_injective I hM) (hvan M (annihilatorRestriction θ I hI))

end Ideal

end Langlands.AlgebraicGeometry.GroupoidCoaction
