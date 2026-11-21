import Langlands.Geometry.FormalGroup.OrderActionCentralScalars
import Langlands.Geometry.FormalGroup.PiDivisible

/-! # Scalar kernels are preserved by changing the central scalar ring -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {C : Type c} [CommRing C] [Algebra C D] [Algebra C R]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}
variable (E : OrderAction D M)
variable (hs : ∀ (a : C) (x : σ → R),
  E.fiberTangent (RingHom.id R) (algebraMap C D a) x = algebraMap C R a • x)

/-- An integral scalar from the base acts by the actual scalar endomorphism. -/
theorem action_algebraMap_eq_scalarHom (a : O) : E.action (algebraMap O D a) = M.scalarHom a := by
  apply ModuleLaw.Hom.ext
  rw [E.extends_scalars, scalarHom, ModuleLaw.Hom.smul_toHom]
  exact (CommLaw.Hom.comp_id _).symm

/-- Changing the scalar ring leaves the actual kernel of each order element unchanged. -/
def centralOrder_kernelSetIso (a : D) :
    (E.action a).kernelSetFunctor ≅ ((E.centralOrder hs).action a).kernelSetFunctor :=
  NatIso.ofComponents (fun _ => (Equiv.refl _).toIso) (fun _ => rfl)

/-- The locally lifting condition uses the same nilpotent points after the scalar change. -/
theorem centralOrder_isFppfLocallySurjective (a : D)
    (h : (E.action a).IsFppfLocallySurjective) :
    ((E.centralOrder hs).action a).IsFppfLocallySurjective := h

private theorem action_pow_natCast (a n : ℕ) :
    E.action ((a : D) ^ n) = M.scalarHom ((a : O) ^ n) := by
  simpa only [map_pow (algebraMap O D), map_natCast (algebraMap O D)] using
    E.action_algebraMap_eq_scalarHom ((a : O) ^ n)

/-- The two scalar powers are literally the same formal map after forgetting the scalar ring. -/
theorem centralModule_scalarPower_toHom (a n : ℕ) :
    ((E.centralModule hs).scalarHom ((a : C) ^ n)).toHom =
      (M.scalarHom ((a : O) ^ n)).toHom := by
  rw [← (E.centralOrder hs).action_pow_natCast a n, ← E.action_pow_natCast a n]
  rfl

/-- A natural-number scalar power has the same actual kernel on either scalar law. -/
def centralModule_scalarPowerKernelIso (a n : ℕ) :
    (M.scalarHom ((a : O) ^ n)).kernelSetFunctor ≅
      ((E.centralModule hs).scalarHom ((a : C) ^ n)).kernelSetFunctor := by
  rw [← E.action_pow_natCast a n, ← (E.centralOrder hs).action_pow_natCast a n]
  exact E.centralOrder_kernelSetIso hs ((a : D) ^ n)

/-- Preserve the representing algebra and its rank when a natural-number scalar is retained. -/
def centralModule_scalarPowerFiniteKernel (a n : ℕ)
    (K : ModuleLaw.Hom.FiniteKernelModel (M.scalarHom ((a : O) ^ n))) :
    ModuleLaw.Hom.FiniteKernelModel ((E.centralModule hs).scalarHom ((a : C) ^ n)) where
  coordinateAlgebra := K.coordinateAlgebra
  finite := K.finite
  projective := K.projective
  represents := K.represents.ofIso (E.centralModule_scalarPowerKernelIso hs a n)

/-- Divisibility by a natural-number scalar only depends on its actual formal endomorphism. -/
theorem centralModule_isPiDivisible_natCast (a : ℕ) (hM : M.IsPiDivisible (a : O)) :
    (E.centralModule hs).IsPiDivisible (a : C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_natCast] using hM.base_nilpotent
  · intro A x
    let y : M.AlgebraPoint A := x
    obtain ⟨n, hn⟩ := hM.torsion A y
    refine ⟨n, ?_⟩
    have hy := (scalarHom_onAlgebraPoints M ((a : O) ^ n) A y).trans hn
    rw [← scalarHom_onAlgebraPoints (E.centralModule hs) ((a : C) ^ n) A x]
    change (((E.centralModule hs).scalarHom ((a : C) ^ n)).toHom.map
      (algebraMap R A)).onPoints x = 0
    rw [E.centralModule_scalarPower_toHom hs a n]
    exact hy
  · have hsource : (E.action ((a : D) ^ 1)).IsFppfLocallySurjective := by
      rw [E.action_pow_natCast, pow_one]
      exact hM.scalar_locallySurjective
    have ht := E.centralOrder_isFppfLocallySurjective hs ((a : D) ^ 1) hsource
    rw [(E.centralOrder hs).action_pow_natCast, pow_one] at ht
    exact ht
  · intro n
    obtain ⟨K⟩ := hM.scalarPower_finiteKernel n
    exact ⟨E.centralModule_scalarPowerFiniteKernel hs a n K⟩

/-- Changing the central scalar ring preserves the finite height for natural-number scalars. -/
theorem centralModule_hasPiHeight_natCast {a q h : ℕ} (hM : M.HasPiHeight (a : O) q h) :
    (E.centralModule hs).HasPiHeight (a : C) q h := by
  refine ⟨E.centralModule_isPiDivisible_natCast hs a hM.piDivisible, fun n => ?_⟩
  obtain ⟨K, hK⟩ := hM.scalarPower_rank n
  exact ⟨E.centralModule_scalarPowerFiniteKernel hs a n K, hK⟩

/-- The same rank formula transfers back to the original scalar-divisible law. -/
theorem hasPiHeight_natCast_of_centralModule {a q h : ℕ} (hM : M.IsPiDivisible (a : O))
    (hC : (E.centralModule hs).HasPiHeight (a : C) q h) : M.HasPiHeight (a : O) q h := by
  refine ⟨hM, fun n => ?_⟩
  obtain ⟨K, hK⟩ := hC.scalarPower_rank n
  exact ⟨{
    coordinateAlgebra := K.coordinateAlgebra
    finite := K.finite
    projective := K.projective
    represents := K.represents.ofIso (E.centralModule_scalarPowerKernelIso hs a n).symm
  }, hK⟩

end Langlands.FormalGroup.ModuleLaw.OrderAction
