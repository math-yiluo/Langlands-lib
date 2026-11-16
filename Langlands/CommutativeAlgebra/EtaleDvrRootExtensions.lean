import Langlands.CommutativeAlgebra.EtaleDvrExtensions
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Unramified.Field
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Local etale DVR extensions with a prescribed residue root -/

noncomputable section

universe u v

open Polynomial IsLocalRing Module

namespace Langlands.CommutativeAlgebra.EtaleDvrExtensions

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A simple root at a field point lifts to a local essentially etale DVR extension. -/
theorem exists_root_extension (f : R[X]) (hf : f.Monic)
    {K : Type v} [Field K] (φ : R →+* K) (hφ : RingHom.ker φ = maximalIdeal R)
    (x : K) (hx : f.eval₂ φ x = 0) (hx' : f.derivative.eval₂ φ x ≠ 0) :
    ∃ (T : Type u) (_ : CommRing T) (_ : IsDomain T) (_ : IsDiscreteValuationRing T)
      (_ : Algebra R T) (_ : IsLocalHom (algebraMap R T))
      (_ : Algebra.EssFiniteType R T) (_ : Algebra.FormallyUnramified R T)
      (_ : Module.Flat R T) (y : T) (ψ : T →+* K),
      aeval y f = 0 ∧ ψ.comp (algebraMap R T) = φ ∧ ψ y = x := by
  let : Algebra R K := φ.toAlgebra
  let E : StandardEtalePair R := ⟨f, hf, derivative f, ⟨1, 0, 1, by simp⟩⟩
  let A := E.Ring
  have hE : E.HasMap x := ⟨hx, isUnit_iff_ne_zero.mpr hx'⟩
  let ρ : A →ₐ[R] K := E.lift x hE
  let q : Ideal A := RingHom.ker ρ.toRingHom
  have : q.IsPrime := RingHom.ker_isPrime _
  let T := Localization.AtPrime q
  let ψ : T →+* K := IsLocalization.lift (S := T)
    (fun z : q.primeCompl => isUnit_iff_ne_zero.mpr z.property)
  have hψ (a : A) : ψ (algebraMap A T a) = ρ a :=
    IsLocalization.lift_eq ..
  have hcomp : ψ.comp (algebraMap R T) = φ := by
    ext r
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R A T, hψ, ρ.commutes]
    rfl
  have : IsLocalHom (algebraMap R T) := by
    constructor
    intro r hr
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro h
    have h0 : φ r = 0 := by
      rw [← RingHom.mem_ker, hφ]
      exact h
    have := (hr.map ψ).ne_zero
    exact this (by rw [← RingHom.comp_apply, hcomp, h0])
  have : Algebra.EssFiniteType R T := Algebra.EssFiniteType.comp R A T
  have : Algebra.FormallyUnramified R T :=
    Algebra.FormallyUnramified.comp R A T
  have : Module.Flat R T := Module.Flat.trans R A T
  have : IsDomain T := isDomain R T
  have : IsDiscreteValuationRing T := isDiscreteValuationRing R T
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, algebraMap A T E.X, ψ, ?_, hcomp, ?_⟩
  · rw [aeval_algebraMap_apply, E.hasMap_X.1, map_zero]
  · rw [hψ, E.lift_X]

section Embedding

variable {R}
variable (T : Type*) [CommRing T] [IsDomain T] [Algebra R T]
  [Algebra.EssFiniteType R T] [Algebra.FormallyUnramified R T] [Module.Flat R T]
  (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [IsTorsionFree R Ω]

/-- An essentially finite type unramified domain extension embeds in an algebraically
closed overfield of its DVR base. -/
theorem exists_injective_algHom :
    ∃ e : T →ₐ[R] Ω, Function.Injective e := by
  let K := FractionRing R
  let L := FractionRing T
  let : Algebra K L := FractionRing.liftAlgebra R L
  have : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  let : Algebra K Ω := FractionRing.liftAlgebra R Ω
  have : IsScalarTower R K Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  have : Algebra.FormallyUnramified R L :=
    Algebra.FormallyUnramified.comp R T L
  have : Algebra.FormallyUnramified K L :=
    Algebra.FormallyUnramified.of_restrictScalars R K L
  have : Algebra.EssFiniteType R L := Algebra.EssFiniteType.comp R T L
  have : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp R K L
  have : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  let e : L →ₐ[K] Ω := IsAlgClosed.lift
  let j : T →ₐ[R] Ω :=
    (e.restrictScalars R).comp ((Algebra.ofId T L).restrictScalars R)
  exact ⟨j, e.injective.comp (IsFractionRing.injective T L)⟩

end Embedding

end Langlands.CommutativeAlgebra.EtaleDvrExtensions
