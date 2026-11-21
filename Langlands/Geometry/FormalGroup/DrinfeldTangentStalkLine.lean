import Langlands.Geometry.FormalGroup.DrinfeldTangentComponentTransport
import Langlands.Geometry.FormalGroup.DrinfeldTangentFibreLine
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Rank one of the actual Drinfeld tangent components at every stalk -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision CentralSimple CategoryTheory
open scoped TensorProduct

universe u v s

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance tangentStalkLineLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B : Nilp.{u, max u v} 𝒪[K] π}
variable (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj) (Y : SpecialModule K D ι B.obj)

local notation "d" => CentralSimple.reducedDegree K D
local notation "W" => drinfeldTangentComponent ι Y.unramified χ ψ Y.order

/-- Every stalk of the actual tangent component has rank one. -/
theorem drinfeldTangentComponent_rankAtStalk (i : Fin d) (p : PrimeSpectrum B.obj) :
    Module.rankAtStalk (W i) p = 1 := by
  let : Module.Finite B.obj (W i) := drinfeldTangentComponent_finite ι Y.unramified χ ψ Y.order i
  let : Module.Projective B.obj (W i) :=
    drinfeldTangentComponent_projective ι Y.unramified χ ψ Y.order i
  let S := AlgebraicClosure p.asIdeal.ResidueField
  let : Algebra 𝒪[K] p.asIdeal.ResidueField :=
    Algebra.compHom p.asIdeal.ResidueField (algebraMap 𝒪[K] B.obj)
  let : IsScalarTower 𝒪[K] B.obj p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let φ : B.obj →ₐ[𝒪[K]] S := IsScalarTower.toAlgHom 𝒪[K] B.obj S
  have hS : IsNilpotent (algebraMap 𝒪[K] S π) := by
    have h : IsNilpotent (φ (algebraMap 𝒪[K] B.obj π)) := (B.nilpotent).map φ
    rwa [φ.commutes] at h
  let B' := Nilp.of 𝒪[K] π S hS
  let f : B ⟶ B' := ObjectProperty.homMk (CommAlgCat.ofHom φ)
  let ψ' := (Nilp.reductionMap (π := π) (A := B.obj) (B := B'.obj) φ).comp ψ
  let Y' := Y.mapSameUniverse φ
  have hφ : φ.toRingHom =
      (algebraMap p.asIdeal.ResidueField S).comp (algebraMap B.obj p.asIdeal.ResidueField) :=
    IsScalarTower.algebraMap_eq B.obj p.asIdeal.ResidueField S
  let : Algebra B.obj B'.obj := φ.toRingHom.toAlgebra
  let : IsDomain B'.obj := inferInstanceAs (IsDomain S)
  let W' := drinfeldTangentComponent ι (B := B') Y'.unramified χ ψ' Y'.order i
  let e₁ : B'.obj ⊗[B.obj] W i ≃ₗ[B'.obj] W' :=
    drinfeldTangentComponentBaseChange ι Y.unramified χ ψ Y.order f i
  let e₂ : W' ≃ₗ[B'.obj] B'.obj := drinfeldTangentFibreLine ι χ hS ψ' Y' i
  let e := e₁.trans e₂
  let q : PrimeSpectrum B'.obj := ⟨⊥, Ideal.isPrime_bot⟩
  have hq : q.comap (algebraMap B.obj B'.obj) = p := by
    apply PrimeSpectrum.ext
    change RingHom.ker φ.toRingHom = p.asIdeal
    rw [hφ, RingHom.ker_comp_of_injective _ (algebraMap p.asIdeal.ResidueField S).injective,
      Ideal.ker_algebraMap_residueField]
  rw [← hq, ← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv e,
    Module.rankAtStalk_self]
  rfl

/-- A choice of basis of the actual tangent component at a prime. -/
def drinfeldTangentStalkLine (i : Fin d) (p : PrimeSpectrum B.obj) :
    LocalizedModule p.asIdeal.primeCompl (W i) ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal := by
  letI : Module.Finite B.obj (W i) := drinfeldTangentComponent_finite ι Y.unramified χ ψ Y.order i
  letI : Module.Projective B.obj (W i) :=
    drinfeldTangentComponent_projective ι Y.unramified χ ψ Y.order i
  have hp : p ∈ Module.freeLocus B.obj (W i) := by
    rw [Module.freeLocus_eq_univ]
    exact Set.mem_univ _
  letI : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (W i)) := Module.mem_freeLocus.mp hp
  exact (Module.nonempty_linearEquiv_of_finrank_eq_one
    (drinfeldTangentComponent_rankAtStalk ι χ ψ Y i p)).some.symm

end Langlands.FormalGroup.LocalDivision
