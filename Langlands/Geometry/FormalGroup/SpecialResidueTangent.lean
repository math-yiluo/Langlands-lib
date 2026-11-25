import Langlands.Geometry.FormalGroup.DrinfeldSubfieldCharacters

/-! # Residue characters of the actual special tangent representation -/

noncomputable section

set_option autoImplicit false

universe u v s

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {k : Type v} [Field k] [Algebra 𝒪[K] k] [Algebra 𝓀[K] k]
  [IsScalarTower 𝒪[K] 𝓀[K] k]

local notation "C" => SubfieldIntegerRing K D ι
local notation "kC" => IsLocalRing.ResidueField C
local notation "d" => CentralSimple.reducedDegree K D

private local instance : IsLocalHom (algebraMap 𝒪[K] C) := subfieldIntegerAlgebra_isLocalHom ι

/-- A character of the unramified integer ring over a residue algebra factors through
its actual residue field. -/
def factorSubfieldCharacter (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (χ : C →ₐ[𝒪[K]] k) : kC →ₐ[𝓀[K]] k := by
  let : Module.Finite 𝒪[K] C := hL.2.1
  let : Algebra.Etale 𝒪[K] C := hL.2.2.1
  have hm : (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] C) =
      IsLocalRing.maximalIdeal C := Algebra.FormallyUnramified.map_maximalIdeal
  have hχ : IsLocalRing.maximalIdeal C ≤ RingHom.ker χ.toRingHom := by
    rw [← hm, Ideal.map_le_iff_le_comap]
    intro a ha
    change χ (algebraMap 𝒪[K] C a) = 0
    rw [χ.commutes, IsScalarTower.algebraMap_apply 𝒪[K] 𝓀[K] k]
    change algebraMap 𝓀[K] k (IsLocalRing.residue 𝒪[K] a) = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).mpr ha, map_zero]
  refine ⟨Ideal.Quotient.lift _ χ.toRingHom (fun _ ha => hχ ha), ?_⟩
  intro t
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective t
  rw [IsLocalRing.ResidueField.algebraMap_residue]
  change χ (algebraMap 𝒪[K] C a) = algebraMap 𝓀[K] k (IsLocalRing.residue 𝒪[K] a)
  rw [χ.commutes, IsScalarTower.algebraMap_apply 𝒪[K] 𝓀[K] k]
  rfl

@[simp]
theorem factorSubfieldCharacter_residue (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (χ : C →ₐ[𝒪[K]] k) (a : C) :
    factorSubfieldCharacter hL χ (IsLocalRing.residue C a) = χ a := rfl

variable {σ : Type} [Finite σ] {M : ModuleLaw 𝒪[K] k σ}
  {E : ModuleLaw.OrderAction (IntegerRing K D) M}
local notation "TangentDecomposition" =>
  ModuleLaw.OrderAction.TangentCharacterDecomposition E
    (AlgHom.toRingHom (subfieldIntegerInclusion K D ι)) d (RingHom.id k)

/-- The characters in the tangent decomposition are algebra maps over the actual central scalars. -/
def tangentSubfieldCharacter (t : TangentDecomposition) (i : Fin d) : C →ₐ[𝒪[K]] k where
  __ := t.characters i
  commutes' a := t.character_scalar ((subfieldIntegerInclusion K D ι).commutes a) i

/-- Index every residue-field embedding exactly once by the tangent eigenlines. -/
def tangentResidueCharacters (t : TangentDecomposition)
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) :
    Fin d ≃ (kC →ₐ[𝓀[K]] k) := by
  let e := fun i => factorSubfieldCharacter hL (tangentSubfieldCharacter t i)
  have he : Function.Injective e := by
    intro i j hij
    exact t.distinct (RingHom.ext fun a => AlgHom.congr_fun hij (IsLocalRing.residue C a))
  refine Equiv.ofBijective e ⟨he, ?_⟩
  let : Module.Finite 𝒪[K] C := hL.2.1
  let : Finite kC := IsLocalRing.ResidueField.finite_of_finite
    (R := 𝒪[K]) (S := C) inferInstance
  classical
  let : Fintype (kC →ₐ[𝓀[K]] k) := Fintype.ofFinite _
  have hcard := (card_algHom_le_finrank 𝓀[K] kC k).trans_eq (subfieldResidue_finrank ι hL)
  by_contra h
  have hlt := Fintype.card_lt_of_injective_not_surjective e he h
  rw [Fintype.card_fin, Fintype.card_eq_nat_card] at hlt
  exact (Nat.not_lt_of_le hcard) hlt

@[simp]
theorem tangentResidueCharacters_residue (t : TangentDecomposition)
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (i : Fin d) (a : C) :
    tangentResidueCharacters t hL i (IsLocalRing.residue C a) = t.characters i a := rfl

end Langlands.FormalGroup.LocalDivision
