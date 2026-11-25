import Langlands.ClassFieldTheory.Local.Artin.FiniteArtin
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Arithmetic Artin lifts in the absolute Galois group of a local field

This file belongs to the Library. For a nonarchimedean local field `K`, a separable closure `Ksep`
and `a ∈ Kˣ`, an element `σ ∈ Gal(Ksep/K)` is an **arithmetic Artin lift** of `a`
(`IsArithmeticArtinLift K Ksep a σ`) when its restriction to every finite abelian subextension
`L` of `Ksep / K` is the arithmetic Artin symbol `arithmeticFiniteArtin K L a` of `FiniteArtin.lean`.
This is the notion the cup symbol of local Galois cohomology is stated with; it describes the
image of `a` in `Gal(Kᵃᵇ/K)` under the arithmetic Artin map without constructing that map.

## Main declarations

* `IsArithmeticArtinLift K Ksep a σ`.
* `IsArithmeticArtinLift.restrictNormalHom_eq`: the same holds for every finite abelian extension
  `L` of `K` with a `K`-embedding into `Ksep` (not only for subfields).
* `IsArithmeticArtinLift.mul`, `.inv`, `.one`: lifts multiply.
* `exists_isArithmeticArtinLift`: every `a` has an arithmetic Artin lift (compactness of
  `Gal(Ksep/K)` and the compatibility of the finite Artin maps under restriction).
-/

noncomputable section

universe u v w

namespace Langlands.ClassFieldTheory.Local.Artin

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (Ksep : Type v) [Field Ksep] [Algebra K Ksep]

/-- `σ ∈ Gal(Ksep/K)` is an arithmetic Artin lift of `a ∈ Kˣ`: on every finite abelian
subextension `L` of `Ksep / K` it restricts to the arithmetic Artin symbol of `a`. -/
def IsArithmeticArtinLift (a : Kˣ) (σ : Gal(Ksep/K)) : Prop :=
  ∀ (L : IntermediateField K Ksep) [FiniteDimensional K L] [IsAbelianGalois K L],
    AlgEquiv.restrictNormalHom L σ = arithmeticFiniteArtin K L a

variable {K Ksep}

namespace IsArithmeticArtinLift

/-- An arithmetic Artin lift restricts to the arithmetic Artin symbol on every finite abelian
extension `L` of `K` embedded in `Ksep`. -/
theorem restrictNormalHom_eq {a : Kˣ} {σ : Gal(Ksep/K)} (h : IsArithmeticArtinLift K Ksep a σ)
    (L : Type w) [Field L] [Algebra K L] [Algebra L Ksep] [IsScalarTower K L Ksep]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    AlgEquiv.restrictNormalHom L σ = arithmeticFiniteArtin K L a := by
  let f := IsScalarTower.toAlgHom K L Ksep
  let L' : IntermediateField K Ksep := f.fieldRange
  let e : L ≃ₐ[K] L' := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional K L' := e.toLinearEquiv.finiteDimensional
  have : IsAbelianGalois K L' := IsAbelianGalois.of_algHom e.symm.toAlgHom
  let : Algebra L L' := e.toRingHom.toAlgebra
  have : IsScalarTower K L L' := IsScalarTower.of_algHom e.toAlgHom
  have : IsScalarTower L L' Ksep := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L L' σ, h L',
    restrictNormalHom_arithmeticFiniteArtin K L L' a]

theorem one : IsArithmeticArtinLift K Ksep 1 1 := fun L _ _ => by
  rw [map_one, map_one]

theorem mul {a b : Kˣ} {σ τ : Gal(Ksep/K)} (ha : IsArithmeticArtinLift K Ksep a σ)
    (hb : IsArithmeticArtinLift K Ksep b τ) : IsArithmeticArtinLift K Ksep (a * b) (σ * τ) :=
  fun L _ _ => by rw [map_mul, map_mul, ha L, hb L]

theorem inv {a : Kˣ} {σ : Gal(Ksep/K)} (ha : IsArithmeticArtinLift K Ksep a σ) :
    IsArithmeticArtinLift K Ksep a⁻¹ σ⁻¹ :=
  fun L _ _ => by rw [map_inv, map_inv, ha L]

end IsArithmeticArtinLift

section Existence

variable (K Ksep) [IsGalois K Ksep]

/-- The set of elements of `Gal(Ksep/K)` restricting to the arithmetic Artin symbol of `a` on one
finite abelian subextension `L`. -/
private def liftSet (a : Kˣ)
    (L : {L : IntermediateField K Ksep // FiniteDimensional K L ∧ IsAbelianGalois K L}) :
    Set Gal(Ksep/K) :=
  haveI := L.2.1
  haveI := L.2.2
  {σ | AlgEquiv.restrictNormalHom L.1 σ = arithmeticFiniteArtin K L.1 a}

/-- Every element of `Kˣ` has an arithmetic Artin lift in `Gal(Ksep/K)`. -/
theorem exists_isArithmeticArtinLift (a : Kˣ) : ∃ σ : Gal(Ksep/K), IsArithmeticArtinLift K Ksep a σ := by
  let ι := {L : IntermediateField K Ksep // FiniteDimensional K L ∧ IsAbelianGalois K L}
  have : Nonempty ι := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  have hdir : Directed (· ⊇ ·) (liftSet K Ksep a) := by
    rintro ⟨L₁, h₁, h₁'⟩ ⟨L₂, h₂, h₂'⟩
    have : FiniteDimensional K (L₁ ⊔ L₂ : IntermediateField K Ksep) := inferInstance
    have : IsAbelianGalois K (L₁ ⊔ L₂ : IntermediateField K Ksep) := inferInstance
    refine ⟨⟨L₁ ⊔ L₂, inferInstance, inferInstance⟩, ?_, ?_⟩
    · intro σ hσ
      change AlgEquiv.restrictNormalHom L₁ σ = arithmeticFiniteArtin K L₁ a
      change AlgEquiv.restrictNormalHom (L₁ ⊔ L₂ : IntermediateField K Ksep) σ =
        arithmeticFiniteArtin K (L₁ ⊔ L₂ : IntermediateField K Ksep) a at hσ
      let : Algebra L₁ (L₁ ⊔ L₂ : IntermediateField K Ksep) :=
        (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra
      have : IsScalarTower K L₁ (L₁ ⊔ L₂ : IntermediateField K Ksep) :=
        IsScalarTower.of_algHom (IntermediateField.inclusion le_sup_left)
      have : IsScalarTower L₁ (L₁ ⊔ L₂ : IntermediateField K Ksep) Ksep :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L₁
        (L₁ ⊔ L₂ : IntermediateField K Ksep) σ, hσ,
        restrictNormalHom_arithmeticFiniteArtin K L₁ (L₁ ⊔ L₂ : IntermediateField K Ksep) a]
    · intro σ hσ
      change AlgEquiv.restrictNormalHom L₂ σ = arithmeticFiniteArtin K L₂ a
      change AlgEquiv.restrictNormalHom (L₁ ⊔ L₂ : IntermediateField K Ksep) σ =
        arithmeticFiniteArtin K (L₁ ⊔ L₂ : IntermediateField K Ksep) a at hσ
      let : Algebra L₂ (L₁ ⊔ L₂ : IntermediateField K Ksep) :=
        (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra
      have : IsScalarTower K L₂ (L₁ ⊔ L₂ : IntermediateField K Ksep) :=
        IsScalarTower.of_algHom (IntermediateField.inclusion le_sup_right)
      have : IsScalarTower L₂ (L₁ ⊔ L₂ : IntermediateField K Ksep) Ksep :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L₂
        (L₁ ⊔ L₂ : IntermediateField K Ksep) σ, hσ,
        restrictNormalHom_arithmeticFiniteArtin K L₂ (L₁ ⊔ L₂ : IntermediateField K Ksep) a]
  have hclosed : ∀ L, IsClosed (liftSet K Ksep a L) := by
    rintro ⟨L, h, h'⟩
    exact isClosed_singleton.preimage (InfiniteGalois.restrictNormalHom_continuous L)
  have hne : ∀ L, (liftSet K Ksep a L).Nonempty := by
    rintro ⟨L, h, h'⟩
    exact AlgEquiv.restrictNormalHom_surjective Ksep (arithmeticFiniteArtin K L a)
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (liftSet K Ksep a) hdir hne (fun L => (hclosed L).isCompact) hclosed
  refine ⟨σ, fun L hL hL' => ?_⟩
  exact Set.mem_iInter.mp hσ ⟨L, hL, hL'⟩

end Existence

end Langlands.ClassFieldTheory.Local.Artin
