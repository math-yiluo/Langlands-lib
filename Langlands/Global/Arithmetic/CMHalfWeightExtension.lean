import Langlands.Global.Arithmetic.CMInfinityExtension
import Langlands.Topology.ComplexCharacterExtension

/-! # Quotient extension for conjugate-inverse Hecke characters -/

noncomputable section

universe u

namespace Langlands.Global.CMHalfWeight

open NumberField

variable {K : Type u} [Field K] [NumberField K]

local instance : CommGroup (IdeleClasses K) := inferInstance

/-- The continuous quotient map by a subgroup of the actual idele-class group. -/
def classQuotientMap (N : Subgroup (IdeleClasses K)) :
    IdeleClasses K →ₜ* (IdeleClasses K) ⧸ N where
  toMonoidHom := QuotientGroup.mk' N
  continuous_toFun := QuotientGroup.continuous_mk

/-- Extend a prescribed infinity character through a quotient killing norms and
the specified local integral classes. The arithmetic input is compatibility on
an open subgroup of actual ideles containing the entire infinite factor. -/
theorem exists_heckeCharacter_of_open_kernel [IsCMField K]
    (N : Subgroup (IdeleClasses K))
    (hnorm : ∀ x : IdeleClasses K,
      x * AdelicFunctoriality.ideleClassComplexConj x ∈ N)
    (S : Finset (FinitePlace K))
    (hS : ∀ w ∈ S, ∀ a : (FiniteCompletion K w)ˣ,
      a ∈ (Submonoid.ofClass (w.adicCompletionIntegers K)).units →
        finiteClassInclusion K w a ∈ N)
    (H : Subgroup (Ideles K)) (hH : IsOpen (H : Set (Ideles K)))
    (hinf : ∀ x : (InfiniteAdeles K)ˣ, infiniteIdelesInclusion K x ∈ H)
    (η : (InfiniteAdeles K)ˣ →ₜ* ℂˣ)
    (hker : ∀ x : H, ideleClassMap K x ∈ N →
      η (CMUnramifiedInfinity.infinityProjection (x : Ideles K)) = 1) :
    ∃ φ : HeckeCharacter K,
      (∀ x, φ (AdelicFunctoriality.ideleClassComplexConj x) = (φ x)⁻¹) ∧
      φ.atInfinity = η ∧ ∀ w ∈ S, φ.IsUnramifiedAt w := by
  let q := classQuotientMap N
  let f : H →ₜ* (IdeleClasses K) ⧸ N :=
    (q.comp (ideleClassMap K)).comp ⟨H.subtype, continuous_subtype_val⟩
  have hf : IsOpenMap f :=
    (QuotientGroup.isOpenQuotientMap_mk (N := N)).isOpenMap.comp
      ((QuotientGroup.isOpenQuotientMap_mk
        (N := principalIdeles K)).isOpenMap.domRestrict hH)
  let ηH : H →ₜ* ℂˣ :=
    (η.comp CMUnramifiedInfinity.infinityProjection).comp
      ⟨H.subtype, continuous_subtype_val⟩
  have hfker : f.toMonoidHom.ker ≤ ηH.toMonoidHom.ker := by
    intro x hx
    apply hker x
    exact (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨χ, hχ⟩ :=
    Langlands.Topology.exists_continuous_complex_character_of_open_map f hf ηH hfker
  let φ : HeckeCharacter K := χ.comp q
  have hkill (x : IdeleClasses K) (hx : x ∈ N) : φ x = 1 := by
    change χ (q x) = 1
    have hqx : q x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
    rw [hqx, map_one]
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro x
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← map_mul, mul_comm]
    exact hkill _ (hnorm x)
  · apply ContinuousMonoidHom.ext
    intro x
    have h := DFunLike.congr_fun hχ ⟨infiniteIdelesInclusion K x, hinf x⟩
    change φ.atInfinity x =
      η (CMUnramifiedInfinity.infinityProjection (infiniteIdelesInclusion K x)) at h
    simpa only [CMUnramifiedInfinity.infinityProjection_inclusion] using h
  · intro w hw a ha
    exact hkill _ (hS w hw a ha)

end Langlands.Global.CMHalfWeight
