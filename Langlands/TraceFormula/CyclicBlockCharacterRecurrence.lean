import Langlands.Global.HeckeCharacterTransport
import Langlands.Global.HeckeCharacterFiniteOrder
import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.ClassField.Global.IdeleClassNormGaloisProductProof
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! # Existence of character families satisfying the cyclic block recurrence -/

noncomputable section

set_option autoImplicit false

universe u v

namespace Langlands.TraceFormula.CyclicBlockSum

open NumberField Langlands.ClassField.Global Langlands.Global AdelicFunctoriality

section Field

variable {E : Type v} [Field E] [NumberField E] (σ : E ≃+* E) (ω : HeckeCharacter E)

/-- One backward step of the recurrence `η_(α+1) ∘ σ = ω η_α`: the character
`ω⁻¹ · (χ ∘ σ)`. -/
def recurrenceStep (χ : HeckeCharacter E) : HeckeCharacter E :=
  ω⁻¹ * HeckeCharacter.comap σ χ

/-- The iterated step, evaluated on idele classes. -/
theorem recurrenceStep_iterate_apply (χ : HeckeCharacter E) (m : ℕ)
    (y : IdeleClassGroup (𝓞 E) E) :
    ((recurrenceStep σ ω)^[m] χ) y =
      χ ((ideleClassEquiv σ)^[m] y) *
        (∏ j ∈ Finset.range m, ω ((ideleClassEquiv σ)^[j] y))⁻¹ := by
  induction m generalizing χ with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, Finset.prod_range_succ]
    change (ω ((ideleClassEquiv σ)^[m] y))⁻¹ *
        χ (ideleClassEquiv σ ((ideleClassEquiv σ)^[m] y)) *
        (∏ j ∈ Finset.range m, ω ((ideleClassEquiv σ)^[j] y))⁻¹ = _
    rw [← Function.iterate_succ_apply' (ideleClassEquiv σ), mul_inv]
    ac_rfl

/-- If the `d`-th power of the arithmetic automorphism is trivial on idele classes and `ω`
is trivial on the products `∏_(j<d) σ^j(y)`, then every character `η₀` starts a family
indexed by `ZMod d` satisfying `η_(α+1) ∘ σ = ω η_α`. -/
theorem exists_recurrence (d : ℕ) [NeZero d] (η₀ : HeckeCharacter E)
    (hσ : ∀ y, (ideleClassEquiv σ)^[d] y = y)
    (hω : ∀ y, ∏ j ∈ Finset.range d, ω ((ideleClassEquiv σ)^[j] y) = 1) :
    ∃ η : ZMod d → HeckeCharacter E, η 0 = η₀ ∧
      ∀ α : ZMod d, HeckeCharacter.comap σ (η (α + 1)) = ω * η α := by
  have hclose : Function.IsPeriodicPt (recurrenceStep σ ω) d η₀ := by
    refine ContinuousMonoidHom.ext fun y => ?_
    rw [recurrenceStep_iterate_apply, hσ, hω, inv_one, mul_one]
  refine ⟨fun α => (recurrenceStep σ ω)^[(-α).val] η₀, by simp, fun α => ?_⟩
  have hm : (-α).val = ((-(α + 1)).val + 1) % d := by
    rw [show -α = -(α + 1) + 1 by ring, ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  change HeckeCharacter.comap σ ((recurrenceStep σ ω)^[(-(α + 1)).val] η₀) =
    ω * (recurrenceStep σ ω)^[(-α).val] η₀
  rw [hm, hclose.iterate_mod_apply, Function.iterate_succ_apply', recurrenceStep,
    mul_inv_cancel_left]

end Field

section Galois

variable {F : Type u} {E : Type v} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]

omit [NumberField F] [IsGalois F E] in
/-- Iterating the arithmetic automorphism of a Galois element gives that of its power. -/
theorem ideleClassEquiv_iterate (σ : E ≃ₐ[F] E) (j : ℕ) (y : IdeleClassGroup (𝓞 E) E) :
    (ideleClassEquiv σ.toRingEquiv)^[j] y = relativeIdeleClassAut F E (σ ^ j) y := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', map_mul]
    rfl

/-- For a generator `σ` of the Galois group and a character `ω` of `C_E` whose restriction
to `C_F` is trivial on norms, every `η₀` starts a family indexed by `ZMod [E : F]`
satisfying the recurrence `η_(α+1) ∘ σ = ω η_α` of Clozel–Rajan (6.15). -/
theorem exists_recurrence_of_isTrivialOnNorm (σ : E ≃ₐ[F] E)
    (hgen : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) (ω : HeckeCharacter E)
    (hω : HeckeCharacter.IsTrivialOnNorm E (ω.comp (ideleClassInclusion (K := F) (L := E))))
    (η₀ : HeckeCharacter E) :
    ∃ η : ZMod (Module.finrank F E) → HeckeCharacter E, η 0 = η₀ ∧
      ∀ α, HeckeCharacter.comap σ.toRingEquiv (η (α + 1)) = ω * η α := by
  classical
  let _ : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
  have hd : orderOf σ = Module.finrank F E :=
    (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank F E)
  have : NeZero (Module.finrank F E) := ⟨(Module.finrank_pos (R := F) (M := E)).ne'⟩
  refine exists_recurrence σ.toRingEquiv ω (Module.finrank F E) η₀ (fun y => ?_) (fun y => ?_)
  · rw [ideleClassEquiv_iterate, ← hd, pow_orderOf_eq_one, map_one]
    rfl
  · simp only [ideleClassEquiv_iterate]
    rw [← hd]
    have himage := IsCyclic.image_range_orderOf hgen
    rw [← Finset.prod_image (f := fun τ => ω (relativeIdeleClassAut F E τ y))
      (fun i hi j hj h => pow_injOn_Iio_orderOf (Finset.mem_range.mp hi)
        (Finset.mem_range.mp hj) h), himage]
    have h1 : ω (ideleClassInclusion (K := F) (L := E) (ideleClassNorm (K := F) (L := E) y)) = 1 :=
      hω y
    rw [ideleClassNormGaloisProduct.{u, v} F E y] at h1
    rw [← h1]
    have hprod : ∀ s : Finset (E ≃ₐ[F] E),
        ω (∏ τ ∈ s, relativeIdeleClassAut F E τ y) = ∏ τ ∈ s, ω (relativeIdeleClassAut F E τ y) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp only [Finset.prod_empty, map_one]
      | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, ih]
    exact (hprod _).symm

end Galois

end Langlands.TraceFormula.CyclicBlockSum
