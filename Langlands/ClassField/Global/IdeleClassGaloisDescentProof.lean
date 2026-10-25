import Langlands.ClassField.Global.IdeleClassGaloisDescentStatement
import Langlands.ClassField.Global.IdeleGaloisDescentProof
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-! # Galois descent for the actual idele-class inclusion -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

universe u v

variable {K : Type u} {E : Type v} [Field K] [Field E]
  [NumberField K] [NumberField E] [Algebra K E] [IsGalois K E]

private theorem principal_injective :
    Function.Injective (IdeleGroup.unitEmbedding (𝓞 E) E) := by
  intro a b hab
  apply Units.ext
  exact (AdeleRing.algebraMap_injective (𝓞 E) E)
    (congrArg Units.val hab)

omit [NumberField K] [IsGalois K E] in
private theorem principal_smul (σ : E ≃ₐ[K] E) (x : Eˣ) :
    IdeleGroup.unitEmbedding (𝓞 E) E (σ • x) =
      ideleEquiv σ.toRingEquiv (IdeleGroup.unitEmbedding (𝓞 E) E x) := by
  exact (ideleEquiv_diagonal σ.toRingEquiv x).symm

private theorem units_fixed_descent (x : Eˣ)
    (hx : ∀ σ : E ≃ₐ[K] E, σ • x = x) :
    ∃ y : Kˣ, Units.map (algebraMap K E).toMonoidHom y = x := by
  obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (x : E)).mpr
    (fun σ => congrArg Units.val (hx σ))
  have hy0 : y ≠ 0 := by
    intro h
    apply x.ne_zero
    rw [← hy, h, map_zero]
  exact ⟨Units.mk0 y hy0, Units.ext hy⟩

omit [IsGalois K E] in
/-- A fixed idele class admits a fixed idele representative, by Hilbert 90. -/
theorem exists_fixed_idele_representative (c : IdeleClassGroup (𝓞 E) E)
    (hc : ∀ σ : E ≃ₐ[K] E, relativeIdeleClassAut K E σ c = c) :
    ∃ a : IdeleGroup (𝓞 E) E,
      QuotientGroup.mk a = c ∧ ∀ σ : E ≃ₐ[K] E, ideleEquiv σ.toRingEquiv a = a := by
  classical
  induction c using QuotientGroup.induction_on with
  | H a =>
    have hf : ∀ σ : E ≃ₐ[K] E, ∃ x : Eˣ,
        IdeleGroup.unitEmbedding (𝓞 E) E x = ideleEquiv σ.toRingEquiv a / a := by
      intro σ
      exact QuotientGroup.eq_iff_div_mem.mp (hc σ)
    choose f hf using hf
    have hfc : groupCohomology.IsMulCocycle₁ f := by
      intro σ τ
      apply principal_injective
      rw [map_mul, principal_smul, hf, hf, hf, map_div]
      change ideleEquiv (τ.toRingEquiv.trans σ.toRingEquiv) a / a = _
      rw [ideleEquiv_trans]
      change ideleEquiv σ.toRingEquiv (ideleEquiv τ.toRingEquiv a) / a = _
      exact (div_mul_div_cancel _ _ _).symm
    obtain ⟨b, hb⟩ :=
      groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hfc
    refine ⟨a / IdeleGroup.unitEmbedding (𝓞 E) E b, ?_, ?_⟩
    · rw [QuotientGroup.mk_div]
      have hq : (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 E) E b) :
          IdeleClassGroup (𝓞 E) E) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ⟨b, rfl⟩
      rw [hq, div_one]
    · intro σ
      have h := congrArg (IdeleGroup.unitEmbedding (𝓞 E) E) (hb σ)
      rw [map_div, principal_smul, hf] at h
      rw [map_div, div_eq_div_iff_mul_eq_mul]
      exact (div_eq_div_iff_mul_eq_mul.mp h).symm.trans (mul_comm _ _)

/-- The idele descent clauses imply the actual idele-class descent clauses. -/
theorem ideleClass_descent_of_idele_descent
    (hinj : Function.Injective (ideleInclusion (K := K) (L := E)))
    (hdesc : ∀ a : IdeleGroup (𝓞 E) E,
      (∀ σ : E ≃ₐ[K] E, ideleEquiv σ.toRingEquiv a = a) ↔
        ∃ b : IdeleGroup (𝓞 K) K, ideleInclusion (K := K) (L := E) b = a) :
    Function.Injective (ideleClassInclusion (K := K) (L := E)) ∧
      ∀ c : IdeleClassGroup (𝓞 E) E,
        (∀ σ : E ≃ₐ[K] E, relativeIdeleClassAut K E σ c = c) ↔
          ∃ a : IdeleClassGroup (𝓞 K) K,
            ideleClassInclusion (K := K) (L := E) a = c := by
  constructor
  · apply (injective_iff_map_eq_one (ideleClassInclusion (K := K) (L := E)).toMonoidHom).mpr
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff _).mp hc
      have hxfix : ∀ σ : E ≃ₐ[K] E, σ • x = x := by
        intro σ
        apply principal_injective
        rw [principal_smul, hx]
        exact (hdesc _).mpr ⟨a, rfl⟩ σ
      obtain ⟨y, hy⟩ := units_fixed_descent x hxfix
      apply (QuotientGroup.eq_one_iff _).mpr
      refine ⟨y, hinj ?_⟩
      rw [ideleInclusion_diagonal, hy, hx]
      rfl
  · intro c
    constructor
    · intro hc
      obtain ⟨a, ha, hfix⟩ := exists_fixed_idele_representative c hc
      obtain ⟨b, hb⟩ := (hdesc a).mp hfix
      exact ⟨QuotientGroup.mk b, by rw [ideleClassInclusion_mk, hb, ha]⟩
    · rintro ⟨b, rfl⟩
      induction b using QuotientGroup.induction_on with
      | H b =>
        intro σ
        change QuotientGroup.mk (ideleEquiv σ.toRingEquiv (ideleInclusion b)) =
          (QuotientGroup.mk (ideleInclusion b) : IdeleClassGroup (𝓞 E) E)
        rw [(hdesc _).mpr ⟨b, rfl⟩ σ]

/-- Galois descent for the actual idele-class inclusion. -/
theorem ideleClassGaloisDescent : IdeleClassGaloisDescent.{u, v} := by
  intro K E _ _ _ _ _ _
  exact ideleClass_descent_of_idele_descent
    (ideleGaloisDescent K E).1 (ideleGaloisDescent K E).2

end Langlands.ClassField.Global
