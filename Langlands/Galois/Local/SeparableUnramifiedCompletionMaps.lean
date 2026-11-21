import Langlands.Galois.Local.SeparableUnramifiedCompletion

/-! # Maps from completed unramified integers to nilpotent algebras -/

noncomputable section

set_option maxHeartbeats 800000

open IsLocalRing
open scoped ValuativeRel

namespace Langlands.LocalGalois.Separable.UnramifiedCompletion

universe u v

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- The natural algebra map into the completed maximal unramified integers. -/
def integerToCompletion : fixedFieldIntegers F →ₐ[↥𝒪[F]] Integers F where
  __ := algebraMap (fixedFieldIntegers F) (Integers F)
  commutes' _ := rfl

/-- The map to the completion induces an isomorphism of residue algebras. -/
def residueAlgEquiv : ResidueField (fixedFieldIntegers F) ≃ₐ[↥𝒪[F]] Residue F :=
  { residueEquiv F with commutes' := fun _ => rfl }

@[simp]
theorem residueAlgEquiv_residue (x : fixedFieldIntegers F) :
    residueAlgEquiv F (residue _ x) = residue _ (integerToCompletion F x) := rfl

variable {B : Type v} [CommRing B] [Algebra ↥𝒪[F] B]
variable {π : 𝒪[F]} (hπ : Irreducible π)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem map_eq_zero_of_mem_span_uniformizer_pow
    {A : Type u} [CommRing A] [Algebra ↥𝒪[F] A]
    (f : A →ₐ[↥𝒪[F]] B) {n : ℕ} (hn : (algebraMap ↥𝒪[F] B π) ^ n = 0) {x : A}
    (hx : x ∈ Ideal.span {algebraMap ↥𝒪[F] A π} ^ n) : f x = 0 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, f.commutes, hn, zero_mul]

include hπ in
private theorem mem_maximalIdeal_pow_of_evalₐ_eq_zero
    {n : ℕ} {x : Integers F}
    (hx : AdicCompletion.evalₐ (maximalIdeal (fixedFieldIntegers F)) n x = 0) :
    x ∈ maximalIdeal (Integers F) ^ n := by
  let S := fixedFieldIntegers F
  let m := maximalIdeal S
  have fg : m.FG := by
    rw [show m = maximalIdeal (fixedFieldIntegers F) from rfl,
      maximalIdeal_before_eq_span_uniformizer F hπ]
    exact Submodule.fg_span_singleton _
  rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg, ← Ideal.map_pow,
    ← Submodule.restrictScalars_mem S, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
  rw [← AdicCompletion.factor_evalₐ_eq_eval m x (by simp), hx, map_zero]

include hπ in
private theorem restrict_integerToCompletion_bijective (hB : IsNilpotent (algebraMap ↥𝒪[F] B π)) :
    Function.Bijective (fun f : Integers F →ₐ[↥𝒪[F]] B => f.comp (integerToCompletion F)) := by
  obtain ⟨n, hn⟩ := hB
  let S := fixedFieldIntegers F
  let m := maximalIdeal S
  let i := integerToCompletion F
  refine ⟨?_, ?_⟩
  · intro f g heq
    ext x
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ m n x)
    have hxy : AdicCompletion.evalₐ m n (x - i y) = 0 := by
      rw [map_sub, show AdicCompletion.evalₐ m n (i y) = Ideal.Quotient.mk (m ^ n) y
        from AdicCompletion.evalₐ_of m n y, hy, sub_self]
    have hx : x - i y ∈ Ideal.span {algebraMap ↥𝒪[F] (Integers F) π} ^ n := by
      rw [← maximalIdeal_eq_span_uniformizer F hπ]
      exact mem_maximalIdeal_pow_of_evalₐ_eq_zero F hπ hxy
    have hf : f x = f (i y) := by
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact map_eq_zero_of_mem_span_uniformizer_pow F f hn hx
    have hg : g x = g (i y) := by
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact map_eq_zero_of_mem_span_uniformizer_pow F g hn hx
    exact hf.trans ((AlgHom.congr_fun heq y).trans hg.symm)
  · intro f
    let f' : S ⧸ m ^ n →ₐ[↥𝒪[F]] B := Ideal.Quotient.liftₐ (m ^ n) f (by
      intro x hx
      have h : m = Ideal.span {algebraMap ↥𝒪[F] S π} :=
        maximalIdeal_before_eq_span_uniformizer F hπ
      rw [h] at hx
      exact map_eq_zero_of_mem_span_uniformizer_pow F f hn hx)
    let q : Integers F →ₐ[↥𝒪[F]] S ⧸ m ^ n :=
      { (AdicCompletion.evalₐ m n).toRingHom with
        commutes' a := AdicCompletion.evalₐ_of m n (algebraMap ↥𝒪[F] S a) }
    refine ⟨f'.comp q, ?_⟩
    ext x
    change f' (AdicCompletion.evalₐ m n (AdicCompletion.of m S x)) = f x
    rw [AdicCompletion.evalₐ_of]
    rfl

/-- Restriction from the completed integers is a bijection on algebra maps to
any base algebra in which the original uniformizer acts nilpotently. -/
def integerMapEquiv (hB : IsNilpotent (algebraMap ↥𝒪[F] B π)) :
    (Integers F →ₐ[↥𝒪[F]] B) ≃ (fixedFieldIntegers F →ₐ[↥𝒪[F]] B) :=
  Equiv.ofBijective (fun f => f.comp (integerToCompletion F))
    (restrict_integerToCompletion_bijective F hπ hB)

@[simp]
theorem integerMapEquiv_apply (hB : IsNilpotent (algebraMap ↥𝒪[F] B π))
    (f : Integers F →ₐ[↥𝒪[F]] B) :
    integerMapEquiv F hπ hB f = f.comp (integerToCompletion F) := rfl

end Langlands.LocalGalois.Separable.UnramifiedCompletion
