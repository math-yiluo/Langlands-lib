import Langlands.Global.AdelicGLStandardCompact
import Langlands.Global.FiniteAdelicGL.RestrictedProduct
import Langlands.Group.GL.TriangularParabolic
import Langlands.Representation.Whittaker.Iwasawa

/-! # Iwasawa decomposition of the actual adelic `GL(n)` for the standard compact subgroup -/

noncomputable section

universe u

open scoped Matrix RestrictedProduct Pointwise

namespace Langlands.Global.PrimitiveAdelicHeight

open Langlands.LinearAlgebra.TriangularUnitary

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-! ## Finite places -/

/-- Iwasawa decomposition at a finite place: every element of `GL(n, F_v)` is an upper
triangular matrix times an element of `GL(n, O_v)`. -/
theorem exists_local_iwasawa (v : FinitePlace F) (g : FiniteLocalGL F n v) :
    ∃ b k : FiniteLocalGL F n v, g = b * k ∧ b.val.IsUpperTriangular ∧
      k ∈ FiniteAdelicGL.localIntegral F n v := by
  cases n with
  | zero =>
    refine ⟨g, 1, (mul_one g).symm, ?_, one_mem _⟩
    intro i
    exact i.elim0
  | succ m =>
    obtain ⟨b, hb, k, hk, rfl⟩ := GeneralLinear.Iwasawa.exists_upperTriangular_mul
      (Valued.v : Valuation (FiniteCompletion F v) _) g
    refine ⟨b, k, rfl, hb, ?_⟩
    obtain ⟨k', rfl⟩ := hk
    rw [FiniteAdelicGL.mem_localIntegral]
    refine ⟨fun i j => (k' i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact (k'⁻¹ i j).2

/-- Iwasawa decomposition of the actual finite adelic `GL(n)`: every element is an upper
triangular matrix times an element of `FiniteAdelicGL.standardIntegral F n`. -/
theorem exists_finite_iwasawa (g : FiniteAdelicGL F n) :
    ∃ β κ : FiniteAdelicGL F n, g = β * κ ∧ β.val.IsUpperTriangular ∧
      κ ∈ FiniteAdelicGL.standardIntegral F n := by
  classical
  choose b k hbk hb hk using fun v =>
    exists_local_iwasawa F n v (FiniteAdelicGL.localProjection F n v g)
  let b' : (v : FinitePlace F) → FiniteLocalGL F n v := fun v =>
    if FiniteAdelicGL.localProjection F n v g ∈ FiniteAdelicGL.localIntegral F n v then 1
    else b v
  have hb' : ∀ᶠ v in Filter.cofinite, b' v ∈ FiniteAdelicGL.localIntegral F n v := by
    filter_upwards [FiniteAdelicGL.eventually_localIntegral F n g] with v hv
    have h1 : b' v = 1 := ite_eq_left_iff.mpr fun h => absurd hv h
    rw [h1]
    exact one_mem _
  let β := (FiniteAdelicGL.restrictedProductEquiv F n).symm ⟨b', hb'⟩
  have hβv : ∀ v, FiniteAdelicGL.localProjection F n v β = b' v := fun v => by
    rw [← FiniteAdelicGL.restrictedProductEquiv_apply,
      show FiniteAdelicGL.restrictedProductEquiv F n β = ⟨b', hb'⟩ from
        ContinuousMulEquiv.apply_symm_apply _ _]
    rfl
  refine ⟨β, β⁻¹ * g, (mul_inv_cancel_left β g).symm, ?_, ?_⟩
  · intro i j hij
    refine IsDedekindDomain.FiniteAdeleRing.ext _ fun v => ?_
    change b' v i j = 0
    simp only [b']
    split_ifs
    · exact Matrix.one_apply_ne (ne_of_gt hij)
    · exact hb v hij
  · rw [FiniteAdelicGL.mem_standardIntegral_iff_local]
    intro v
    rw [map_mul, map_inv, hβv]
    simp only [b']
    split_ifs with hv
    · rw [inv_one, one_mul]
      exact hv
    · rw [hbk v, inv_mul_cancel_left]
      exact hk v

/-! ## Infinite places -/

omit [NumberField F] in
/-- Iwasawa decomposition of the actual infinite adelic `GL(n)`: every element is an upper
triangular matrix times an element of `standardInfiniteCompact F n`. -/
theorem exists_infinite_iwasawa (h : InfiniteAdelicGL F n) :
    ∃ β κ : InfiniteAdelicGL F n, h = β * κ ∧ β.val.IsUpperTriangular ∧
      κ ∈ standardInfiniteCompact F n := by
  classical
  let X := archimedeanGLCoordinates F n h
  choose br ur hfr using fun v => exists_upperTriangular_mul_unitary
    (Matrix.GeneralLinearGroup.map (realCoord v) X).val (Units.isUnit _)
  choose bc uc hfc using fun v => exists_upperTriangular_mul_unitary
    (Matrix.GeneralLinearGroup.map (complexCoord v) X).val (Units.isUnit _)
  let p : ArchimedeanCompactFactors F n :=
    (fun v => ⟨ur v, (hfr v).2.2.1⟩, fun v => ⟨uc v, (hfc v).2.2.1⟩)
  let κ := ArchimedeanCompactFactors.toInfiniteAdelicGL F n p
  have hκr : ∀ v, (Matrix.GeneralLinearGroup.map (realCoord v)
      (archimedeanGLCoordinates F n κ)).val = ur v := fun v => by
    ext i j
    rw [ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
    rfl
  have hκc : ∀ v, (Matrix.GeneralLinearGroup.map (complexCoord v)
      (archimedeanGLCoordinates F n κ)).val = uc v := fun v => by
    ext i j
    rw [ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
    rfl
  have hβr : ∀ v, (Matrix.GeneralLinearGroup.map (realCoord v)
      (archimedeanGLCoordinates F n (h * κ⁻¹))).val = br v := fun v => by
    rw [local_mul_inv]
    exact mul_inv_val_eq (hfr v) (hκr v)
  have hβc : ∀ v, (Matrix.GeneralLinearGroup.map (complexCoord v)
      (archimedeanGLCoordinates F n (h * κ⁻¹))).val = bc v := fun v => by
    rw [local_mul_inv]
    exact mul_inv_val_eq (hfc v) (hκc v)
  refine ⟨h * κ⁻¹, κ, (inv_mul_cancel_right h κ).symm, ?_, ⟨p, rfl⟩⟩
  intro i j hij
  apply (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
  rw [map_zero]
  apply Prod.ext
  · funext v
    exact (congrArg (fun M => M i j) (hβr v)).trans ((hfr v).1 hij)
  · funext v
    exact (congrArg (fun M => M i j) (hβc v)).trans ((hfc v).1 hij)

/-! ## Assembly -/

/-- `g = β κ` is an Iwasawa factorization for the standard compact subgroup: `β` is upper
triangular and `κ` lies in `standardCompact F n`. -/
def IsStandardIwasawaFactorization (g β κ : AdelicGL F n) : Prop :=
  g = β * κ ∧ β ∈ GeneralLinear.upperTriangularSubgroup n (Adeles F) ∧
    κ ∈ standardCompact F n

/-- **Iwasawa decomposition of the actual adelic `GL(n)`.** Every element of `GL(n, 𝔸_F)` is
an upper triangular matrix times an element of the standard compact subgroup. -/
theorem exists_isStandardIwasawaFactorization (g : AdelicGL F n) :
    ∃ β κ : AdelicGL F n, IsStandardIwasawaFactorization F n g β κ := by
  obtain ⟨βi, κi, hgi, hβi, hκi⟩ := exists_infinite_iwasawa F n (AdelicGL.infinite F n g)
  obtain ⟨βf, κf, hgf, hβf, hκf⟩ := exists_finite_iwasawa F n (AdelicGL.finite F n g)
  refine ⟨AdelicGL.pair F n βi βf, AdelicGL.pair F n κi κf, ?_, ?_,
    (mem_standardCompact_iff F n _).mpr ⟨by rw [AdelicGL.infinite_pair]; exact hκi,
      by rw [AdelicGL.finite_pair]; exact hκf⟩⟩
  · apply (AdelicGL.split F n).injective
    rw [map_mul]
    change (AdelicGL.infinite F n g, AdelicGL.finite F n g) =
      (AdelicGL.infinite F n (AdelicGL.pair F n βi βf),
        AdelicGL.finite F n (AdelicGL.pair F n βi βf)) *
      (AdelicGL.infinite F n (AdelicGL.pair F n κi κf),
        AdelicGL.finite F n (AdelicGL.pair F n κi κf))
    rw [AdelicGL.infinite_pair, AdelicGL.finite_pair, AdelicGL.infinite_pair,
      AdelicGL.finite_pair, Prod.mk_mul_mk, ← hgi, ← hgf]
  · rw [GeneralLinear.mem_upperTriangularSubgroup_iff]
    intro i j hij
    rw [AdelicGL.pair_apply, hβi hij, hβf hij]
    rfl

/-- The upper triangular subgroup times the standard compact subgroup is all of
`GL(n, 𝔸_F)`. -/
theorem upperTriangular_mul_standardCompact :
    (GeneralLinear.upperTriangularSubgroup n (Adeles F) : Set (AdelicGL F n)) *
      (standardCompact F n : Set (AdelicGL F n)) = Set.univ := by
  refine Set.eq_univ_of_forall fun g => ?_
  obtain ⟨β, κ, hg, hβ, hκ⟩ := exists_isStandardIwasawaFactorization F n g
  exact ⟨β, hβ, κ, hκ, hg.symm⟩

end Langlands.Global.PrimitiveAdelicHeight
