import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Star
import Mathlib.Tactic

/-!
# Integral infinity types on actual archimedean ideles

The exponents are indexed by the actual complex embeddings of a number field.
For a totally complex field each infinite place contributes its chosen embedding
and its conjugate. Character extension to the idele-class group is separate.
-/

noncomputable section

universe u v

namespace Langlands.Global

open NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- Integral exponents indexed by all complex embeddings of the number field. -/
abbrev InfinityType := (K →+* ℂ) → ℤ

namespace InfinityType

variable {K}

/-- Pullback of an infinity type by conjugation of complex embeddings. -/
def conjugate (a : InfinityType K) : InfinityType K :=
  fun σ ↦ a (ComplexEmbedding.conjugate σ)

omit [NumberField K] in
@[simp]
theorem conjugate_conjugate (a : InfinityType K) : conjugate (conjugate a) = a := by
  funext σ
  exact congrArg a (ComplexEmbedding.involutive_conjugate K σ)

/-- The weight at the conjugate embedding is the negative of the original weight. -/
def IsAnticyclotomic (a : InfinityType K) : Prop :=
  ∀ σ, a (ComplexEmbedding.conjugate σ) = -a σ

/-- All conjugate pairs have the same total weight. -/
def IsPureOfWeight (a : InfinityType K) (w : ℤ) : Prop :=
  ∀ σ, a σ + a (ComplexEmbedding.conjugate σ) = w

/-- Distinct weights among embeddings extending a specified embedding of a subfield.
For Henniart's infinity regularity, the subfield is imaginary quadratic. -/
def DistinctWeightsAbove {E : Type v} [Field E] (ι : E →+* K) (τ : E →+* ℂ)
    (a : InfinityType K) : Prop :=
  Function.Injective (fun σ : {σ : K →+* ℂ // σ.comp ι = τ} ↦ a σ.val)

omit [NumberField K] in
theorem isAnticyclotomic_iff_pure_zero (a : InfinityType K) :
    IsAnticyclotomic a ↔ IsPureOfWeight a 0 := by
  constructor
  · intro h σ
    rw [h σ]
    exact add_neg_cancel _
  · intro h σ
    have hs := h σ
    omega

/-- A complex algebraic character with explicit integral holomorphic and
antiholomorphic exponents. -/
def complexCharacter (p q : ℤ) : ℂˣ →ₜ* ℂˣ where
  toFun z := z ^ p * star z ^ q
  map_one' := by simp
  map_mul' z w := by simp [mul_zpow, mul_assoc, mul_left_comm]
  continuous_toFun := (continuous_id.zpow p).mul (continuous_star.zpow q)

@[simp]
theorem complexCharacter_apply (p q : ℤ) (z : ℂˣ) :
    complexCharacter p q z = z ^ p * star z ^ q := rfl

theorem complexCharacter_anticyclotomic (p : ℤ) (z : ℂˣ) :
    complexCharacter p (-p) z = (z / star z) ^ p := by
  simp only [complexCharacter_apply, zpow_neg, div_eq_mul_inv, mul_zpow, inv_zpow]

theorem complexCharacter_conjugate (p q : ℤ) (z : ℂˣ) :
    complexCharacter p q (star z) = complexCharacter q p z := by
  simp only [complexCharacter_apply, star_star]
  exact mul_comm _ _

theorem complexCharacter_anticyclotomic_unitary (p : ℤ) (z : ℂˣ) :
    ‖(complexCharacter p (-p) z : ℂ)‖ = 1 := by
  rw [complexCharacter_anticyclotomic]
  simp [norm_zpow, norm_ne_zero_iff.mpr z.ne_zero]

/-- The complex coordinate of an actual archimedean idele, using Mathlib's
chosen complex embedding for the place and its extension to the completion. -/
def coordinate (v : NumberField.InfinitePlace K) :
    (NumberField.InfiniteAdeleRing K)ˣ →ₜ* ℂˣ where
  toMonoidHom := Units.map
    ((NumberField.InfinitePlace.Completion.extensionEmbedding v).comp
      (Pi.evalRingHom (fun w : NumberField.InfinitePlace K ↦ w.Completion) v)).toMonoidHom
  continuous_toFun :=
    ((NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp
      (continuous_apply v)).units_map _

omit [NumberField K] in
@[simp]
theorem coordinate_apply (v : NumberField.InfinitePlace K)
    (x : (NumberField.InfiniteAdeleRing K)ˣ) :
    (coordinate v x : ℂ) =
      NumberField.InfinitePlace.Completion.extensionEmbedding v (x.val v) := rfl

omit [NumberField K] in
theorem coordinate_diagonal (v : NumberField.InfinitePlace K) (x : Kˣ) :
    (coordinate v (Units.map
      (algebraMap K (NumberField.InfiniteAdeleRing K)).toMonoidHom x) : ℂ) =
        v.embedding (x : K) := by
  change NumberField.InfinitePlace.Completion.extensionEmbedding v
    ((x : K) : v.Completion) = _
  simp

/-- The continuous infinity character associated with integral weights.
The totally complex hypothesis ensures that conjugate embeddings occur in pairs. -/
def toCharacter [IsTotallyComplex K] (a : InfinityType K) :
    (NumberField.InfiniteAdeleRing K)ˣ →ₜ* ℂˣ where
  toFun x := ∏ v : NumberField.InfinitePlace K,
    complexCharacter (a v.embedding) (a (ComplexEmbedding.conjugate v.embedding))
      (coordinate v x)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    exact Finset.prod_mul_distrib
  continuous_toFun := continuous_finsetProd _ fun v _ ↦
    (complexCharacter _ _).continuous.comp (coordinate v).continuous

theorem toCharacter_apply [IsTotallyComplex K] (a : InfinityType K)
    (x : (NumberField.InfiniteAdeleRing K)ˣ) :
    toCharacter a x = ∏ v : NumberField.InfinitePlace K,
      (coordinate v x) ^ a v.embedding *
        star (coordinate v x) ^ a (ComplexEmbedding.conjugate v.embedding) := rfl

theorem toCharacter_anticyclotomic [IsTotallyComplex K] (a : InfinityType K)
    (ha : IsAnticyclotomic a) (x : (NumberField.InfiniteAdeleRing K)ˣ) :
    toCharacter a x = ∏ v : NumberField.InfinitePlace K,
      (coordinate v x / star (coordinate v x)) ^ a v.embedding := by
  change (∏ v, complexCharacter _ _ _) = _
  apply Finset.prod_congr rfl
  intro v _
  rw [ha v.embedding, complexCharacter_anticyclotomic]

theorem toCharacter_unitary [IsTotallyComplex K] (a : InfinityType K)
    (ha : IsAnticyclotomic a) (x : (NumberField.InfiniteAdeleRing K)ˣ) :
    ‖(toCharacter a x : ℂ)‖ = 1 := by
  change ‖(Units.coeHom ℂ) (∏ v : NumberField.InfinitePlace K,
    complexCharacter (a v.embedding) (a (ComplexEmbedding.conjugate v.embedding))
      (coordinate v x))‖ = 1
  rw [map_prod, norm_prod]
  apply Finset.prod_eq_one
  intro v _
  rw [ha v.embedding]
  exact complexCharacter_anticyclotomic_unitary _ _

/-- On a CM field, conjugating embeddings is the pullback by the actual
arithmetic complex conjugation. -/
theorem conjugate_apply_cm [IsCMField K] (a : InfinityType K) (σ : K →+* ℂ) :
    conjugate a σ = a (σ.comp (IsCMField.complexConj K).toRingHom) := by
  apply congrArg a
  ext x
  exact (IsCMField.complexEmbedding_complexConj K σ x).symm

end InfinityType
end Langlands.Global
