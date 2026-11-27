import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Algebra.Rat

/-! # Complementary summands for a linear involution -/

noncomputable section

universe u

open TensorProduct LinearMap

namespace Langlands.Algebra

variable {R : Type u} [CommRing R] {M N : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The image of `1/2` in a rational algebra. -/
abbrev half (R : Type u) [CommRing R] [Algebra ℚ R] : R := algebraMap ℚ R (1 / 2)

lemma half_add_half (R : Type u) [CommRing R] [Algebra ℚ R] : half R + half R = 1 := by
  rw [← map_add, show (1 / 2 : ℚ) + 1 / 2 = 1 by norm_num, map_one]

lemma half_smul_add_half_smul [Algebra ℚ R] (x : M) :
    half R • x + half R • x = x := by rw [← add_smul, half_add_half, one_smul]

lemma eq_zero_of_eq_neg_of_rat [Algebra ℚ R] {x : M} (h : x = -x) : x = 0 := by
  have hy : half R • x = -(half R • x) := by
    simpa only [smul_neg] using congrArg (half R • ·) h
  calc
    x = half R • x + half R • x := (half_smul_add_half_smul (R := R) x).symm
    _ = half R • x + -(half R • x) := congrArg (half R • x + ·) hy
    _ = 0 := add_neg_cancel _

/-- The submodule on which a linear involution acts by the scalar `s`. -/
abbrev involutionPart (T : M →ₗ[R] M) (s : R) := (T - s • LinearMap.id).ker

lemma mem_involutionPart {T : M →ₗ[R] M} {s : R} {x : M} :
    x ∈ involutionPart T s ↔ T x = s • x := by
  change T x - s • x = 0 ↔ _
  exact sub_eq_zero

/-- The polynomial projection `c(1 + sT)` for `2c = 1` and `s² = 1`. -/
def involutionProjector (T : M →ₗ[R] M) (hT : Function.Involutive T)
    (s c : R) (hs : s * s = 1) : M →ₗ[R] involutionPart T s :=
  (c • (LinearMap.id + s • T)).codRestrict _ (fun x => by
    apply mem_involutionPart.mpr
    change T (c • (x + s • T x)) = s • (c • (x + s • T x))
    rw [map_smul, map_add, map_smul, hT, smul_comm s c, smul_add s, smul_smul, hs, one_smul,
      add_comm (T x)])

@[simp]
lemma involutionProjector_val (T : M →ₗ[R] M) (hT : Function.Involutive T)
    (s c : R) (hs : s * s = 1) (x : M) :
    (involutionProjector T hT s c hs x : M) = c • (x + s • T x) := rfl

lemma involutionProjector_subtype (T : M →ₗ[R] M) (hT : Function.Involutive T)
    (s c : R) (hs : s * s = 1) (hc : c + c = 1) :
    (involutionProjector T hT s c hs).comp (involutionPart T s).subtype = LinearMap.id := by
  ext x : 1
  apply Subtype.ext
  change c • (x.val + s • T x.val) = x.val
  rw [mem_involutionPart.mp x.property, smul_smul, hs, one_smul, smul_add, ← add_smul, hc, one_smul]

/-- A map commuting with the involutions restricts to either scalar summand. -/
def involutionPartMap (T : M →ₗ[R] M) (T' : N →ₗ[R] N) (s : R)
    (d : M →ₗ[R] N) (hd : ∀ x, T' (d x) = d (T x)) :
    involutionPart T s →ₗ[R] involutionPart T' s :=
  (d.comp (involutionPart T s).subtype).codRestrict _ (fun x => by
    apply mem_involutionPart.mpr
    change T' (d x.val) = s • d x.val
    rw [hd, mem_involutionPart.mp x.property, map_smul])

@[simp]
lemma involutionPartMap_val (T : M →ₗ[R] M) (T' : N →ₗ[R] N) (s : R)
    (d : M →ₗ[R] N) (hd : ∀ x, T' (d x) = d (T x)) (x : involutionPart T s) :
    (involutionPartMap T T' s d hd x : N) = d x.val := rfl

lemma involutionPart_flat [Module.Flat R M] (T : M →ₗ[R] M) (hT : Function.Involutive T)
    (s c : R) (hs : s * s = 1) (hc : c + c = 1) : Module.Flat R (involutionPart T s) :=
  Module.Flat.of_retract _ _ (involutionProjector_subtype T hT s c hs hc)

section BaseChange

variable {K M' : Type u} [CommRing K] [Algebra R K]
  [AddCommGroup M'] [Module K M']
  (T : M →ₗ[R] M) (hT : Function.Involutive T) (S : M' →ₗ[K] M')
  (hS : Function.Involutive S) (e : (K ⊗[R] M) ≃ₗ[K] M')
  (he : ∀ x, e (T.baseChange K x) = S (e x))
  (s c : R) (hs : s * s = 1) (hc : c + c = 1)

include he in
private lemma involutionProjection_baseChange (x : K ⊗[R] M) :
    e (((c • (LinearMap.id + s • T)).baseChange K) x) =
      algebraMap R K c • (e x + algebraMap R K s • S (e x)) := by
  simp only [LinearMap.baseChange_smul, LinearMap.baseChange_add, LinearMap.baseChange_id,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
  rw [← IsScalarTower.algebraMap_smul K s, ← IsScalarTower.algebraMap_smul K c,
    map_smul, map_add, map_smul, he]

/-- The eigensummand commutes with scalar extension because the projectors do. -/
def involutionPartBaseChange : K ⊗[R] involutionPart T s ≃ₗ[K]
    involutionPart S (algebraMap R K s) := by
  let i := (involutionPart T s).subtype.baseChange K
  let p := (involutionProjector T hT s c hs).baseChange K
  have hsk : algebraMap R K s * algebraMap R K s = 1 := by rw [← map_mul, hs, map_one]
  have hck : algebraMap R K c + algebraMap R K c = 1 := by rw [← map_add, hc, map_one]
  let q := involutionProjector S hS (algebraMap R K s) (algebraMap R K c) hsk
  let j := (involutionPart S (algebraMap R K s)).subtype
  have hpi : p.comp i = LinearMap.id := by
    dsimp [p, i]
    rw [← LinearMap.baseChange_comp, involutionProjector_subtype T hT s c hs hc,
      LinearMap.baseChange_id]
  have hqj : q.comp j = LinearMap.id := involutionProjector_subtype _ _ _ _ _ hck
  have hproj (x : K ⊗[R] M) : e (i (p x)) = j (q (e x)) := by
    have hl : i.comp p = (c • (LinearMap.id + s • T)).baseChange K := by
      dsimp [p, i]
      rw [← LinearMap.baseChange_comp]
      rfl
    rw [← LinearMap.comp_apply, hl]
    exact involutionProjection_baseChange T S e he s c x
  refine LinearEquiv.ofLinearMap (q.comp (e.toLinearMap.comp i))
    (p.comp (e.symm.toLinearMap.comp j)) ?_ ?_
  · apply LinearMap.ext
    intro y
    apply Subtype.ext
    change j (q (e (i (p (e.symm (j y)))))) = j y
    rw [hproj, e.apply_symm_apply, show q (j y) = y from LinearMap.congr_fun hqj y,
      show q (j y) = y from LinearMap.congr_fun hqj y]
  · apply LinearMap.ext
    intro x
    change p (e.symm (j (q (e (i x))))) = x
    rw [← hproj, e.symm_apply_apply, show p (i x) = x from LinearMap.congr_fun hpi x,
      show p (i x) = x from LinearMap.congr_fun hpi x]

lemma involutionPartBaseChange_val (x : K ⊗[R] involutionPart T s) :
    (involutionPartBaseChange T hT S hS e he s c hs hc x : M') =
      e ((involutionPart T s).subtype.baseChange K x) := by
  change ((involutionProjector S hS (algebraMap R K s) (algebraMap R K c)
    (by rw [← map_mul, hs, map_one])
    (e ((involutionPart T s).subtype.baseChange K x))) : M') = _
  have hp : (involutionProjector T hT s c hs).baseChange K
      ((involutionPart T s).subtype.baseChange K x) = x := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      involutionProjector_subtype T hT s c hs hc, LinearMap.baseChange_id, LinearMap.id_apply]
  rw [involutionProjector_val, ← involutionProjection_baseChange T S e he s c]
  have hh : (c • (LinearMap.id + s • T)).baseChange K =
      ((involutionPart T s).subtype.baseChange K).comp ((involutionProjector T hT s c hs).baseChange K) := by
    rw [← LinearMap.baseChange_comp]
    rfl
  rw [hh, LinearMap.comp_apply, hp]

end BaseChange

end Langlands.Algebra
