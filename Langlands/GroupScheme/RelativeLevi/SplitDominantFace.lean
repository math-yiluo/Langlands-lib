import Langlands.GroupScheme.RelativeLevi.SplitParabolicWeightChart
import Langlands.LinearAlgebra.RootDatumFaceBaseComparison

/-! # Prescribed dominant bases as actual coweight-face data -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.LinearAlgebra.RootDatumFaceBaseComparison

open IsAddIndecomposable

variable {J M N : Type*} [AddCommGroup M] [AddCommGroup N]
  (P : RootDatum J M N) [Fintype J] [P.IsReduced]

/-- A functional with exactly the positive-root signs of a base has that
base as its indecomposable positive-root set. -/
theorem support_eq_baseOf_of_signs (b : P.Base) (f : Module.Dual ℤ M)
    (hsign : ∀ a, 0 < f (P.root a) ↔ b.IsPos a) :
    (b.support : Set J) = baseOf P.root (f : M →+ ℤ) := by
  ext a
  constructor
  · intro ha
    refine ⟨(hsign a).mpr (b.isPos_of_mem_support ha), ?_⟩
    intro j hj k hk he
    have hj' := (hsign j).mp hj
    have hk' := (hsign k).mp hk
    have hh := b.height_add he
    rw [b.height_one_of_mem_support ha] at hh
    change 0 < b.height j at hj'
    change 0 < b.height k at hk'
    exfalso
    omega
  · intro ha
    by_contra hn
    have hapos : b.IsPos a := (hsign a).mp ha.1
    obtain ⟨j, hj, hpair⟩ := hapos.exists_mem_support_pos_pairingIn
    rw [P.zero_lt_pairingIn_iff'] at hpair
    have haj : a ≠ j := by
      rintro rfl
      exact hn hj
    obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos hpair haj
    have hkpos : b.IsPos k := hapos.sub hj hk
    have he : P.root a = P.root k + P.root j := by rw [hk]; abel
    rcases ha.2 k ((hsign k).mpr hkpos) j
      ((hsign j).mpr (b.isPos_of_mem_support hj)) he with hz | hz
    · exact P.ne_zero k hz
    · exact P.ne_zero j hz

/-- A coweight dominant on the simple roots is nonnegative on every positive root. -/
theorem root'_nonneg_of_isPos (b : P.Base) (cv : N)
    (hdom : ∀ a ∈ b.support, 0 ≤ P.root' a cv) {a : J} (ha : b.IsPos a) :
    0 ≤ P.root' a cv := by
  apply ha.induction_on_add
  · exact hdom
  · intro a j k hk hA hj
    change 0 ≤ P.toLinearMap (P.root k) cv
    rw [hk, map_add, LinearMap.add_apply]
    exact add_nonneg hA (hdom j hj)

end Langlands.LinearAlgebra.RootDatumFaceBaseComparison

namespace Langlands.GroupScheme.LocalSplitCell

open Langlands.LinearAlgebra.RootDatumFaceBaseComparison
open Langlands.LinearAlgebra.RootDatumFaceHeight
open Langlands.LinearAlgebra.RootDatumCoweightFace

variable {I J : Type u} [Fintype I] [Fintype J]
  (P : RootDatum J (I → ℤ) (I → ℤ)) [P.IsReduced]

/-- Every prescribed dominant base occurs as the base of actual sign-refining
coweight-face data, without changing the base. -/
theorem nonempty_face_of_dominant_base (b : P.Base) (cv : I → ℤ)
    (hdom : ∀ a ∈ b.support, 0 ≤ P.root' a cv) :
    Nonempty {F : Face P cv // F.base = b} := by
  classical
  obtain ⟨reg, hregpos, hregneg⟩ := exists_cocharacter_of_base P b
  let f := P.flip.toPerfPair.symm (coPairingLinear reg)
  have hfval (a : J) : P.root' a f = coPairing (P.root a) reg := by
    change (P.flip.toPerfPair f) (P.root a) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hf (a : J) : P.root' a f ≠ 0 := by
    rw [hfval]
    by_cases ha : b.IsPos a
    · exact ne_of_gt (hregpos a ha)
    · exact ne_of_lt (hregneg a ha)
  have hsign (a : J) : 0 < P.root' a f ↔ b.IsPos a := by
    rw [hfval]
    constructor
    · intro h
      by_contra hn
      exact (not_lt_of_ge (hregneg a hn).le) h
    · exact hregpos a
  have hface (a : J) (ha : P.root' a cv ≠ 0) :
      0 < P.root' a f ↔ 0 < P.root' a cv := by
    constructor
    · intro h
      have hn := root'_nonneg_of_isPos P b cv hdom ((hsign a).mp h)
      omega
    · intro h
      apply (hsign a).mpr
      by_contra hn
      let := P.indexNeg
      have hneg := root'_nonneg_of_isPos P b cv hdom
        ((RootPairing.Base.IsPos.neg_iff_not b a).mpr hn)
      have he : P.root (-a) = - P.root a := by
        change P.root (P.reflectionPerm a a) = _
        simp
      change 0 ≤ P.toLinearMap (P.root (-a)) cv at hneg
      rw [he, map_neg, LinearMap.neg_apply] at hneg
      change 0 ≤ - P.root' a cv at hneg
      omega
  have hsupport : (b.support : Set J) =
      IsAddIndecomposable.baseOf P.root ((P.flip.toLinearMap f) : (I → ℤ) →+ ℤ) :=
    support_eq_baseOf_of_signs P b (P.flip.toLinearMap f) hsign
  exact ⟨⟨{
    regular := f
    nonzero := hf
    signs := hface
    base := b
    support_eq := hsupport
    span_eq := coroot_span_zero_eq P cv f hface b hsupport
  }, rfl⟩⟩

/-- Choose actual coweight-face data with the prescribed dominant base. -/
def dominantBaseFace (b : P.Base) (cv : I → ℤ)
    (hdom : ∀ a ∈ b.support, 0 ≤ P.root' a cv) : {F : Face P cv // F.base = b} :=
  Classical.choice (nonempty_face_of_dominant_base P b cv hdom)

/-- The unscaled integral face height is independent of any prescribed
coordinate-root-datum bases dominant for the same coweight. -/
theorem faceHeight_eq_of_dominant_bases (b b' : P.Base) (cv : I → ℤ)
    [Finite (Langlands.LinearAlgebra.RootDatumWeylChambers.reflectionSubgroup
      P {a | P.root' a cv = 0})]
    (hdom : ∀ a ∈ b.support, 0 ≤ P.root' a cv)
    (hdom' : ∀ a ∈ b'.support, 0 ≤ P.root' a cv) :
    faceHeight b cv = faceHeight b' cv := by
  let F := dominantBaseFace P b cv hdom
  let F' := dominantBaseFace P b' cv hdom'
  have h := Langlands.LinearAlgebra.RootDatumFaceBaseComparison.faceHeight_eq
    P cv F.val F'.val
  simpa only [F.property, F'.property] using h

end Langlands.GroupScheme.LocalSplitCell
