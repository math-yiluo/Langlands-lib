import Langlands.Geometry.FormalGroup.BaseChange
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # Principal-open descent of actual substitutable tuples -/

noncomputable section

universe u v

namespace Langlands.FormalGroup

open MvPowerSeries

variable {R : Type v} [CommRing R]
variable {σ κ : Type}

/-- Nilpotence of an element is detected on any principal-open cover. -/
theorem isNilpotent_of_basic_cover (s : Set R) (hs : Ideal.span s = ⊤) (x : R)
    (h : ∀ a : s, IsNilpotent (algebraMap R (Localization.Away a.val) x)) :
    IsNilpotent x := by
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have hns : ¬ s ⊆ J := by
    intro hsub
    have ht : ⊤ ≤ J := hs ▸ Ideal.span_le.mpr hsub
    exact hJ.ne_top (top_le_iff.mp ht)
  obtain ⟨a, has, haJ⟩ := Set.not_subset.mp hns
  obtain ⟨n, hn⟩ := h ⟨a, has⟩
  have hz : algebraMap R (Localization.Away a) (x ^ n) =
      algebraMap R (Localization.Away a) 0 := by
    rw [map_pow, map_zero]
    exact hn
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq a hz
  have hmul : a ^ m * x ^ n ∈ J := by
    rw [hm, mul_zero]
    exact J.zero_mem
  rcases hJ.mem_or_mem hmul with ha | hx
  · exact False.elim (haJ (hJ.mem_of_pow_mem m ha))
  · exact hJ.mem_of_pow_mem n hx

namespace SeriesPoint

/-- Matching actual substitutable tuples on every pairwise localized overlap. -/
def BasicCompatible (s : Set R) (z : (a : s) → SeriesPoint (Localization.Away a.val) σ κ) :
    Prop :=
  ∀ a b : s,
    (z a).map (IsLocalization.Away.awayToAwayRight
      (S := Localization.Away a.val) (P := Localization.Away (a.val * b.val)) a.val b.val) =
    (z b).map (IsLocalization.Away.awayToAwayLeft
      (S := Localization.Away b.val) (P := Localization.Away (a.val * b.val)) b.val a.val)

/-- Equality of actual tuples is detected after localization on a basic cover. -/
theorem ext_basic (s : Set R) (hs : Ideal.span s = ⊤) {x y : SeriesPoint R σ κ}
    (h : ∀ a : s, x.map (algebraMap R (Localization.Away a.val)) =
      y.map (algebraMap R (Localization.Away a.val))) : x = y := by
  apply SeriesPoint.ext
  intro i
  apply MvPowerSeries.ext
  intro d
  apply Localization.algebraMap_injective_of_span_eq_top s hs
  funext a
  exact congrArg (fun z : SeriesPoint (Localization.Away a.val) σ κ =>
    coeff d (z.val i)) (h a)

/-- Glue an actual coefficient using the structure-sheaf localization theorem. -/
def glueBasicCoefficient (s : Set R) (hs : Ideal.span s = ⊤)
    (z : (a : s) → SeriesPoint (Localization.Away a.val) σ κ)
    (hz : BasicCompatible s z) (i : σ) (d : κ →₀ ℕ) : R :=
  Classical.choose (Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs
    (fun a => coeff d ((z a).val i))
    (fun a b => congrArg (fun q => coeff d (q.val i)) (hz a b)))

/-- Every glued coefficient has the prescribed localization. -/
theorem glueBasicCoefficient_spec (s : Set R) (hs : Ideal.span s = ⊤)
    (z : (a : s) → SeriesPoint (Localization.Away a.val) σ κ)
    (hz : BasicCompatible s z) (i : σ) (d : κ →₀ ℕ) (a : s) :
    algebraMap R (Localization.Away a.val) (glueBasicCoefficient s hs z hz i d) =
      coeff d ((z a).val i) :=
  (Classical.choose_spec (Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs
    (fun a => coeff d ((z a).val i))
    (fun a b => congrArg (fun q => coeff d (q.val i)) (hz a b)))).1 a

/-- Coefficient gluing yields a substitutable tuple, with no uniform local exponent. -/
def glueBasic [Finite σ] (s : Set R) (hs : Ideal.span s = ⊤)
    (z : (a : s) → SeriesPoint (Localization.Away a.val) σ κ)
    (hz : BasicCompatible s z) : SeriesPoint R σ κ :=
  ⟨fun i d => glueBasicCoefficient s hs z hz i d,
    hasSubst_of_constantCoeff_nilpotent (fun i => by
      apply isNilpotent_of_basic_cover s hs
      intro a
      change IsNilpotent (algebraMap R (Localization.Away a.val)
        (glueBasicCoefficient s hs z hz i 0))
      rw [glueBasicCoefficient_spec]
      exact (z a).property.const_coeff i)⟩

/-- The actual glued tuple restricts to every prescribed local tuple. -/
theorem glueBasic_map [Finite σ] (s : Set R) (hs : Ideal.span s = ⊤)
    (z : (a : s) → SeriesPoint (Localization.Away a.val) σ κ)
    (hz : BasicCompatible s z) (a : s) :
    (glueBasic s hs z hz).map (algebraMap R (Localization.Away a.val)) = z a := by
  apply SeriesPoint.ext
  intro i
  apply MvPowerSeries.ext
  intro d
  exact glueBasicCoefficient_spec s hs z hz i d a

/-- Canonical restrictions of a global tuple satisfy the matching equations. -/
theorem basicCompatible_map (s : Set R) (x : SeriesPoint R σ κ) :
    BasicCompatible s (fun a => x.map (algebraMap R (Localization.Away a.val))) := by
  intro a b
  apply SeriesPoint.ext
  intro i
  apply MvPowerSeries.ext
  intro d
  exact (IsLocalization.Away.awayToAwayRight_eq
    (S := Localization.Away a.val) (P := Localization.Away (a.val * b.val))
    a.val b.val (coeff d (x.val i))).trans
    (IsLocalization.Away.awayToAwayLeft_eq
      (S := Localization.Away b.val) (P := Localization.Away (a.val * b.val))
      b.val a.val (coeff d (x.val i))).symm

/-- Actual local tuples satisfying the principal-open overlap equations. -/
abbrev MatchingBasic (s : Set R) :=
  {z : (a : s) → SeriesPoint (Localization.Away a.val) σ κ // BasicCompatible s z}

/-- Actual tuple descent along an arbitrary principal-open cover. -/
def basicEquiv [Finite σ] (s : Set R) (hs : Ideal.span s = ⊤) :
    SeriesPoint R σ κ ≃ MatchingBasic (σ := σ) (κ := κ) s where
  toFun x := ⟨fun a => x.map (algebraMap R (Localization.Away a.val)),
    basicCompatible_map s x⟩
  invFun z := glueBasic s hs z.val z.property
  left_inv x := by
    apply ext_basic s hs
    intro a
    exact glueBasic_map s hs _ _ a
  right_inv z := by
    apply Subtype.ext
    funext a
    exact glueBasic_map s hs z.val z.property a

end SeriesPoint

end Langlands.FormalGroup
