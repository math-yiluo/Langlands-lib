import Langlands.BaseChange.RegularElementaryDoubleCoset
import Langlands.Representation.Hecke.DoubleCoset

/-! # Finite coset decomposition of the regular elementary test -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.Unramified HarmonicAnalysis Hecke.TestFunction
open GeneralLinear.Iwasawa (diagonalUnits torus)
open scoped BigOperators

universe u

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2

variable {p : ℕ} [Fact p.Prime] (E : PadicField.{u} p) {r : ℕ}
  (τ : E.Carrier ≃ₐ[Padic p] E.Carrier)
  (π : E.Carrierˣ) (ν : Fin (r + 1) → ℤ)

local notation "L" => GeneralLinear (r + 1) E.Carrier
local notation "K" => sphericalOpenSubgroup E r
local notation "I" => regularElementaryCompactOpenSubgroup E r
local notation "A" => elementaryDiagonalTuples E π ν
local notation "D" => doubleCosetSet I (torus π ν)
local notation "τG" => entrywiseAut τ (r + 1)

/-- The unnormalized double-coset test using the subgroup with diagonal reduction. -/
def regularElementaryDoubleCosetTest : SchwartzBruhat L :=
  doubleCosetIndicator I (regularElementaryCompactOpenSubgroup_isCompact E) (torus π ν)

/-- Pull the double-coset test back by twisted conjugation. -/
def regularElementaryCosetTest (k : L) : SchwartzBruhat L :=
  leftTranslate k (rightTranslate (τG k) (regularElementaryDoubleCosetTest E π ν))

@[simp]
theorem regularElementaryCosetTest_apply (k g : L) :
    regularElementaryCosetTest E τ π ν k g =
      (D).indicator (fun _ => (1 : ℂ)) (k⁻¹ * g * τG k) := rfl

/-- The cosets of the diagonal-reduction subgroup in the spherical subgroup. -/
abbrev RegularElementaryCosets (rank : ℕ) :=
  ↥(sphericalOpenSubgroup E rank) ⧸
    (regularElementaryCompactOpenSubgroup E rank).toSubgroup.subgroupOf
      (sphericalOpenSubgroup E rank).toSubgroup

instance regularElementaryCosetsFinite (rank : ℕ) :
    Finite (RegularElementaryCosets E rank) := by
  let C := sphericalOpenSubgroup E rank
  let H := regularElementaryCompactOpenSubgroup E rank
  let : CompactSpace C := isCompact_iff_compactSpace.mp (sphericalOpenSubgroup_isCompact E rank)
  exact Subgroup.quotient_finite_of_isOpen (H.toSubgroup.subgroupOf C.toSubgroup)
    (Subgroup.subgroupOf_isOpen C.toSubgroup H.toSubgroup H.isOpen)

instance regularElementaryCosetsFintype (rank : ℕ) :
    Fintype (RegularElementaryCosets E rank) := Fintype.ofFinite _

variable (hπ : E.canonicalTopologicalData.ord (π : E.Carrier) = 1)
  (hν : StrictAnti ν)

include hπ hν in
/-- For a weighted diagonal and an integral conjugator, the smaller support
is reached exactly by conjugators belonging to the smaller subgroup. -/
theorem twistedConj_weightedDiagonal_mem_doubleCoset_iff
    {a : Fin (r + 1) → E.Carrierˣ} (ha : a ∈ A) (k : K) :
    (k : L)⁻¹ * diagonalUnits a * τG (k : L) ∈ D ↔ (k : L) ∈ I := by
  change _ ∈ DoubleCoset.doubleCoset _ ((I).toSubgroup : Set L) ((I).toSubgroup : Set L) ↔ _
  rw [regularElementary_doubleCoset_eq_twistedDiagonalSaturation E τ π hπ ν hν]
  constructor
  · rintro ⟨i, hi, b, hb, he⟩
    have he' : ((k : L) * i⁻¹)⁻¹ * diagonalUnits a * τG ((k : L) * i⁻¹) =
        diagonalUnits b := by
      calc
        _ = i * ((k : L)⁻¹ * diagonalUnits a * τG (k : L)) * (τG i)⁻¹ := by
          rw [map_mul, map_inv]
          group
        _ = _ := by rw [← he]; group
    have ha' := (mem_elementaryDiagonalTuples_iff E π hπ ν a).1 ha
    have hb' := (mem_elementaryDiagonalTuples_iff E π hπ ν b).1 hb
    obtain ⟨d, hd⟩ := exists_diagonalUnits_of_strict_twistedConj E τ
      (fun j => (ha' j).trans (hb' j).symm) (by simpa only [ha'] using hν.injective) he'
    have hki : (k : L) * i⁻¹ ∈ K := (K).mul_mem k.property
      ((K).inv_mem (regularElementaryCompactOpenSubgroup_le_spherical E hi))
    have hki' : (k : L) * i⁻¹ ∈ I := by
      rw [hd] at hki ⊢
      exact diagonalUnits_mem_regularElementaryCompactOpenSubgroup E hki
    change (k : L) ∈ (I).toSubgroup
    simpa only [inv_mul_cancel_right] using (I).toSubgroup.mul_mem hki' hi
  · intro hk
    exact ⟨k, hk, a, ha, rfl⟩

include hπ hν in
private theorem mem_support_of_twistedConj_mem_doubleCoset (k : K) {g : L}
    (hg : (k : L)⁻¹ * g * τG (k : L) ∈ D) : g ∈ regularElementarySupport E τ π ν := by
  change _ ∈ DoubleCoset.doubleCoset _ ((I).toSubgroup : Set L) ((I).toSubgroup : Set L) at hg
  rw [regularElementary_doubleCoset_eq_twistedDiagonalSaturation E τ π hπ ν hν] at hg
  obtain ⟨i, hi, a, ha, he⟩ := hg
  refine ⟨i * (k : L)⁻¹, (K).mul_mem
    (regularElementaryCompactOpenSubgroup_le_spherical E hi) ((K).inv_mem k.property),
    a, ha, ?_⟩
  calc
    _ = (k : L) * (i⁻¹ * diagonalUnits a * τG i) * (τG (k : L))⁻¹ := by
      rw [map_mul, map_inv]
      group
    _ = _ := by rw [he]; group

include hπ hν in
/-- The regular elementary test is the sum of the twisted conjugates of the
smaller double-coset indicator, one for each spherical subgroup coset. -/
theorem regularElementaryTest_eq_sum_cosets :
    regularElementaryTest E τ π hπ ν hν =
      ∑ q : RegularElementaryCosets E r, regularElementaryCosetTest E τ π ν (q.out : L) := by
  classical
  ext g
  simp only [regularElementaryTest_apply, Submodule.coe_sum, Finset.sum_apply,
    regularElementaryCosetTest_apply]
  by_cases hg : g ∈ regularElementarySupport E τ π ν
  · rw [Set.indicator_of_mem hg]
    obtain ⟨h, hh, a, ha, rfl⟩ := hg
    let j : K := ⟨h, hh⟩
    let q₀ : RegularElementaryCosets E r := QuotientGroup.mk j⁻¹
    have hmem (q : RegularElementaryCosets E r) :
        (q.out : L)⁻¹ * (h⁻¹ * diagonalUnits a * τG h) * τG (q.out : L) ∈ D ↔ q = q₀ := by
      have he : (q.out : L)⁻¹ * (h⁻¹ * diagonalUnits a * τG h) * τG (q.out : L) =
          ((j * q.out : K) : L)⁻¹ * diagonalUnits a * τG ((j * q.out : K) : L) := by
        change _ = (h * (q.out : L))⁻¹ * diagonalUnits a * τG (h * (q.out : L))
        rw [map_mul]
        group
      rw [he, twistedConj_weightedDiagonal_mem_doubleCoset_iff E τ π ν hπ hν ha]
      have hq : q₀ = (q.out : RegularElementaryCosets E r) ↔ ↑(j * q.out) ∈ I := by
        change (↑j⁻¹ : RegularElementaryCosets E r) = _ ↔ _
        rw [QuotientGroup.eq, inv_inv]
        rfl
      rw [QuotientGroup.out_eq' q] at hq
      exact hq.symm.trans eq_comm
    rw [Finset.sum_eq_single q₀]
    · rw [Set.indicator_of_mem ((hmem q₀).2 rfl)]
    · intro q _ hq
      rw [Set.indicator_of_notMem (fun hq' => hq ((hmem q).1 hq'))]
    · simp
  · rw [Set.indicator_of_notMem hg]
    symm
    apply Finset.sum_eq_zero
    intro q _
    rw [Set.indicator_of_notMem (fun hq =>
      hg (mem_support_of_twistedConj_mem_doubleCoset E τ π ν hπ hν q.out hq))]

/-- Finite test-function decomposition at every strict weight. -/
def RegularElementaryCosetDecompositionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : PadicField.{u} p) (r : ℕ)
    (τ : E.Carrier ≃ₐ[Padic p] E.Carrier) (π : E.Carrierˣ)
    (hπ : E.canonicalTopologicalData.ord (π : E.Carrier) = 1)
    (ν : Fin (r + 1) → ℤ) (hν : StrictAnti ν),
    regularElementaryTest E τ π hπ ν hν =
      ∑ q : RegularElementaryCosets E r, regularElementaryCosetTest E τ π ν
        (q.out : GeneralLinear (r + 1) E.Carrier)

theorem regularElementaryCosetDecomposition : RegularElementaryCosetDecompositionStatement.{u} :=
  fun _ _ E _ τ π hπ ν hν => regularElementaryTest_eq_sum_cosets E τ π ν hπ hν

end Langlands.BaseChange
