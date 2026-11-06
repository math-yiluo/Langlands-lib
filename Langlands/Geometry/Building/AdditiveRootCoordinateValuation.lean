import Langlands.Geometry.Building.IntegerValuation
import Langlands.Geometry.Building.RootDatumValuation
import Langlands.FieldTheory.HenselianSeparableIntegerAddValuation
import Mathlib.Data.Set.Card

/-! # Additive root coordinates and normalized root values -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {a : characterLattice S}
  {L : Type v} [Field L]
  (omega : AddValuation L (WithTop ℝ))
  (e : Multiplicative L ≃* rootGroupPoints i a)

/-- Transfer an additive coordinate valuation to the actual rational root group,
with the prescribed infinite normalization away from that root group. -/
def additiveRootValue (g : rationalPoints G) : WithTop ℝ := by
  classical
  exact if hg : g ∈ rootGroupPoints i a then omega (e.symm ⟨g, hg⟩).toAdd else ⊤

@[simp] theorem additiveRootValue_of_mem (g : rootGroupPoints i a) :
    additiveRootValue omega e g = omega (e.symm g).toAdd := by
  simp only [additiveRootValue, dite_eq_left g.property]

theorem additiveRootValue_of_not_mem {g : rationalPoints G}
    (hg : g ∉ rootGroupPoints i a) : additiveRootValue omega e g = ⊤ := by
  simp only [additiveRootValue, dite_eq_right hg]

@[simp] theorem additiveRootValue_coordinate (x : L) :
    additiveRootValue omega e (e (Multiplicative.ofAdd x)) = omega x := by
  rw [additiveRootValue_of_mem, e.symm_apply_apply]
  rfl

@[simp] theorem additiveRootValue_one :
    additiveRootValue omega e 1 = ⊤ := by
  simpa using additiveRootValue_coordinate omega e 0

theorem additiveRootValue_eq_top_iff {g : rationalPoints G}
    (hg : g ∈ rootGroupPoints i a) :
    additiveRootValue omega e g = ⊤ ↔ g = 1 := by
  rw [additiveRootValue_of_mem omega e ⟨g, hg⟩, AddValuation.top_iff]
  constructor
  · intro h
    have h' : e.symm ⟨g, hg⟩ = 1 := h
    have he := congrArg e h'
    exact congrArg Subtype.val (by simpa only [e.apply_symm_apply, map_one] using he)
  · intro h
    subst g
    simp

theorem additiveRootValue_mul_ge {g h : rationalPoints G}
    (hg : g ∈ rootGroupPoints i a) (hh : h ∈ rootGroupPoints i a) :
    min (additiveRootValue omega e g) (additiveRootValue omega e h) ≤
      additiveRootValue omega e (g * h) := by
  rw [additiveRootValue_of_mem omega e ⟨g, hg⟩,
    additiveRootValue_of_mem omega e ⟨h, hh⟩,
    additiveRootValue_of_mem omega e ⟨g * h, (rootGroupPoints i a).mul_mem hg hh⟩]
  change min (omega (e.symm ⟨g, hg⟩).toAdd) (omega (e.symm ⟨h, hh⟩).toAdd) ≤
    omega (e.symm (⟨g, hg⟩ * ⟨h, hh⟩)).toAdd
  rw [map_mul, toAdd_mul]
  exact omega.map_add _ _

theorem additiveRootValue_inv {g : rationalPoints G}
    (hg : g ∈ rootGroupPoints i a) :
    additiveRootValue omega e g⁻¹ = additiveRootValue omega e g := by
  rw [additiveRootValue_of_mem omega e ⟨g, hg⟩,
    additiveRootValue_of_mem omega e ⟨g⁻¹, (rootGroupPoints i a).inv_mem hg⟩]
  change omega (e.symm (⟨g, hg⟩⁻¹)).toAdd = _
  rw [map_inv, toAdd_inv, omega.map_neg]

/-- Every real threshold defines an actual subgroup of the rational root group. -/
def additiveRootFiltration (r : ℝ) : Subgroup (rationalPoints G) where
  carrier := {g | g ∈ rootGroupPoints i a ∧ (r : WithTop ℝ) ≤ additiveRootValue omega e g}
  one_mem' := ⟨(rootGroupPoints i a).one_mem, by simp⟩
  mul_mem' hg hh := ⟨(rootGroupPoints i a).mul_mem hg.1 hh.1,
    (le_min hg.2 hh.2).trans (additiveRootValue_mul_ge omega e hg.1 hh.1)⟩
  inv_mem' hg := ⟨(rootGroupPoints i a).inv_mem hg.1, by
    rw [additiveRootValue_inv omega e hg.1]; exact hg.2⟩

@[simp] theorem mem_additiveRootFiltration (r : ℝ) (g : rationalPoints G) :
    g ∈ additiveRootFiltration omega e r ↔
      g ∈ rootGroupPoints i a ∧ (r : WithTop ℝ) ≤ additiveRootValue omega e g := Iff.rfl

/-- A scalar coordinate description of conjugation gives the exact value shift. -/
theorem additiveRootValue_conjugation_of_scalar
    (t : rationalPoints G) (c : L)
    (hc : ∀ x : L, t * (e (Multiplicative.ofAdd x) : rationalPoints G) * t⁻¹ =
      (e (Multiplicative.ofAdd (c * x)) : rationalPoints G))
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints i a) :
    additiveRootValue omega e (t * g * t⁻¹) =
      additiveRootValue omega e g + omega c := by
  obtain ⟨x, hx⟩ := e.surjective ⟨g, hg⟩
  have h : (e x : rationalPoints G) = g := congrArg Subtype.val hx
  have hc' : t * (e x : rationalPoints G) * t⁻¹ =
      (e (Multiplicative.ofAdd (c * x.toAdd)) : rationalPoints G) := by
    simpa only [ofAdd_toAdd] using hc x.toAdd
  have hxv : additiveRootValue omega e (e x) = omega x.toAdd := by
    simpa only [ofAdd_toAdd] using additiveRootValue_coordinate omega e x.toAdd
  rw [← h, hc', additiveRootValue_coordinate, hxv, omega.map_mul, add_comm]

section Henselian

variable [Algebra k L] [Algebra.IsSeparable k L]
  (v : Valuation k (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)

/-- The normalized type-R1 value, once an actual additive coordinate is given. -/
def henselianAdditiveRootValue : rationalPoints G → WithTop ℝ :=
  additiveRootValue (FieldTheory.henselianSeparableAddValuation v hH L) e

/-- An embedded nonzero base scalar has exactly its integer apartment order. -/
theorem henselianAdditiveRootValue_base (x : kˣ) :
    henselianAdditiveRootValue e v hH
      (e (Multiplicative.ofAdd (algebraMap k L (x : k)))) =
        ((IntegerValuation.order v x : ℝ) : WithTop ℝ) := by
  rw [henselianAdditiveRootValue, additiveRootValue_coordinate,
    FieldTheory.henselianSeparableAddValuation_base v hH L (Units.ne_zero x),
    IntegerValuation.order, IntegerValuation.orderUnits_toAdd]

/-- Surjectivity on the base yields every integer among actual root values. -/
theorem henselianAdditiveRootValue_exists_integer
    (hv : Function.Surjective v) (n : ℤ) :
    ∃ g ∈ rootGroupPoints i a, henselianAdditiveRootValue e v hH g =
      ((n : ℝ) : WithTop ℝ) := by
  obtain ⟨x, hx⟩ := hv (WithZero.exp (-n))
  have hx0 : x ≠ 0 := by
    intro h
    have hz : (0 : WithZero (Multiplicative ℤ)) = WithZero.exp (-n) := by
      simpa only [h, map_zero] using hx
    exact WithZero.exp_ne_zero hz.symm
  refine ⟨e (Multiplicative.ofAdd (algebraMap k L x)),
    (e (Multiplicative.ofAdd (algebraMap k L x))).property, ?_⟩
  rw [henselianAdditiveRootValue, additiveRootValue_coordinate,
    FieldTheory.henselianSeparableAddValuation_base v hH L hx0,
    hx, WithZero.log_exp, neg_neg]

/-- In particular the type-R1 image is infinite, hence satisfies the local V0 bound. -/
theorem henselianAdditiveRootValue_image_infinite (hv : Function.Surjective v) :
    (henselianAdditiveRootValue e v hH '' (rootGroupPoints i a : Set (rationalPoints G))).Infinite := by
  have hinj : Function.Injective (fun n : ℤ => ((n : ℝ) : WithTop ℝ)) := by
    intro m n h
    exact_mod_cast WithTop.coe_injective h
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  exact henselianAdditiveRootValue_exists_integer e v hH hv n

theorem henselianAdditiveRootValue_three_le_encard (hv : Function.Surjective v) :
    3 ≤ (henselianAdditiveRootValue e v hH ''
      (rootGroupPoints i a : Set (rationalPoints G))).encard := by
  rw [(henselianAdditiveRootValue_image_infinite e v hH hv).encard_eq]
  exact le_top

end Henselian

end Langlands.Geometry.Building
