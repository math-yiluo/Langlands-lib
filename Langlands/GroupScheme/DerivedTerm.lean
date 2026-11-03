import Langlands.GroupScheme.SmoothProducts
import Mathlib.GroupTheory.Solvable

/-! # Finite terms for the derived series of a group scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme

/-- Finite terms whose values belong to the indicated derived-series subgroup.
The two branches of a binary operation have independent inputs. -/
inductive DerivedTerm : ℕ → Type
  | atom : DerivedTerm 0
  | one (n : ℕ) : DerivedTerm n
  | mul {n : ℕ} (s t : DerivedTerm n) : DerivedTerm n
  | inv {n : ℕ} (s : DerivedTerm n) : DerivedTerm n
  | comm {n : ℕ} (s t : DerivedTerm n) : DerivedTerm (n + 1)

namespace DerivedTerm

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- The actual relative scheme of inputs of a finite derived term. -/
abbrev domain : {n : ℕ} → DerivedTerm n → Over S
  | _, .atom => G.X
  | _, .one _ => 𝟙_ (Over S)
  | _, .mul s t => domain s ⊗ domain t
  | _, .inv s => domain s
  | _, .comm s t => domain s ⊗ domain t

/-- The scheme morphism evaluating a finite derived term. -/
def evaluation : {n : ℕ} → (t : DerivedTerm n) → domain G t ⟶ G.X
  | _, .atom => 𝟙 G.X
  | _, .one _ => 1
  | _, .mul s t =>
      (fst (domain G s) (domain G t) ≫ evaluation s) *
        (snd (domain G s) (domain G t) ≫ evaluation t)
  | _, .inv s => (evaluation s)⁻¹
  | _, .comm s t =>
      (⁅fst (domain G s) (domain G t) ≫ evaluation s,
        snd (domain G s) (domain G t) ≫ evaluation t⁆ :
          domain G s ⊗ domain G t ⟶ G.X)

/-- Term domains are smooth whenever the original group scheme is smooth. -/
theorem smooth_domain {n : ℕ} (t : DerivedTerm n) (hG : Smooth G.X.hom) :
    Smooth (domain G t).hom := by
  induction t with
  | atom => exact hG
  | one n => exact inferInstanceAs (Smooth (𝟙 S))
  | mul s t hs ht => exact smooth_tensor _ _ hs ht
  | inv s hs => exact hs
  | comm s t hs ht => exact smooth_tensor _ _ hs ht

/-- Every term evaluation belongs to the matching derived-series subgroup. -/
theorem evaluation_mem {n : ℕ} (t : DerivedTerm n) {T : Over S}
    (a : T ⟶ domain G t) : a ≫ evaluation G t ∈ derivedSeries (T ⟶ G.X) n := by
  induction t with
  | atom => trivial
  | one n => simpa only [evaluation, MonObj.comp_one] using
      (derivedSeries (T ⟶ G.X) n).one_mem
  | mul s t hs ht =>
      simpa only [evaluation, MonObj.comp_mul, ← Category.assoc] using
        (derivedSeries (T ⟶ G.X) _).mul_mem (hs (a ≫ fst _ _)) (ht (a ≫ snd _ _))
  | inv s hs =>
      simpa only [evaluation, GrpObj.comp_inv] using
        (derivedSeries (T ⟶ G.X) _).inv_mem (hs a)
  | comm s t hs ht =>
      simpa only [evaluation, commutatorElement_def, MonObj.comp_mul, GrpObj.comp_inv,
        ← Category.assoc, derivedSeries_succ] using
        (Subgroup.commutator_mem_commutator (hs (a ≫ fst _ _)) (ht (a ≫ snd _ _)))

/-- Finite term evaluations exhaust every derived-series subgroup on every test scheme. -/
theorem exists_evaluation {T : Over S} (n : ℕ) (x : T ⟶ G.X)
    (hx : x ∈ derivedSeries (T ⟶ G.X) n) :
    ∃ (t : DerivedTerm n) (a : T ⟶ domain G t), a ≫ evaluation G t = x := by
  induction n generalizing x with
  | zero => exact ⟨.atom, x, Category.comp_id x⟩
  | succ n ih =>
      rw [derivedSeries_succ, Subgroup.commutator_def] at hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
          obtain ⟨y, hy, z, hz, rfl⟩ := hx
          obtain ⟨s, a, ha⟩ := ih y hy
          obtain ⟨t, b, hb⟩ := ih z hz
          refine ⟨.comm s t, lift a b, ?_⟩
          simp only [evaluation, commutatorElement_def, MonObj.comp_mul,
            GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd, ha, hb]
      | one => exact ⟨.one (n + 1), toUnit T, MonObj.comp_one _⟩
      | mul x y hx hy hxt hyt =>
          obtain ⟨s, a, ha⟩ := hxt
          obtain ⟨t, b, hb⟩ := hyt
          refine ⟨.mul s t, lift a b, ?_⟩
          simp only [evaluation, MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd, ha, hb]
      | inv x hx hxt =>
          obtain ⟨s, a, ha⟩ := hxt
          refine ⟨.inv s, a, ?_⟩
          simp only [evaluation, GrpObj.comp_inv, ha]

end DerivedTerm
end Langlands.GroupScheme
