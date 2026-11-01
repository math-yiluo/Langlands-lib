import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Maps.Basic

/-! # Locally constant descent through an actual quotient map -/

noncomputable section

universe u v w t

namespace Langlands.LocallyConstantQuotient

open Topology

variable {X : Type u} {Y : Type v} {A : Type w}
  [TopologicalSpace X] [TopologicalSpace Y]
  (q : X → Y) (hq : IsQuotientMap q)

include hq in
/-- The quotient topology detects local constancy without a coefficient topology. -/
theorem isLocallyConstant_iff (f : Y → A) :
    IsLocallyConstant f ↔ IsLocallyConstant (f ∘ q) := by
  constructor
  · intro hf
    exact hf.comp_continuous hq.continuous
  · intro hf s
    exact hq.isCoinducing.isOpen_preimage.mp (hf s)

/-- Pullback along the original quotient. -/
def pullback (f : LocallyConstant Y A) : LocallyConstant X A :=
  LocallyConstant.comap ⟨q, hq.continuous⟩ f

@[simp]
theorem pullback_apply (f : LocallyConstant Y A) (x : X) :
    pullback q hq f x = f (q x) := rfl

theorem pullback_factorsThrough (f : LocallyConstant Y A) :
    Function.FactorsThrough (pullback q hq f) q :=
  fun _ _ h => congrArg f h

/-- Choose a preimage, then prove independence and local constancy from the
literal fiber equations and quotient topology. No nonemptiness is required. -/
def descend (f : LocallyConstant X A) (hf : Function.FactorsThrough f q) :
    LocallyConstant Y A where
  toFun y := f (Function.surjInv hq.surjective y)
  isLocallyConstant := by
    apply (isLocallyConstant_iff q hq _).mpr
    have heq : (fun y => f (Function.surjInv hq.surjective y)) ∘ q = f := by
      funext x
      exact hf (Function.surjInv_eq hq.surjective (q x))
    rw [heq]
    exact f.isLocallyConstant

@[simp]
theorem descend_apply (f : LocallyConstant X A) (hf : Function.FactorsThrough f q)
    (x : X) : descend q hq f hf (q x) = f x :=
  hf (Function.surjInv_eq hq.surjective (q x))

@[simp]
theorem pullback_descend (f : LocallyConstant X A)
    (hf : Function.FactorsThrough f q) :
    pullback q hq (descend q hq f hf) = f := by
  ext x
  exact descend_apply q hq f hf x

@[simp]
theorem descend_pullback (f : LocallyConstant Y A) :
    descend q hq (pullback q hq f) (pullback_factorsThrough q hq f) = f := by
  ext y
  obtain ⟨x, rfl⟩ := hq.surjective y
  exact descend_apply q hq _ _ x

/-- Downstairs functions are exactly upstairs functions constant on quotient fibers. -/
def descentEquiv :
    LocallyConstant Y A ≃
      {f : LocallyConstant X A // Function.FactorsThrough f q} where
  toFun f := ⟨pullback q hq f, pullback_factorsThrough q hq f⟩
  invFun f := descend q hq f.val f.property
  left_inv := descend_pullback q hq
  right_inv f := Subtype.ext (pullback_descend q hq f.val f.property)

/-- Descent is uniquely characterized by its values on the original quotient. -/
theorem descend_unique (f : LocallyConstant X A)
    (hf : Function.FactorsThrough f q) (g : LocallyConstant Y A)
    (hg : ∀ x, g (q x) = f x) : g = descend q hq f hf := by
  ext y
  obtain ⟨x, rfl⟩ := hq.surjective y
  exact (hg x).trans (descend_apply q hq f hf x).symm

variable {B : Type t}

/-- Postcomposition by any function of coefficient sets commutes with descent. -/
theorem descend_map (f : LocallyConstant X A)
    (hf : Function.FactorsThrough f q) (p : A → B) :
    (descend q hq f hf).map p =
      descend q hq (f.map p) (hf.comp_left p) := by
  apply descend_unique q hq (f.map p) (hf.comp_left p)
  intro x
  exact congrArg p (descend_apply q hq f hf x)

end Langlands.LocallyConstantQuotient
