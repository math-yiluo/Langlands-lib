import Langlands.CategoryTheory.Renard.HomFunctors
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Integer Hom coproducts from finite component decompositions -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.CategoryTheory.Renard

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {P : C} {I : Type w} {A : I → C}

/-- A cofan with coordinate projections is taken to a coproduct by the actual
integer-module Hom functor whenever all maps from `P` have finite component
decompositions. No abelian-category hypothesis is needed. -/
def homCofanIsColimitOfFiniteDecomposition
    (c : Cofan A) (π : ∀ i, c.pt ⟶ A i)
    (hself : ∀ i, c.inj i ≫ π i = 𝟙 (A i))
    (hother : ∀ i j, i ≠ j → c.inj i ≫ π j = 0)
    (hdec : ∀ x : P ⟶ c.pt, ∃ T : Finset I,
      (∀ i ∉ T, x ≫ π i = 0) ∧
      x = ∑ i ∈ T, (x ≫ π i) ≫ c.inj i) :
    IsColimit (Cofan.mk ((preadditiveCoyonedaInt P).obj c.pt)
      (fun i => (preadditiveCoyonedaInt P).map (c.inj i))) := by
  classical
  let H := preadditiveCoyonedaInt P
  have hdec' : ∀ x : H.obj c.pt, ∃ T : Finset I,
      (∀ i ∉ T, (H.map (π i)).hom x = 0) ∧
      x = ∑ i ∈ T, (H.map (c.inj i)).hom ((H.map (π i)).hom x) :=
    fun x => hdec x
  let Φ : ∀ t : Cofan (fun i => H.obj (A i)), H.obj c.pt → t.pt :=
    fun t x => ∑ᶠ i, (t.inj i).hom ((H.map (π i)).hom x)
  have hΦ : ∀ t x (T : Finset I), (∀ i ∉ T, (H.map (π i)).hom x = 0) →
      Φ t x = ∑ i ∈ T, (t.inj i).hom ((H.map (π i)).hom x) := by
    intro t x T hT
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hiT
    exact Function.mem_support.1 hi (by rw [hT i hiT, map_zero])
  have hadd : ∀ t x y, Φ t (x + y) = Φ t x + Φ t y := by
    intro t x y
    obtain ⟨Tx, hx, -⟩ := hdec' x
    obtain ⟨Ty, hy, -⟩ := hdec' y
    have hx' : ∀ i ∉ Tx ∪ Ty, (H.map (π i)).hom x = 0 :=
      fun i hi => hx i (fun h => hi (Finset.mem_union_left _ h))
    have hy' : ∀ i ∉ Tx ∪ Ty, (H.map (π i)).hom y = 0 :=
      fun i hi => hy i (fun h => hi (Finset.mem_union_right _ h))
    have hxy : ∀ i ∉ Tx ∪ Ty, (H.map (π i)).hom (x + y) = 0 := by
      intro i hi
      rw [map_add, hx' i hi, hy' i hi, add_zero]
    rw [hΦ t _ _ hxy, hΦ t _ _ hx', hΦ t _ _ hy', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by rw [map_add, map_add])
  let L : ∀ t : Cofan (fun i => H.obj (A i)), H.obj c.pt ⟶ t.pt := fun t =>
    ConcreteCategory.ofHom
      { toFun := Φ t
        map_add' := hadd t
        map_smul' := fun n x => by
          change Φ t ((H.obj c.pt).isModule.smul n x) = t.pt.isModule.smul n (Φ t x)
          rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
          exact (AddMonoidHom.mk' (Φ t) (hadd t)).map_zsmul n x }
  refine Cofan.IsColimit.mk _ L ?_ ?_
  · intro t i
    ext y
    change Φ t ((H.map (c.inj i)).hom y) = (t.inj i).hom y
    refine (finsum_eq_single _ i (fun j hji => ?_)).trans ?_
    · have h0 : ∀ y' : P ⟶ A i, (y' ≫ c.inj i) ≫ π j = 0 := fun y' => by
        rw [Category.assoc, hother i j (Ne.symm hji), comp_zero]
      exact (congrArg (t.inj j).hom (h0 y)).trans (map_zero _)
    · have h1 : ∀ y' : P ⟶ A i, (y' ≫ c.inj i) ≫ π i = y' := fun y' => by
        rw [Category.assoc, hself i, Category.comp_id]
      exact congrArg (t.inj i).hom (h1 y)
  · intro t m hm
    ext x
    obtain ⟨T, hT, hx⟩ := hdec' x
    change m.hom x = Φ t x
    rw [hΦ t x T hT]
    conv_lhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hm i]
    rfl

end Langlands.CategoryTheory.Renard
