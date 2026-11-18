import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FreeSquareZeroBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteDomainIdealDescent
import Langlands.Geometry.Analytic.GeneralizedAffinoid.ClosedSubmodules

/-! # Closed ideals in the linear part of the finite free square-zero algebra -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FreeSquareZero

open TrivSqZeroExt

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K} {n : ℕ}

/-- The degree-one element with the specified coefficient vector. -/
def linearElement (a : Fin n → A) : algebra K A n :=
  (coordinateEquiv K A n).symm (inr a)

@[simp] theorem coordinateEquiv_linearElement (a : Fin n → A) :
    coordinateEquiv K A n (linearElement a) = inr a :=
  (coordinateEquiv K A n).apply_symm_apply _

/-- Embed a coefficient submodule as an ideal entirely in degree one. -/
def ideal (S : Submodule A (Fin n → A)) : Ideal (algebra K A n) where
  carrier := {x | (coordinateEquiv K A n x).fst = 0 ∧ (coordinateEquiv K A n x).snd ∈ S}
  zero_mem' := by
    change ((coordinateEquiv K A n).toAlgEquiv 0).fst = 0 ∧
      ((coordinateEquiv K A n).toAlgEquiv 0).snd ∈ S
    rw [map_zero, fst_zero, snd_zero]
    exact ⟨rfl, S.zero_mem⟩
  add_mem' {x y} hx hy := by
    change (coordinateEquiv K A n x).fst = 0 ∧ (coordinateEquiv K A n x).snd ∈ S at hx
    change (coordinateEquiv K A n y).fst = 0 ∧ (coordinateEquiv K A n y).snd ∈ S at hy
    change ((coordinateEquiv K A n).toAlgEquiv (x + y)).fst = 0 ∧
      ((coordinateEquiv K A n).toAlgEquiv (x + y)).snd ∈ S
    rw [map_add, fst_add, snd_add, hx.1, hy.1, add_zero]
    exact ⟨rfl, S.add_mem hx.2 hy.2⟩
  smul_mem' r x hx := by
    change (coordinateEquiv K A n x).fst = 0 ∧ (coordinateEquiv K A n x).snd ∈ S at hx
    change ((coordinateEquiv K A n).toAlgEquiv (r * x)).fst = 0 ∧
      ((coordinateEquiv K A n).toAlgEquiv (r * x)).snd ∈ S
    rw [map_mul, fst_mul, snd_mul, hx.1, mul_zero, MulOpposite.op_zero, zero_smul, add_zero]
    exact ⟨rfl, S.smul_mem _ hx.2⟩

@[simp] theorem mem_ideal (S : Submodule A (Fin n → A)) (x : algebra K A n) :
    x ∈ ideal S ↔ (coordinateEquiv K A n x).fst = 0 ∧ (coordinateEquiv K A n x).snd ∈ S :=
  Iff.rfl

@[simp] theorem linearElement_mem_ideal (S : Submodule A (Fin n → A)) (a : Fin n → A) :
    linearElement a ∈ ideal S ↔ a ∈ S := by
  simp only [mem_ideal, coordinateEquiv_linearElement, fst_inr, snd_inr, true_and]

/-- The coefficient ideal is closed for the actual presentation norm. -/
theorem isClosed_ideal (S : Submodule A (Fin n → A)) : IsClosed (ideal S : Set (algebra K A n)) := by
  let e := (coordinateEquiv K A n).toBoundedAlgHom
  have hfst : Continuous (fst : Coordinates A n → A) :=
    AddMonoidHomClass.continuous_of_bound (fstHom K A (Fin n → A)) 1
      fun x => by
        change ‖x.fst‖ ≤ 1 * ‖x‖
        simpa only [one_mul] using norm_fst_le x
  have hsnd : Continuous (snd : Coordinates A n → Fin n → A) :=
    AddMonoidHomClass.continuous_of_bound (sndHom A (Fin n → A)) 1
      fun x => by
        change ‖x.snd‖ ≤ 1 * ‖x‖
        simpa only [one_mul] using norm_snd_le x
  exact (isClosed_eq (hfst.comp e.continuous) continuous_const).inter
    ((isClosed_submodule_pi A S).preimage (hsnd.comp e.continuous))

@[simp] theorem map_linearElement (f : BoundedAlgHom K A B) (a : Fin n → A) :
    map f n (linearElement a) = linearElement (fun j => f (a j)) := by
  apply (coordinateEquiv K B n).toAlgEquiv.injective
  rw [coordinateEquiv_map, coordinateEquiv_linearElement, coordinateEquiv_linearElement,
    coordinateMap_inr]

/-- Closed extension of a linear ideal amounts to taking the new coefficient
span of the coordinatewise images. -/
theorem closedIdealMap_ideal (f : BoundedAlgHom K A B) (S : Submodule A (Fin n → A)) :
    (map f n).closedIdealMap (ideal S) =
      ideal (Submodule.span B ((fun a : Fin n → A => fun j => f (a j)) '' (S : Set _))) := by
  let T := Submodule.span B ((fun a : Fin n → A => fun j => f (a j)) '' (S : Set _))
  let J := (map f n).closedIdealMap (ideal S)
  refine le_antisymm ?_ ?_
  · apply ((map f n).closedIdealMap_le_iff (ideal S) (ideal T) (isClosed_ideal T)).mpr
    intro x hx
    obtain ⟨hx₀, hx₁⟩ := (mem_ideal S x).1 hx
    change map f n x ∈ ideal T
    rw [mem_ideal, coordinateEquiv_map, coordinateMap_fst, hx₀]
    exact ⟨map_zero f.toAlgHom, Submodule.subset_span ⟨_, hx₁, rfl⟩⟩
  · intro x hx
    obtain ⟨hx₀, hx₁⟩ := (mem_ideal T x).1 hx
    have hlin : x = linearElement (coordinateEquiv K B n x).snd := by
      apply (coordinateEquiv K B n).toAlgEquiv.injective
      rw [coordinateEquiv_linearElement]
      exact TrivSqZeroExt.ext hx₀ rfl
    rw [hlin]
    change linearElement (coordinateEquiv K B n x).snd ∈ J
    refine Submodule.span_induction (p := fun a _ => linearElement a ∈ J) ?_ ?_ ?_ ?_ hx₁
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_linearElement]
      exact (map f n).mem_closedIdealMap ((linearElement_mem_ideal S a).mpr ha)
    · have hz : linearElement (0 : Fin n → B) = 0 := by
        change (coordinateEquiv K B n).symm.toAlgEquiv (inr (0 : Fin n → B)) = 0
        rw [inr_zero, map_zero]
      exact hz ▸ J.zero_mem
    · intro a b _ _ ha hb
      have hab : linearElement (a + b) = linearElement a + linearElement b := by
        change (coordinateEquiv K B n).symm.toAlgEquiv (inr (a + b)) = _
        rw [inr_add, map_add]
        rfl
      exact hab ▸ J.add_mem ha hb
    · intro r a _ ha
      have hra : linearElement (r • a) = baseMap K B n r * linearElement a := by
        apply (coordinateEquiv K B n).toAlgEquiv.injective
        rw [map_mul, coordinateEquiv_baseMap, coordinateEquiv_linearElement,
          coordinateEquiv_linearElement, inl_mul_inr]
      exact hra ▸ J.mul_mem_left _ ha

end Langlands.Analytic.PresentedAffinoidAlgebra.FreeSquareZero
