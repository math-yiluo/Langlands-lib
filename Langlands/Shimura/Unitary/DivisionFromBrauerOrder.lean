import Langlands.Algebra.BrauerComparison.PeriodDegree
import Langlands.Algebra.DivisionBrauerClass
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Shimura.Unitary.FiniteModels

/-! # Division from a Brauer class of full order -/

noncomputable section

universe u v w

namespace Langlands.Brauer

open CentralSimple

/-- A CSA whose Brauer period equals its reduced degree has every nonzero element
invertible. -/
theorem isUnit_of_order_eq_reducedDegree {F : Type u} [Field F] (B : CSA.{u, u} F)
    (horder : addOrderOf (classOf B) = reducedDegree F B) (x : B) (hx : x ≠ 0) :
    IsUnit x := by
  have := IsArtinianRing.of_finite F B
  obtain ⟨r, hr, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F B
  let : NeZero r := hr
  let : Algebra.IsCentral F D := isCentral_of_algEquiv_matrix e
  let C := divisionAlgebra F D
  have hclass : classOf B = classOf C :=
    (classOf_eq_of_algEquiv (B := matrix C r) e).trans (classOf_matrix C r)
  have hdegree : reducedDegree F B = r * reducedDegree F C := by
    apply Nat.mul_self_inj.mp
    rw [← finrank_eq_reducedDegree_mul_self, e.toLinearEquiv.finrank_eq, Module.finrank_matrix,
      Fintype.card_fin]
    change r * r * Module.finrank F C = _
    rw [finrank_eq_reducedDegree_mul_self]
    ac_rfl
  have hdvd : reducedDegree F B ∣ reducedDegree F C := by
    rw [← horder, hclass]
    exact addOrderOf_classOf_dvd_reducedDegree C
  have hle := Nat.le_of_dvd (reducedDegree_pos F C) hdvd
  have hrle : r ≤ 1 := Nat.le_of_mul_le_mul_right
    (by rwa [one_mul, ← hdegree]) (reducedDegree_pos F C)
  have hrone : r = 1 := le_antisymm hrle (Nat.pos_of_ne_zero (NeZero.ne r))
  subst r
  let f := e.trans (matrixOneEquiv D)
  have hfx : f x ≠ 0 := fun h => hx (f.injective (h.trans f.map_zero.symm))
  have hu : IsUnit (f x) := isUnit_iff_ne_zero.mpr hfx
  simpa only [AlgEquiv.symm_apply_apply] using hu.map f.symm

/-- The existing ring of a full-period CSA, equipped with division. -/
@[instance_reducible]
def divisionRingOfOrderEqReducedDegree {F : Type u} [Field F] (B : CSA.{u, u} F)
    (horder : addOrderOf (classOf B) = reducedDegree F B) : DivisionRing B :=
  DivisionRing.ofIsUnitOrEqZero fun x =>
    (em (x = 0)).elim Or.inr fun hx => Or.inl (isUnit_of_order_eq_reducedDegree B horder x hx)

end Langlands.Brauer

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.CentralSimple
open scoped TensorProduct

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  {A : Type w} [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A] {n : ℕ}

omit [NumberField E] [IsScalarTower E K A] in
/-- An actual completion chart of full Brauer period gives division at that place. -/
theorem isDivisionAt_of_brauer_order (D : CentralSimpleUnitaryData E K A n)
    (q : Global.FinitePlace K) (B : CSA.{v, v} (FiniteCompletion K q))
    (e : CompletedAlgebra K A q ≃ₐ[FiniteCompletion K q] B)
    (horder : addOrderOf (Brauer.classOf B) = n) : IsDivisionAt K A q := by
  let : FiniteDimensional K A := D.finite
  have hdegree : reducedDegree (FiniteCompletion K q) B = n := by
    rw [reducedDegree, ← e.toLinearEquiv.finrank_eq]
    change Nat.sqrt (Module.finrank (FiniteCompletion K q) (FiniteCompletion K q ⊗[K] A)) = n
    rw [Module.finrank_baseChange, D.dimension, pow_two, Nat.sqrt_eq]
  intro a ha
  have he : e a ≠ 0 := fun h => ha (e.injective (h.trans e.map_zero.symm))
  let := Brauer.divisionRingOfOrderEqReducedDegree B (horder.trans hdegree.symm)
  have hu : IsUnit (e a) := isUnit_iff_ne_zero.mpr he
  simpa only [AlgEquiv.symm_apply_apply] using hu.map e.symm

/-- Division at the CM places above one finite place implies global division. -/
theorem isDivision_of_isDivisionAbove (D : CentralSimpleUnitaryData E K A n)
    (p : Global.FinitePlace E) (hp : IsDivisionAbove (K := K) (A := A) p) : D.IsDivision := by
  obtain ⟨q, hq⟩ := exists_place_above (L := K) p
  exact isDivision_of_isDivisionAt D q (hp q hq)

end Langlands.Shimura.FiniteUnitary
