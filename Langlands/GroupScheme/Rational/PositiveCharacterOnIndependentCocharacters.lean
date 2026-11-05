import Langlands.GroupScheme.Rational.PositiveCharacterOnIndependentCocharactersStatement
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterLinear
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Data.Rat.Cast.Order

/-! # Positive characters on independent cocharacters -/

noncomputable section

universe u v uM uJ uI

namespace Langlands.LinearAlgebra

/-- Prescribed integer values on independent vectors in a finite integral
coordinate lattice extend to an integral functional after multiplication by
one positive integer. -/
theorem exists_integer_functional_scaled_values_of_coordinates
    {M : Type uM} [AddCommGroup M]
    {J : Type uJ} [Finite J] (e : M ≃ₗ[ℤ] (J → ℤ))
    {I : Type uI} (x : I → M) (hx : LinearIndependent ℤ x) (w : I → ℤ) :
    ∃ d : ℤ, 0 < d ∧ ∃ l : M →ₗ[ℤ] ℤ, ∀ i, l (x i) = d * w i := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  have hxZ : LinearIndependent ℤ (fun i => e (x i)) :=
    hx.map' e.toLinearMap e.ker
  have hxQ : LinearIndependent ℚ (fun i j => (e (x i) j : ℚ)) := by
    simpa only [algebraMap_int_eq, Function.comp_def, Int.coe_castRingHom] using
      (linearIndependent_algebraMap_comp_iff (S := ℚ)).mpr hxZ
  let V := J → ℚ
  let W : Submodule ℚ V := Submodule.span ℚ (Set.range (fun i j => (e (x i) j : ℚ)))
  let f : V →ₗ[ℚ] ℚ :=
    Subspace.dualLift W ((Module.Basis.span hxQ).constr ℚ (fun i => (w i : ℚ)))
  have hf (i : I) : f (fun j => (e (x i) j : ℚ)) = w i := by
    dsimp only [f]
    rw [← Module.Basis.coe_span_apply hxQ i, Subspace.dualLift_of_subtype,
      Module.Basis.constr_basis]
  let q : J → ℚ := fun j => f (Pi.single j 1)
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  choose a ha using hb
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.ne_zero b.property
  let z : J → ℤ := fun j => (b : ℤ) * a j
  let l : M →ₗ[ℤ] ℤ := (dotProductEquiv ℤ J z).comp e.toLinearMap
  have hq (y : J → ℤ) : f (fun j => (y j : ℚ)) = ∑ j, (y j : ℚ) * q j := by
    conv_lhs => rw [← Finset.univ_sum_single (fun j => (y j : ℚ))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show Pi.single j (y j : ℚ) = (y j : ℚ) • Pi.single j (1 : ℚ) by
      ext t
      by_cases h : t = j <;> simp [h]]
    simp [q]
  have ha' (j : J) : (a j : ℚ) = (b : ℤ) * q j := by
    simpa [Algebra.smul_def, algebraMap_int_eq] using ha j
  refine ⟨(b : ℤ) ^ 2, sq_pos_of_ne_zero hb0, l, fun i => ?_⟩
  have hl : (l (x i) : ℚ) = ((b : ℤ) : ℚ) ^ 2 *
      f (fun j => (e (x i) j : ℚ)) := by
    change ((∑ j, z j * e (x i) j : ℤ) : ℚ) = _
    rw [Int.cast_sum, hq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only [z]
    push_cast
    rw [ha']
    ring
  rw [hf] at hl
  exact_mod_cast hl

/-- Finite free integral lattices admit an integral functional taking prescribed
values on an independent family up to one common positive integer. -/
theorem exists_integer_functional_scaled_values
    {M : Type uM} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    {I : Type uI} (x : I → M) (hx : LinearIndependent ℤ x) (w : I → ℤ) :
    ∃ d : ℤ, 0 < d ∧ ∃ l : M →ₗ[ℤ] ℤ, ∀ i, l (x i) = d * w i :=
  exists_integer_functional_scaled_values_of_coordinates
    (Module.Free.chooseBasis ℤ M).equivFun x hx w

end Langlands.LinearAlgebra

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A finite independent family of actual cocharacters of a split torus admits
one actual character positive on every family member. -/
theorem positiveCharacterOnIndependentCocharacters :
    PositiveCharacterOnIndependentCocharactersStatement.{u,v} := by
  intro k _ T hT I _ x hx
  obtain ⟨J, hJ, ⟨e⟩⟩ := hT.exists_cocharacterCoordinates
  let _ := hJ
  obtain ⟨d, hd, l, hl⟩ :=
    Langlands.LinearAlgebra.exists_integer_functional_scaled_values_of_coordinates
      e x hx (fun _ => 1)
  obtain ⟨α, hα⟩ := hT.isPerfPair_latticePairing.bijective_left.surjective l
  refine ⟨α, fun i => ?_⟩
  have h := LinearMap.congr_fun hα (x i)
  rw [hl, mul_one] at h
  exact h.symm ▸ hd

end Langlands.GroupScheme
