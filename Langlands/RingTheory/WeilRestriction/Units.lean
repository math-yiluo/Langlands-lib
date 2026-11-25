module

public import Langlands.Algebra.Polynomial.Laurent.CoefficientMaps
public import Langlands.Algebra.Polynomial.Laurent.Smooth
public import Langlands.RingTheory.WeilRestriction.PointMultiplication
public import Langlands.RingTheory.WeilRestriction.Smooth
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! # The units of a tensor product as points of the Weil restriction of the multiplicative group

Let `B` be a commutative `A`-algebra that is finite and projective as an `A`-module. The Weil
restriction `Langlands.Algebra.WeilRestriction A B B[T;T⁻¹]` is the coordinate algebra of
`Res_{B/A} 𝔾ₘ`. Its points over a commutative `A`-algebra `T` form a group isomorphic to the unit
group of `B ⊗[A] T` (`WeilRestriction.multiplicativeGroupPoints`), naturally in `T`
(`WeilRestriction.multiplicativeGroupPoints_naturality`). A point is sent to the value at `T 1` of
the point of `B[T;T⁻¹]` over `B ⊗[A] T` that it classifies.
-/

public noncomputable section

open WithConv LaurentPolynomial
open scoped TensorProduct

namespace Langlands.Algebra.WeilRestriction

section UnitPoints

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/- The unit `f (T 1)` of `S`, with inverse `f (T (-1))`, attached to an algebra map
`f : R[T;T⁻¹] →ₐ[R] S`. -/
private def unitOfPoint (f : R[T;T⁻¹] →ₐ[R] S) : Sˣ where
  val := f (T 1)
  inv := f (T (-1))
  val_inv := by rw [← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
  inv_val := by rw [← map_mul, ← T_add, neg_add_cancel, T_zero, map_one]

/- The algebra map `R[T;T⁻¹] →ₐ[R] S` sending `T n` to `u ^ n`, from the universal property of the
group algebra of `ℤ`. -/
private def pointOfUnit (u : Sˣ) : R[T;T⁻¹] →ₐ[R] S :=
  AddMonoidAlgebra.lift R S ℤ ((Units.coeHom S).comp (zpowersHom Sˣ u))

private theorem pointOfUnit_T_one (u : Sˣ) : pointOfUnit (R := R) u (T 1) = u := by
  rw [pointOfUnit, T, AddMonoidAlgebra.lift_single, one_smul, MonoidHom.comp_apply,
    zpowersHom_apply, toAdd_ofAdd, zpow_one, Units.coeHom_apply]

/- An algebra map out of `R[T;T⁻¹]` is determined by its value at `T 1`: through the universal
property of the group algebra, this is the same statement for monoid maps out of
`Multiplicative ℤ`. -/
private theorem point_ext {f g : R[T;T⁻¹] →ₐ[R] S} (h : f (T 1) = g (T 1)) : f = g := by
  apply (AddMonoidAlgebra.lift R S ℤ).symm.injective
  apply MonoidHom.ext_mint
  simp only [AddMonoidAlgebra.lift_symm_apply, toAdd_ofAdd]
  exact h

variable (R S) in
/- Points of `𝔾ₘ = Spec R[T;T⁻¹]` with values in `S` are the units of `S`; the convolution product
of points is the product of units, since `T 1` is group-like. -/
private def unitPointsEquiv : WithConv (R[T;T⁻¹] →ₐ[R] S) ≃* Sˣ where
  toFun f := unitOfPoint f.ofConv
  invFun u := toConv (pointOfUnit u)
  left_inv f := WithConv.ofConv_injective <| point_ext <| by
    rw [ofConv_toConv, pointOfUnit_T_one]
    rfl
  right_inv u := Units.ext <| pointOfUnit_T_one u
  map_mul' f g := Units.ext <| by
    change (f * g) (T 1) = f (T 1) * g (T 1)
    rw [AlgHom.convMul_apply, comul_T, Algebra.TensorProduct.lift_tmul]

private theorem unitPointsEquiv_comp {S' : Type*} [CommSemiring S'] [Algebra R S']
    (ψ : S →ₐ[R] S') (f : R[T;T⁻¹] →ₐ[R] S) :
    unitPointsEquiv R S' (toConv (ψ.comp f)) =
      Units.map (ψ : S →* S') (unitPointsEquiv R S (toConv f)) :=
  Units.ext rfl

end UnitPoints

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B] (T : Type*) [CommRing T] [Algebra A T]

/-- **The points of the Weil restriction of `𝔾ₘ` are units.** For every commutative `A`-algebra
`T`, the points of `Res_{B/A} 𝔾ₘ` over `T` form a group isomorphic to the unit group of
`B ⊗[A] T`. -/
def multiplicativeGroupPoints :
    WithConv (WeilRestriction A B B[T;T⁻¹] →ₐ[A] T) ≃* (B ⊗[A] T)ˣ :=
  (pointsMulEquiv A B B[T;T⁻¹] T).trans (unitPointsEquiv B (B ⊗[A] T))

variable {A B T}

/-- The unit attached to a point of `Res_{B/A} 𝔾ₘ` is the value at `T 1` of the point of
`B[T;T⁻¹]` over `B ⊗[A] T` that it classifies. -/
@[simp]
theorem multiplicativeGroupPoints_apply (f : WithConv (WeilRestriction A B B[T;T⁻¹] →ₐ[A] T)) :
    (multiplicativeGroupPoints A B T f : B ⊗[A] T) =
      homEquiv A B B[T;T⁻¹] T f.ofConv (LaurentPolynomial.T 1) := by
  rw [multiplicativeGroupPoints, MulEquiv.trans_apply]
  change (pointsMulEquiv A B B[T;T⁻¹] T f).ofConv (LaurentPolynomial.T 1) = _
  rw [pointsMulEquiv_apply]

/-- Naturality of `multiplicativeGroupPoints` in the `A`-algebra `T`: post-composing with
`h : T →ₐ[A] T'` corresponds to applying `B ⊗[A] h` to units. -/
theorem multiplicativeGroupPoints_naturality {T' : Type*} [CommRing T'] [Algebra A T']
    (h : T →ₐ[A] T') (f : WithConv (WeilRestriction A B B[T;T⁻¹] →ₐ[A] T)) :
    multiplicativeGroupPoints A B T' (toConv (h.comp f.ofConv)) =
      Units.map (Algebra.TensorProduct.lTensor (S := B) B h : B ⊗[A] T →* B ⊗[A] T')
        (multiplicativeGroupPoints A B T f) := by
  rw [multiplicativeGroupPoints, MulEquiv.trans_apply, pointsMulEquiv_naturality,
    unitPointsEquiv_comp]
  rfl

end Langlands.Algebra.WeilRestriction
