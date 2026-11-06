import Langlands.Weil.Representation.Induction
import Langlands.Weil.Representation.DualClasses
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Actual contragredients and finite-index induction

The sum of evaluation pairings on right cosets gives the dual-induction
equivalence on the existing equivariant-function construction.
-/

noncomputable section

open scoped Classical

universe uK uG uV

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

namespace Induction

/-- Right multiplication permutes the actual right cosets used by
equivariant-function induction. -/
def cosetRightMul (S : Subgroup G) (g : G) : Cosets S ≃ Cosets S where
  toFun := Quotient.map (fun x => x * g) (by
    intro a b hab
    apply QuotientGroup.rightRel_apply.mpr
    simpa [mul_inv_rev, mul_assoc] using QuotientGroup.rightRel_apply.mp hab)
  invFun := Quotient.map (fun x => x * g⁻¹) (by
    intro a b hab
    apply QuotientGroup.rightRel_apply.mpr
    simpa [mul_inv_rev, mul_assoc] using QuotientGroup.rightRel_apply.mp hab)
  left_inv q := Quotient.inductionOn q (fun a => by
    change coset S ((a * g) * g⁻¹) = coset S a
    simp [mul_assoc])
  right_inv q := Quotient.inductionOn q (fun a => by
    change coset S ((a * g⁻¹) * g) = coset S a
    simp [mul_assoc])

theorem cosetRightMul_apply (S : Subgroup G) (g : G) (q : Cosets S) :
    cosetRightMul S g q = coset S (q.out * g) := by
  conv_lhs => rw [← q.out_eq]
  rfl

end Induction

variable (S : Subgroup G)

private theorem pointwise_dual_pairing_mul
    (A : FiniteRepresentation.{uK, uG, uV} K S)
    (f : Representation.coindV S.subtype A.representation.dual) (v : Representation.coindV S.subtype A.representation) (s : S) (g : G) :
    (DFunLike.coe (F := Module.Dual K A) (f.val ((s : G) * g))) (v.val ((s : G) * g)) = (DFunLike.coe (F := Module.Dual K A) (f.val g)) (v.val g) := by
  have hf : f.val ((s : G) * g) = A.representation.dual s (f.val g) :=
    f.property s g
  have hv : v.val ((s : G) * g) = A.representation s (v.val g) :=
    v.property s g
  rw [hf, hv]
  change (DFunLike.coe (F := Module.Dual K A) (f.val g)) (A.representation s⁻¹ (A.representation s (v.val g))) = _
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

private theorem pointwise_dual_pairing_coset
    (A : FiniteRepresentation.{uK, uG, uV} K S)
    (f : Representation.coindV S.subtype A.representation.dual) (v : Representation.coindV S.subtype A.representation) (g : G) :
    (DFunLike.coe (F := Module.Dual K A) (f.val g)) (v.val g) =
      (DFunLike.coe (F := Module.Dual K A) (f.val (Induction.coset S g).out)) (v.val (Induction.coset S g).out) := by
  simpa only [Induction.factor_mul_out] using
    pointwise_dual_pairing_mul S A f v (Induction.factor S g)
      (Induction.coset S g).out

variable [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The sum of the actual dual evaluation pairings in right-coset
coordinates, viewed as a linear map to the full algebraic dual. -/
def induceDualPairing (A : FiniteRepresentation.{uK, uG, uV} K S) :
    Representation.coindV S.subtype A.representation.dual →ₗ[K]
      Module.Dual K (Representation.coindV S.subtype A.representation) where
  toFun f := {
    toFun v := ∑ q : Induction.Cosets S, (DFunLike.coe (F := Module.Dual K A) (f.val q.out)) (v.val q.out)
    map_add' v w := by
      simp [Finset.sum_add_distrib]
    map_smul' r v := by
      simp [Finset.mul_sum] }
  map_add' f f' := by
    ext v
    simp [Finset.sum_add_distrib]
  map_smul' r f := by
    ext v
    simp [Finset.mul_sum]

private theorem induceDualPairing_invariant
    (A : FiniteRepresentation.{uK, uG, uV} K S)
    (f : Representation.coindV S.subtype A.representation.dual) (v : Representation.coindV S.subtype A.representation) (g : G) :
    induceDualPairing S A ((Representation.coind S.subtype A.representation.dual) g f)
        ((Representation.coind S.subtype A.representation) g v) =
      induceDualPairing S A f v := by
  change (∑ q : Induction.Cosets S, (DFunLike.coe (F := Module.Dual K A) (f.val (q.out * g))) (v.val (q.out * g))) =
    ∑ q : Induction.Cosets S, (DFunLike.coe (F := Module.Dual K A) (f.val q.out)) (v.val q.out)
  calc
    _ = ∑ q : Induction.Cosets S,
        (DFunLike.coe (F := Module.Dual K A) (f.val (Induction.cosetRightMul S g q).out))
          (v.val (Induction.cosetRightMul S g q).out) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Induction.cosetRightMul_apply]
      exact pointwise_dual_pairing_coset S A f v (q.out * g)
    _ = _ := (Induction.cosetRightMul S g).sum_comp
      (fun q : Induction.Cosets S => (f.val q.out) (v.val q.out))

/-- The coset evaluation pairing is an actual intertwiner to the
contragredient of induction. -/
def induceDualMap (A : FiniteRepresentation.{uK, uG, uV} K S) :
    (Representation.coind S.subtype A.representation.dual).IntertwiningMap
      (Representation.coind S.subtype A.representation).dual where
  toLinearMap := induceDualPairing S A
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    change induceDualPairing S A ((Representation.coind S.subtype A.representation.dual) g f) v =
      induceDualPairing S A f ((Representation.coind S.subtype A.representation) g⁻¹ v)
    have h := induceDualPairing_invariant S A f
      ((Representation.coind S.subtype A.representation) g⁻¹ v) g
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] using h

private theorem induceDualPairing_single
    (A : FiniteRepresentation.{uK, uG, uV} K S) (f : Representation.coindV S.subtype A.representation.dual)
    (q : Induction.Cosets S) (v : A) :
    induceDualPairing S A f
        ((Induction.coordinates S A).symm (Pi.single q v)) =
      (DFunLike.coe (F := Module.Dual K A) (f.val q.out)) v := by
  classical
  change (∑ r : Induction.Cosets S,
    (DFunLike.coe (F := Module.Dual K A) (f.val r.out)) ((Induction.coordinates S A
      ((Induction.coordinates S A).symm (Pi.single q v))) r)) = _
  rw [LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply, apply_ite]

theorem induceDualPairing_injective
    (A : FiniteRepresentation.{uK, uG, uV} K S) :
    Function.Injective (induceDualPairing S A) := by
  classical
  intro f f' h
  apply (Induction.coordinates S (dual A)).injective
  funext q
  apply LinearMap.ext
  intro v
  have hv := congrArg (fun l : Module.Dual K (Representation.coindV S.subtype A.representation) =>
    l ((Induction.coordinates S A).symm (Pi.single q v))) h
  rw [induceDualPairing_single, induceDualPairing_single] at hv
  change (f.val q.out) v = (f'.val q.out) v
  exact hv

/-- Finite-index induction of the actual contragredient is equivalent to
the actual contragredient of induction. No equivariant splitting or
semisimplicity hypothesis is used. -/
def induceDualEquiv (A : FiniteRepresentation.{uK, uG, uV} K S) :
    Equiv (induce S (dual A)) (dual (induce S A)) where
  toLinearEquiv := LinearEquiv.ofInjectiveOfFinrankEq
    (induceDualPairing S A) (induceDualPairing_injective S A) (by
      change (induce S (dual A)).rank = (dual (induce S A)).rank
      rw [rank_induce, rank_dual, rank_dual, rank_induce])
  isIntertwining' := (induceDualMap S A).isIntertwining'

end Langlands.FiniteRepresentation
