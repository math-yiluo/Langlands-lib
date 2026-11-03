import Langlands.GroupScheme.GaloisPointDescent
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Finite-Galois point norms on actual commutative affine group schemes -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.GaloisPoint

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The product of all conjugates in the actual extension-field point group. -/
def conjugateProduct :
    affinePoints T.toGrp (CommAlgCat.of k L) →* affinePoints T.toGrp (CommAlgCat.of k L) where
  toFun x := ∏ σ : L ≃ₐ[k] L, conjugate k L T.toGrp σ x
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]

@[simp] theorem conjugateProduct_apply (x : affinePoints T.toGrp (CommAlgCat.of k L)) :
    conjugateProduct k L T x = ∏ σ : L ≃ₐ[k] L, conjugate k L T.toGrp σ x := rfl

/-- Left multiplication permutes the full automorphism group, so the product is fixed. -/
theorem conjugateProduct_fixed (x : affinePoints T.toGrp (CommAlgCat.of k L)) :
    conjugateProduct k L T x ∈ fixedSubgroup k L T.toGrp := by
  intro σ
  rw [conjugateProduct_apply, map_prod]
  simp only [← conjugate_mul]
  exact Fintype.prod_equiv (Equiv.mulLeft σ) _ _ (fun _ => rfl)

variable [IsGalois k L] [IsAffine T.X.left]

/-- The point norm descends the full Galois product to the actual base-field points. -/
def norm : affinePoints T.toGrp (CommAlgCat.of k L) →*
    affinePoints T.toGrp (CommAlgCat.of k k) :=
  (fixedEquiv k L T.toGrp).symm.toMonoidHom.comp
    ((conjugateProduct k L T).codRestrict (fixedSubgroup k L T.toGrp)
      (conjugateProduct_fixed k L T))

/-- Extending the norm gives exactly the product of all Galois conjugates. -/
@[simp] theorem extend_norm (x : affinePoints T.toGrp (CommAlgCat.of k L)) :
    extend k L T.toGrp (norm k L T x) =
      ∏ σ : L ≃ₐ[k] L, conjugate k L T.toGrp σ x :=
  extend_fixedEquiv_symm k L T.toGrp _

/-- The norm of an extended base point is its extension-degree power. -/
@[simp] theorem norm_extend (x : affinePoints T.toGrp (CommAlgCat.of k k)) :
    norm k L T (extend k L T.toGrp x) = x ^ Module.finrank k L := by
  apply extend_injective k L T.toGrp
  rw [extend_norm, map_pow]
  simp only [conjugate_extend, Finset.prod_const, Finset.card_univ]
  rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]

variable {T} {U : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An actual commutative-group-scheme homomorphism commutes with the point norm. -/
theorem norm_naturality [IsAffine U.X.left] (f : T ⟶ U)
    (x : affinePoints T.toGrp (CommAlgCat.of k L)) :
    affinePointsTarget T.toGrp (CommGroupScheme.groupHom f) (CommAlgCat.of k k)
        (norm k L T x) =
      norm k L U (affinePointsTarget T.toGrp (CommGroupScheme.groupHom f)
        (CommAlgCat.of k L) x) := by
  apply extend_injective k L U.toGrp
  have hn := DFunLike.congr_fun
    (affinePointsTarget_naturality T.toGrp (CommGroupScheme.groupHom f)
      (CommAlgCat.ofHom (Algebra.ofId k L))) (norm k L T x)
  change extend k L U.toGrp
    (affinePointsTarget T.toGrp (CommGroupScheme.groupHom f) _ (norm k L T x)) =
      affinePointsTarget T.toGrp (CommGroupScheme.groupHom f) _
        (extend k L T.toGrp (norm k L T x)) at hn
  rw [hn, extend_norm, map_prod, extend_norm]
  apply Finset.prod_congr rfl
  intro σ _
  exact (DFunLike.congr_fun
    (affinePointsTarget_naturality T.toGrp (CommGroupScheme.groupHom f)
      (CommAlgCat.ofHom σ.toAlgHom)) x).symm

end Langlands.GroupScheme.GaloisPoint
