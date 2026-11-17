import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Langlands.GroupScheme.HopfBaseChange
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-! # Base change for group-like-spanned Hopf algebras -/

noncomputable section

universe u v w

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.HopfCoordinates

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {A : Type w} [CommRing A] [HopfAlgebra R A]

/-- Scalar extension carries a group-like element to a group-like element. -/
theorem isGroupLikeElem_one_tmul {a : A} (ha : IsGroupLikeElem R a) :
    IsGroupLikeElem S ((1 : S) ⊗ₜ[R] a) := by
  constructor
  · simp [TensorProduct.counit_tmul, ha.counit_eq_one]
  · simp [TensorProduct.comul_tmul, ha.comul_eq_tmul_self]

/-- The canonical character homomorphism under extension of scalars. -/
def groupLikeBaseChange : GroupLike R A →* GroupLike S (S ⊗[R] A) where
  toFun a := ⟨(1 : S) ⊗ₜ[R] a.val, isGroupLikeElem_one_tmul a.isGroupLikeElem_val⟩
  map_one' := by
    apply GroupLike.val_injective
    simp [Algebra.TensorProduct.one_def]
  map_mul' a b := by
    apply GroupLike.val_injective
    simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- Group-like spanning is preserved by arbitrary extension of scalars. -/
theorem span_groupLike_baseChange
    (hspan : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤) :
    Submodule.span S {x : S ⊗[R] A | IsGroupLikeElem S x} = ⊤ := by
  apply top_unique
  suffices ∀ x : S ⊗[R] A, x ∈ Submodule.span S {x | IsGroupLikeElem S x} by
    intro x _
    exact this x
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul s a =>
    have ha : a ∈ Submodule.span R {a : A | IsGroupLikeElem R a} := by rw [hspan]; trivial
    induction ha using Submodule.span_induction with
    | mem a ha =>
      have hmem : (1 : S) ⊗ₜ[R] a ∈
          Submodule.span S {x : S ⊗[R] A | IsGroupLikeElem S x} :=
        Submodule.subset_span (isGroupLikeElem_one_tmul (S := S) ha)
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
        (Submodule.span S {x : S ⊗[R] A | IsGroupLikeElem S x}).smul_mem s hmem
    | zero => simp
    | add a b ha hb hia hib =>
      simpa only [TensorProduct.tmul_add] using (Submodule.add_mem _ hia hib)
    | smul r a ha hia =>
      rw [TensorProduct.tmul_smul]
      exact Submodule.smul_of_tower_mem _ r hia

end HopfCoordinates

namespace Diagonalizable

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [AddGroup.FG M]

/-- The group algebra of any finitely generated abelian group is finitely
presented over every commutative ring, including when the group has torsion. -/
theorem finitePresentation_addGroupAlgebra : Algebra.FinitePresentation R (AddMonoidAlgebra R M) := by
  let : Algebra.FiniteType ℤ (AddMonoidAlgebra ℤ M) := inferInstance
  let : Algebra.FinitePresentation ℤ (AddMonoidAlgebra ℤ M) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.FinitePresentation.equiv (AddMonoidAlgebra.scalarTensorEquiv ℤ R)

end Diagonalizable

end Langlands.GroupScheme
