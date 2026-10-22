import Langlands.Cohomology.Tate.ZeroDefinitions
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.TensorProduct.Associator

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Mathlib's actual Tate-to-homology comparison followed by its proved first-homology theorem. -/
def minusTwoTensorEquiv (A : Rep.{u} R G) [A.IsTrivial] :
    tateCohomology A (-2) ≃+ (Additive (Abelianization G)) ⊗[ℤ] A :=
  ((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A).toLinearEquiv.toAddEquiv.trans
    (groupHomology.H1AddEquivOfIsTrivial A)

/-- The actual first-homology single-chain class, transported into degree minus two. -/
def minusTwoClass (A : Rep.{u} R G) [A.IsTrivial] (g : G) (a : A) :
    tateCohomology A (-2) :=
  ((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A).inv
    (groupHomology.H1π A
      ((groupHomology.cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a)))

lemma minusTwoTensorEquiv_class (A : Rep.{u} R G) [A.IsTrivial] (g : G) (a : A) :
    minusTwoTensorEquiv A (minusTwoClass A g a) =
      Additive.ofMul (Abelianization.of g) ⊗ₜ[ℤ] a := by
  change groupHomology.H1AddEquivOfIsTrivial A
    (((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A).hom
      (((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A).inv
        (groupHomology.H1π A
          ((groupHomology.cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a))))) = _
  exact (congrArg (groupHomology.H1AddEquivOfIsTrivial A)
    (((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A).toLinearEquiv.apply_symm_apply
      (groupHomology.H1π A
        ((groupHomology.cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a))))).trans
    (groupHomology.H1AddEquivOfIsTrivial_single A g a)

/-- Remove the actual lifted integral tensor factor using its explicit equivalence with integers. -/
def integralTensorEquiv (G : Type u) [Group G] :
    (Additive (Abelianization G)) ⊗[ℤ] IntegralScalar.{u} ≃+ Additive (Abelianization G) :=
  (TensorProduct.congr (LinearEquiv.refl ℤ (Additive (Abelianization G)))
    integralScalarEquiv.toAddEquiv.toIntLinearEquiv).toAddEquiv.trans
    (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv

/-- The degree-minus-two group for the actual trivial lifted integral module is the abelianization. -/
def integralMinusTwoEquiv (G : Type u) [Group G] [Fintype G] :
    tateCohomology (integralTrivial G) (-2) ≃+ Additive (Abelianization G) :=
  (minusTwoTensorEquiv (integralTrivial G)).trans (integralTensorEquiv G)

lemma integralMinusTwoEquiv_class (g : G) :
    integralMinusTwoEquiv G (minusTwoClass (integralTrivial G) g (1 : IntegralScalar.{u})) =
      Additive.ofMul (Abelianization.of g) := by
  change integralTensorEquiv G
    (minusTwoTensorEquiv (integralTrivial G) (minusTwoClass (integralTrivial G) g 1)) = _
  rw [minusTwoTensorEquiv_class]
  simp [integralTensorEquiv, integralScalarEquiv]

/-- The actual map on abelianizations induced by subgroup inclusion. -/
def abelianizationInclusion (H : Subgroup G) :
    Additive (Abelianization H) →+ Additive (Abelianization G) :=
  (Abelianization.map H.subtype).toAdditive

/-- The actual group-theoretic transfer to the subgroup abelianization, descended from `G`. -/
def abelianizationTransfer (H : Subgroup G) :
    Additive (Abelianization G) →+ Additive (Abelianization H) :=
  (Abelianization.lift (MonoidHom.transfer (Abelianization.of : H →* Abelianization H))).toAdditive

end Langlands.Tate
