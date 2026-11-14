import Langlands.GroupScheme.KernelPair
import Langlands.GroupScheme.Rational.LeviSubgroup
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Multiplication by a homomorphism kernel as a pullback -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.KernelSubgroupMultiplication

variable {S : Scheme.{u}} {A G Q : GroupScheme S} (a : A ⟶ G) (q : G ⟶ Q)

@[reassoc]
theorem multiplication_comp :
    subgroupMultiplication a (kernelι q) ≫ q.hom.hom =
      fst A.X (kernel q).X ≫ (a ≫ q).hom.hom := by
  rw [subgroupMultiplication, MonObj.mul_comp, Category.assoc, Category.assoc,
    (kernel_isPullback q).w]
  change _ * (snd _ _ ≫ toUnit (kernel q).X ≫ η[Q.X]) = _
  rw [← Category.assoc (snd _ _) (toUnit _) _, comp_toUnit]
  exact mul_one _

/-- The map into the pullback over the quotient. -/
def hom : A.X ⊗ (kernel q).X ⟶ pullback (a ≫ q).hom.hom q.hom.hom :=
  pullback.lift (fst _ _) (subgroupMultiplication a (kernelι q))
    (multiplication_comp a q).symm

@[reassoc (attr := simp)]
theorem hom_fst : hom a q ≫ pullback.fst _ _ = fst A.X (kernel q).X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem hom_snd : hom a q ≫ pullback.snd _ _ = subgroupMultiplication a (kernelι q) :=
  pullback.lift_snd _ _ _

/-- Subtracting the chosen subgroup component gives a kernel point. -/
def difference : pullback (a ≫ q).hom.hom q.hom.hom ⟶ (kernel q).X :=
  (kernel_isPullback q).lift
    ((pullback.fst _ _ ≫ a.hom.hom)⁻¹ * pullback.snd _ _) (toUnit _) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
      change (pullback.fst _ _ ≫ (a ≫ q).hom.hom)⁻¹ *
        (pullback.snd _ _ ≫ q.hom.hom) = _
      rw [pullback.condition, inv_mul_cancel]
      rfl)

@[reassoc (attr := simp)]
theorem difference_ι :
    difference a q ≫ (kernelι q).hom.hom =
      (pullback.fst (a ≫ q).hom.hom q.hom.hom ≫ a.hom.hom)⁻¹ *
        pullback.snd _ _ :=
  (kernel_isPullback q).lift_fst _ _ _

def inv : pullback (a ≫ q).hom.hom q.hom.hom ⟶ A.X ⊗ (kernel q).X :=
  lift (pullback.fst _ _) (difference a q)

@[reassoc (attr := simp)]
theorem inv_fst : inv a q ≫ fst _ _ =
    pullback.fst (a ≫ q).hom.hom q.hom.hom := lift_fst _ _

@[reassoc (attr := simp)]
theorem inv_snd : inv a q ≫ snd _ _ = difference a q := lift_snd _ _

theorem hom_inv_id : hom a q ≫ inv a q = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, inv_fst, hom_fst, Category.id_comp]
  · apply (cancel_mono (kernelι q).hom.hom).mp
    rw [Category.assoc, Category.assoc, inv_snd_assoc, difference_ι,
      MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hom_fst, hom_snd,
      subgroupMultiplication]
    simp only [Category.id_comp, inv_mul_cancel_left]

theorem inv_hom_id : inv a q ≫ hom a q = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, hom_fst, inv_fst, Category.id_comp]
  · rw [Category.assoc, hom_snd, subgroupMultiplication, MonObj.comp_mul,
      ← Category.assoc, inv_fst, ← Category.assoc, inv_snd, difference_ι]
    simp only [Category.id_comp, mul_inv_cancel_left]

/-- The subgroup times the kernel is the quotient pullback. -/
def iso : A.X ⊗ (kernel q).X ≅ pullback (a ≫ q).hom.hom q.hom.hom where
  hom := hom a q
  inv := inv a q
  hom_inv_id := hom_inv_id a q
  inv_hom_id := inv_hom_id a q

/-- Multiplication by the actual kernel is a base change of the composite. -/
theorem isPullback :
    IsPullback (fst A.X (kernel q).X) (subgroupMultiplication a (kernelι q))
      (a ≫ q).hom.hom q.hom.hom :=
  IsPullback.of_iso_pullback ⟨(multiplication_comp a q).symm⟩ (iso a q)
    (hom_fst a q) (hom_snd a q)

theorem isPullback_scheme :
    IsPullback (fst A.X (kernel q).X).left
      (subgroupMultiplication a (kernelι q)).left
      (a ≫ q).hom.hom.left q.hom.hom.left :=
  (isPullback a q).map (Over.forget S)

/-- Finiteness and surjectivity transfer to multiplication by the kernel. -/
theorem finite_surjective [IsFinite (a ≫ q).hom.hom.left]
    [Surjective (a ≫ q).hom.hom.left] :
    IsFinite (subgroupMultiplication a (kernelι q)).left ∧
      Surjective (subgroupMultiplication a (kernelι q)).left := by
  exact ⟨MorphismProperty.of_isPullback (isPullback_scheme a q) inferInstance,
    MorphismProperty.of_isPullback (isPullback_scheme a q) inferInstance⟩

end Langlands.GroupScheme.KernelSubgroupMultiplication
