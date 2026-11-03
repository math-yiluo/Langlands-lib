import Langlands.AbelianScheme.GroupScheme
import Langlands.AbelianScheme.Kernel

/-! # The kernel trivializes a group homomorphism's kernel pair -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.KernelPair

variable {S : Scheme.{u}} {G Q : GroupScheme S} (q : G ⟶ Q)

/-- The second component of the kernel action on the source. -/
def action : G.X ⊗ (kernel q).X ⟶ G.X :=
  fst _ _ * (snd _ _ ≫ (kernelι q).hom.hom)

@[reassoc]
theorem action_comp :
    action q ≫ q.hom.hom = fst G.X (kernel q).X ≫ q.hom.hom := by
  rw [action, MonObj.mul_comp, Category.assoc, (kernel_isPullback q).w]
  change _ * (snd _ _ ≫ toUnit (kernel q).X ≫ η[Q.X]) = _
  rw [← Category.assoc, comp_toUnit]
  exact mul_one _

/-- A source point and a kernel point give two points with the same image. -/
def hom : G.X ⊗ (kernel q).X ⟶ pullback q.hom.hom q.hom.hom :=
  pullback.lift (fst _ _) (action q) (action_comp q).symm

@[reassoc (attr := simp)]
theorem hom_fst : hom q ≫ pullback.fst _ _ = fst G.X (kernel q).X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem hom_snd : hom q ≫ pullback.snd _ _ = action q :=
  pullback.lift_snd _ _ _

/-- The difference of the two points of a kernel pair lies in the actual kernel. -/
def difference : pullback q.hom.hom q.hom.hom ⟶ (kernel q).X :=
  (kernel_isPullback q).lift
    ((pullback.fst _ _)⁻¹ * pullback.snd _ _) (toUnit _) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, pullback.condition, inv_mul_cancel]
      rfl)

@[reassoc (attr := simp)]
theorem difference_ι :
    difference q ≫ (kernelι q).hom.hom =
      (pullback.fst q.hom.hom q.hom.hom)⁻¹ * pullback.snd _ _ :=
  (kernel_isPullback q).lift_fst _ _ _

/-- Recover the source point and its kernel-valued difference. -/
def inv : pullback q.hom.hom q.hom.hom ⟶ G.X ⊗ (kernel q).X :=
  lift (pullback.fst _ _) (difference q)

@[reassoc (attr := simp)]
theorem inv_fst : inv q ≫ fst _ _ = pullback.fst q.hom.hom q.hom.hom :=
  lift_fst _ _

@[reassoc (attr := simp)]
theorem inv_snd : inv q ≫ snd _ _ = difference q :=
  lift_snd _ _

theorem hom_inv_id : hom q ≫ inv q = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, inv_fst, hom_fst, Category.id_comp]
  · apply (cancel_mono (kernelι q).hom.hom).mp
    rw [Category.assoc, Category.assoc, inv_snd_assoc, difference_ι,
      MonObj.comp_mul, GrpObj.comp_inv, hom_fst, hom_snd, action]
    simp only [Category.id_comp, inv_mul_cancel_left]

theorem inv_hom_id : inv q ≫ hom q = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, hom_fst, inv_fst, Category.id_comp]
  · rw [Category.assoc, hom_snd, action, MonObj.comp_mul,
      inv_fst, ← Category.assoc, inv_snd, difference_ι]
    simp only [Category.id_comp, mul_inv_cancel_left]

/-- The canonical isomorphism `(g,k) ↦ (g,gk)` over the original scheme base.
It is an isomorphism of schemes over the base, without a commutativity premise. -/
def iso : G.X ⊗ (kernel q).X ≅ pullback q.hom.hom q.hom.hom where
  hom := hom q
  inv := inv q
  hom_inv_id := hom_inv_id q
  inv_hom_id := inv_hom_id q

/-- The kernel action square is a pullback in schemes over the base. -/
theorem isPullback :
    IsPullback (fst G.X (kernel q).X) (action q) q.hom.hom q.hom.hom :=
  IsPullback.of_iso_pullback ⟨(action_comp q).symm⟩ (iso q)
    (hom_fst q) (hom_snd q)

/-- Forgetting the base retains the kernel action pullback square. -/
theorem isPullback_scheme :
    IsPullback (fst G.X (kernel q).X).left (action q).left
      q.hom.hom.left q.hom.hom.left :=
  (isPullback q).map (Over.forget S)

/-- The same comparison as an isomorphism of actual schemes. -/
def schemeIso :
    (G.X ⊗ (kernel q).X).left ≅ pullback q.hom.hom.left q.hom.hom.left :=
  (isPullback_scheme q).isoPullback

@[reassoc (attr := simp)]
theorem schemeIso_hom_fst :
    (schemeIso q).hom ≫ pullback.fst _ _ = (fst G.X (kernel q).X).left :=
  (isPullback_scheme q).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem schemeIso_hom_snd :
    (schemeIso q).hom ≫ pullback.snd _ _ = (action q).left :=
  (isPullback_scheme q).isoPullback_hom_snd

end Langlands.GroupScheme.KernelPair
