import Langlands.GroupScheme.Reductive.AffinePinnedModel
import Langlands.GroupScheme.Lie.FieldExtension
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Actual pinning points over arbitrary test schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffinePinnedModel

variable (M : AffinePinnedModel.{u}) {T : Scheme.{u}}
  (f : T ⟶ M.base) (A : Type u) [CommRing A] [Algebra M.ring A]
  (a : Spec (CommRingCat.of A) ⟶ T)
  (ha : algebraBaseMap M.ring A = a ≫ f)

/-- The original pinning vector with coefficients extended to the test ring. -/
def rootVectorAt (s : M.basis.support) : lieKernel M.group A :=
  lieKernelMap M.group (Algebra.ofId M.ring A) (M.pinning s 1).val.toMul

include ha in
private theorem rootVectorAt_base (s : M.basis.support) :
    (M.rootVectorAt A s).val.left ≫ M.group.X.hom =
      algebraBaseMap A (DualNumber A) ≫ a ≫ f := by
  rw [← ha]
  exact (Over.w (M.rootVectorAt A s).val).trans (by
    change algebraBaseMap M.ring (DualNumber A) =
      algebraBaseMap A (DualNumber A) ≫ algebraBaseMap M.ring A
    simp only [algebraBaseMap, ← Spec.map_comp]
    congr 1)

/-- An actual dual-number point of the pulled-back model, attached to one
original pinning vector and an affine test over its arbitrary common scheme. -/
def rootVectorPoint (s : M.basis.support) :
    Spec (CommRingCat.of (DualNumber A)) ⟶ (M.groupOver f).X.left :=
  pullback.lift (M.rootVectorAt A s).val.left
    (algebraBaseMap A (DualNumber A) ≫ a) (by
      simpa only [Category.assoc] using M.rootVectorAt_base f A a ha s)

@[reassoc (attr := simp)]
theorem rootVectorPoint_fst (s : M.basis.support) :
    M.rootVectorPoint f A a ha s ≫ pullback.fst M.group.X.hom f =
      (M.rootVectorAt A s).val.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem rootVectorPoint_snd (s : M.basis.support) :
    M.rootVectorPoint f A a ha s ≫ (M.groupOver f).X.hom =
      algebraBaseMap A (DualNumber A) ≫ a :=
  pullback.lift_snd _ _ _

variable {W : Scheme.{u}} (q : W ⟶ T)
  (b : Spec (CommRingCat.of A) ⟶ W)
  (hb : algebraBaseMap M.ring A = b ≫ (q ≫ f))

/-- Direct and iterated pullback give the same pinning point after projection
to the model over the intermediate common scheme. -/
theorem rootVectorPoint_pull (s : M.basis.support) :
    M.rootVectorPoint (q ≫ f) A b hb s ≫
        (baseChangeCompIso f q M.group).hom.hom.hom.left ≫
        pullback.fst (M.groupOver f).X.hom q =
      M.rootVectorPoint f A (b ≫ q) (by simpa only [Category.assoc] using hb) s := by
  change M.rootVectorPoint (q ≫ f) A b hb s ≫
    (baseChangeCompIso f q M.group).hom.hom.hom.left ≫
    pullback.fst (pullback.snd M.group.X.hom f) q = _
  apply pullback.hom_ext
  · have hcomp :
        (baseChangeCompIso f q M.group).hom.hom.hom.left ≫
            (baseChangeCompIso f q M.group).inv.hom.hom.left = 𝟙 _ :=
      congrArg (fun k => k.hom.hom.left) (baseChangeCompIso f q M.group).hom_inv_id
    simp only [Category.assoc]
    rw [← baseChangeCompIso_inv_fst,
      ← Category.assoc (baseChangeCompIso f q M.group).hom.hom.hom.left,
      hcomp, Category.id_comp, rootVectorPoint_fst, rootVectorPoint_fst]
  · have hi := Over.w (baseChangeCompIso f q M.group).hom.hom.hom
    change (baseChangeCompIso f q M.group).hom.hom.hom.left ≫
      pullback.snd (pullback.snd M.group.X.hom f) q =
        pullback.snd M.group.X.hom (q ≫ f) at hi
    change M.rootVectorPoint (q ≫ f) A b hb s ≫
      (baseChangeCompIso f q M.group).hom.hom.hom.left ≫
      pullback.fst (pullback.snd M.group.X.hom f) q ≫
      pullback.snd M.group.X.hom f = _
    rw [pullback.condition, ← Category.assoc _ _ q, hi]
    simp only [rootVectorPoint, pullback.lift_snd, pullback.lift_snd_assoc,
      Category.assoc]

end Langlands.GroupScheme.AffinePinnedModel
