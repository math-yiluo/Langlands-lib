import Langlands.GroupScheme.RelativeLevi.ParabolicCoproductChart

/-! # Injectivity for disjoint coproduct parabolic charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open Langlands.AlgebraicGeometry.AlgebraicSpace
open CoproductChart

variable {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G)
    {I : Type u} (V : I → Over S)
    (F : ∀ i, ParabolicSubgroup ((GroupScheme.baseChange (V i).hom).obj G))
    (hinj : ∀ (i : I) (T : Over S),
      Function.Injective (fun a : T ⟶ V i => restrict hG a (F i)))
    (htype : ∀ (i j : I) (T : Over S) (a : T ⟶ V i) (b : T ⟶ V j),
      restrict hG a (F i) = restrict hG b (F j) → i = j ∨ IsEmpty T.left)

include hinj htype in
/-- Equal component families determine the same morphism into the coproduct. -/
theorem eq_sigmaOverι_of_restrict_eq {T : Over S} (i j : I)
    (a : T ⟶ V i) (b : T ⟶ V j)
    (hab : restrict hG a (F i) = restrict hG b (F j)) :
    a ≫ sigmaOverι V i = b ≫ sigmaOverι V j := by
  rcases htype i j T a b hab with hij | hT
  · subst j
    exact congrArg (fun c => c ≫ sigmaOverι V i) (hinj i T hab)
  · let : IsEmpty T.left := hT
    apply Over.OverMorphism.ext
    exact isInitialOfIsEmpty.hom_ext _ _

include hinj htype in
/-- Componentwise injectivity and disjointness on nonempty tests imply
injectivity of the actual scheme coproduct chart on every test scheme. -/
theorem coproductParabolicChart_injective_of_disjoint (T : Over S) :
    Function.Injective ((coproductParabolicChart hG V F).app (op T)) := by
  rintro ⟨a⟩ ⟨b⟩ hab
  change restrict hG a (coproductParabolic hG V F) =
    restrict hG b (coproductParabolic hG V F) at hab
  apply ULift.ext
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (pullbackOpenCover V a) a.left b.left
  intro i
  change I at i
  let A := pullback a (sigmaOverι V i)
  let p : A ⟶ T := pullback.fst a (sigmaOverι V i)
  let x : A ⟶ V i := pullback.snd a (sigmaOverι V i)
  change p.left ≫ a.left = p.left ≫ b.left
  apply Scheme.Cover.hom_ext (pullbackOpenCover V (p ≫ b))
    (p.left ≫ a.left) (p.left ≫ b.left)
  intro j
  change I at j
  let B := pullback (p ≫ b) (sigmaOverι V j)
  let r : B ⟶ A := pullback.fst (p ≫ b) (sigmaOverι V j)
  let y : B ⟶ V j := pullback.snd (p ≫ b) (sigmaOverι V j)
  let c : B ⟶ T := r ≫ p
  change r.left ≫ (p.left ≫ a.left) = r.left ≫ (p.left ≫ b.left)
  have hca : c ≫ a = (r ≫ x) ≫ sigmaOverι V i := by
    dsimp [c, x, p]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  have hcb : c ≫ b = y ≫ sigmaOverι V j := by
    dsimp [c, r, y]
    rw [Category.assoc, pullback.condition]
  have hF : restrict hG (r ≫ x) (F i) = restrict hG y (F j) := by
    have h := congrArg (restrict hG c) hab
    rw [restrict_comp, restrict_comp, hca, hcb] at h
    rw [← restrict_comp hG (sigmaOverι V i) (r ≫ x),
      ← restrict_comp hG (sigmaOverι V j) y, restrict_coproductParabolic,
      restrict_coproductParabolic] at h
    exact h
  have heq : c ≫ a = c ≫ b :=
    hca.trans ((eq_sigmaOverι_of_restrict_eq hG V F hinj htype i j (r ≫ x) y hF).trans
      hcb.symm)
  simpa only [c, Over.comp_left, Category.assoc] using
    congrArg (fun f : B ⟶ sigmaOver V => f.left) heq

include hinj htype in
/-- The disjoint actual coproduct chart is a monomorphism of presheaves. -/
theorem coproductParabolicChart_mono_of_disjoint :
    Mono (coproductParabolicChart hG V F) := by
  have : ∀ T, Mono ((coproductParabolicChart hG V F).app T) := fun T =>
    ConcreteCategory.mono_of_injective _
      (coproductParabolicChart_injective_of_disjoint hG V F hinj htype T.unop)
  exact NatTrans.mono_of_mono_app _

end Langlands.GroupScheme.ParabolicSubgroupModuli
