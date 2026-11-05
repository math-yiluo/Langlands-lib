import Langlands.AlgebraicGeometry.FiniteEtale.Pullback

/-! # The image of a cover fundamental group fixes its selected lift -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))

/-- The map from a cover's fundamental group at a selected lift lands in the
stabilizer of that very lift. No connectedness or surjectivity is needed. -/
theorem fundamentalGroupMap_fixes_lift
    (Y : Cover S) (x : Fiber s Y)
    (ht : ∀ Z : Cover Y.obj.left, Finite (Fiber x.left Z))
    (g : FundamentalGroup x.left ht) :
    fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs g • x = x := by
  let I : Cover Y.obj.left := cover (𝟙 _)
  let e : Fiber x.left I := Over.homMk x.left (by simp [I, cover])
  have he : (g • e).left = x.left := by
    simpa [I, cover] using Over.w (g • e)
  apply Over.OverMorphism.ext
  rw [fundamentalGroupMap_smul_left_of_comp Y.obj.hom x.left s (Over.w x) ht hs
    g x e (𝟙 Y.obj.left) (by simp [I, cover])
      (by change x.left ≫ 𝟙 Y.obj.left = x.left; exact Category.comp_id _)]
  exact (Category.comp_id _).trans he

end Langlands.AlgebraicGeometry.FiniteEtale
