/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.AlgebraDiagramPullback.AlgebraDiagramPullbackData
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Algebra.Homology.PullbackTensorCanonical.PullbackTensorCanonicalShiftUnit
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.Algebra.Homology.ExactPullbackSigned.ExactPullbackSignedComparison
/-! # Derived normalized comparison maps

Source: Stacks 03EL and 07A4.
(blueprint: lem-pur-algebra-diagram-derived-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [local irreducible] DerivedCategory.Q CategoryTheory.Functor.mapDerivedCategory
universe u w v v' v'' u' u''
open CategoryTheory CategoryTheory.Limits CategoryTheory.CochainPullback
open scoped ZeroObject
namespace CategoryTheory.AlgebraDiagramPullback
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {L : GrothendieckTopology D}
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf L CommRingCat.{u}}
section
variable (f : RingedPullback.{u, u, u, u, u} R S)
  (k : Comparison.{u, u, u, u, u} f) (d : CoefficientSquare.{u, u, u, u, u} f)
  [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} S)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} d.R')]
  [HasDerivedCategory.{w} (Modules.{u, u, u} d.S')]
  [ExactPullback f] [ExactPullback (changed f d)]
  [ExactRestriction d.sourceMap] [ExactRestriction d.targetMap]
end

private def fixedSecond {A : Type u} [Category.{v} A] (Y : A) : A ⥤ A × A where
  obj X := (X, Y)
  map f := (f, 𝟙 Y)

private theorem unary_descent
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    {E : Type u''} [Category.{v''} E] (q : A ⥤ B) (X₀ : A)
    (ff : ((Functor.whiskeringLeft (A × A) (B × B) E).obj (q.prod q)).FullyFaithful)
    {F G : B ⥤ E} (e : q ⋙ F ≅ q ⋙ G) :
    ∃ t : F ≅ G, ∀ X, t.app (q.obj X) = e.app X := by
  let fstA : A × A ⥤ A := Prod.fst _ _
  let fstB : B × B ⥤ B := Prod.fst _ _
  let ee : (q.prod q) ⋙ (fstB ⋙ F) ≅ (q.prod q) ⋙ (fstB ⋙ G) :=
    Functor.isoWhiskerLeft fstA e
  let tt : fstB ⋙ F ≅ fstB ⋙ G := ff.preimageIso ee
  let t : F ≅ G := Functor.isoWhiskerLeft (fixedSecond (q.obj X₀)) tt
  refine ⟨t, ?_⟩
  intro X
  apply Iso.ext
  exact NatTrans.congr_app (ff.map_preimage ee.hom) (X, X₀)

end CategoryTheory.AlgebraDiagramPullback
