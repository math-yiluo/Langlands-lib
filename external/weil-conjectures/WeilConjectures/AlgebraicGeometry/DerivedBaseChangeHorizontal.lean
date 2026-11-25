/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeHorizontalMate

/-! # Horizontal composition of derived base-change squares

Source: Stacks Project, Cohomology, Tags 08HY and 0D5S.
(blueprint: lem-pc-derived-base-change-horizontal).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Horizontal pasting for arbitrary commutative squares, before any open
restriction or coefficient comparison is inserted.
Source: Stacks Project, Cohomology, Remark 08HY and Lemma 0D5S.
(blueprint: lem-pc-derived-base-change-horizontal).

Proof: Transpose under the composite adjunction for j' followed by f'.
The right-adjoint uniqueness comparison changes transposition for j' followed
by f' into transposition for j'≫f', with the pinned pullback composition
comparison. Expand the two inner base-change maps as transposes of pulled-back
counits. Naturality moves the inner transpose through the f' counit and the
triangle identity cancels its unit. The remaining counits are the composite
counit for j followed by f, transported along the source composition
comparison. Associativity of the pinned pullback comparisons identifies the
pasted square comparison with the outer square comparison. The equations h
and hj identify the equality transports; proof irrelevance identifies their
proofs. Injectivity of the composite Hom equivalence proves the identity.
No square has to be cartesian, and no morphism has to be an open immersion.
Identity morphisms, empty schemes and zero objects satisfy the same identities. -/
theorem schemeDerivedBaseChange_horizontal
    {A X S A' X' S' : Scheme.{u}}
    (j : A ⟶ X) (f : X ⟶ S) (j' : A' ⟶ X') (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (v : A' ⟶ A)
    (h : g' ≫ f = f' ≫ g) (hj : v ≫ j = j' ≫ g')
    (E : schemeDerivedCategory A) :
    schemeDerivedBaseChangeMap f f' g g' h ((schemeDerivedDirectImage j).obj E) ≫
        (schemeDerivedDirectImage f').map
          (schemeDerivedBaseChangeMap j j' g' v hj E) ≫
        (relativeMVImageComp j' f').hom.app ((derivedPullback v).obj E) =
      (derivedPullback g).map ((relativeMVImageComp j f).hom.app E) ≫
        schemeDerivedBaseChangeMap (j ≫ f) (j' ≫ f') g v
          (by rw [← Category.assoc, hj, Category.assoc, h, ← Category.assoc]) E  := by
  rw [← Category.assoc, schemeDerivedBaseChange_horizontal_mate j f j' f' g g' v h hj E]
  simp

end AlgebraicGeometry
