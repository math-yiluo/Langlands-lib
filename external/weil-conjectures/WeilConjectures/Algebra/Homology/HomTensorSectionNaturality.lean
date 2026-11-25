/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorComparisonNaturality
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Naturality of the canonical map to the sheaf tensor product

Source: Stacks Project, Modules on Sites, Section 03EK.
(blueprint: lem-sc-hom-tensor-section-natural)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from the presheaf tensor to the sheaf tensor is natural.
Source: Stacks Project, Modules on Sites, Section 03EK (tensor product of sheaves),
and the sheafification universal property of Lemma 03CY.
(blueprint: lem-sc-hom-tensor-section-natural)

Proof: Write S for module sheafification, eta for its unit and epsilon for its
counit. The tensor comparison c(A,B) is the tensor of the inverses of the
counit components followed by the tensorator of S. Naturality of epsilon
and of the tensorator gives
(f tensor g);c(A,B) = c(A',B');S(f.val tensor g.val).
Multiply this equality by the inverses of both comparison isomorphisms to
obtain c(A',B') inverse;(f tensor g) =
S(f.val tensor g.val);c(A,B) inverse. Apply the forgetful functor to this
identity. Precompose with eta at A'.val tensor B'.val, and use naturality
of eta to move the presheaf tensor map to the left. Reassociating gives
the displayed identity, since homTensorSectionMap is eta followed by the
underlying inverse comparison. This argument applies to arbitrary morphisms,
including zero morphisms and zero tensor factors; it uses no sectionwise
surjectivity of sheafification or tensor decomposition of sheaf sections. -/
theorem homTensorSectionMap_natural {A A' B B' : Mod}
    (f : A' ⟶ A) (g : B' ⟶ B) :
    letI := SheafOfModules.monoidalCategory R
    homTensorSectionMap R A' B' ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ homTensorSectionMap R A B := by
  let := SheafOfModules.monoidalCategory R
  let S := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have hc := homTensorComparison_natural R f g
  have hi : (SheafOfModules.tensorObjIsoSheafification A' B').inv ≫ (f ⊗ₘ g) =
      S.map (f.val ⊗ₘ g.val) ≫
        (SheafOfModules.tensorObjIsoSheafification A B).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hv := congrArg SheafOfModules.Hom.val hi
  change (SheafOfModules.tensorObjIsoSheafification A' B').inv.val ≫ (f ⊗ₘ g).val =
    (S.map (f.val ⊗ₘ g.val)).val ≫
      (SheafOfModules.tensorObjIsoSheafification A B).inv.val at hv
  have hn := adj.unit.naturality (f.val ⊗ₘ g.val)
  change (f.val ⊗ₘ g.val) ≫ adj.unit.app (A.val ⊗ B.val) =
    adj.unit.app (A'.val ⊗ B'.val) ≫ (S.map (f.val ⊗ₘ g.val)).val at hn
  unfold homTensorSectionMap
  erw [Category.assoc, hv, ← Category.assoc, ← hn]
  rfl

end CategoryTheory
