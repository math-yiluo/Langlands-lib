/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat

/-!
# Naturality of the sheaf tensor comparison

Source: Stacks Project, Modules on Sites, Section 03EK.
(blueprint: lem-sc-hom-tensor-comparison-natural)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

private lemma homTensorComparison_naturality_of_unit
    {D E : Type*} [Category D] [Category E] [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) [F.LaxMonoidal] (G : E ⥤ D) (η : 𝟭 E ⟶ G ⋙ F)
    {A A' B B' : E} (f : A' ⟶ A) (g : B' ⟶ B) :
    (f ⊗ₘ g) ≫ (η.app A ⊗ₘ η.app B) ≫ Functor.LaxMonoidal.μ F (G.obj A) (G.obj B) =
      ((η.app A' ⊗ₘ η.app B') ≫ Functor.LaxMonoidal.μ F (G.obj A') (G.obj B')) ≫
        F.map (G.map f ⊗ₘ G.map g) := by
  have hf := η.naturality f
  have hg := η.naturality g
  change f ≫ η.app A = η.app A' ≫ F.map (G.map f) at hf
  change g ≫ η.app B = η.app B' ≫ F.map (G.map g) at hg
  rw [← Category.assoc, tensorHom_comp_tensorHom, hf, hg,
    ← tensorHom_comp_tensorHom, Category.assoc, Functor.LaxMonoidal.μ_natural,
    Category.assoc]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the tensor comparison isomorphism.
Source: Stacks Project, Section 03EK and Lemma 03CY.
(blueprint: lem-sc-hom-tensor-comparison-natural)

Proof: Let S be module sheafification and epsilon its invertible counit.
The comparison is the tensor of the inverse counit components followed by
S's tensorator. Naturality of the inverse counit gives
f;epsilon(A) inverse = epsilon(A') inverse;S(f.val), and likewise for g.
The tensor interchange law combines these two identities. Tensorator
naturality then identifies the resulting composite with the comparison
at A',B' followed by S(f.val tensor g.val). Associativity gives the result.
No invertibility of f or g is used; identity and zero maps and zero objects
are included. This is the first step of the section-map naturality proof,
before forgetting and composing with the sheafification unit. -/
theorem homTensorComparison_natural {A A' B B' : Mod}
    (f : A' ⟶ A) (g : B' ⟶ B) :
    letI := SheafOfModules.monoidalCategory R
    (f ⊗ₘ g) ≫ (SheafOfModules.tensorObjIsoSheafification A B).hom =
      (SheafOfModules.tensorObjIsoSheafification A' B').hom ≫
        (PresheafOfModules.sheafification
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
          (f.val ⊗ₘ g.val) := by
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let S := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let G := SheafOfModules.forget
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let η : 𝟭 Mod ⟶ G ⋙ S := (asIso adj.counit).inv
  exact homTensorComparison_naturality_of_unit S G η f g

end CategoryTheory
