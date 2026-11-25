/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
/-!
# Uniqueness of bilinear extensions through module sheafification

Source: Stacks Project, Modules on Sites, Tag 0GMW.
-/

@[expose] public section
universe u v w
open CategoryTheory
namespace PresheafOfModules
/-- Natural bilinear families agreeing on the two module units are equal.
Source: Stacks Project, Modules on Sites, Tag 0GMW, uniqueness in the
sheafification universal property.
(blueprint: lem-pc-sites-module-sheafification-bilinear-extension-uniqueness)

Proof: For sections `x,y`, intersect the covering image sieves of the two units.
Every arrow in this covering sieve gives lifts `a,b` of both restrictions.
Naturality of both families identifies their restricted values with their values
on these unit images. The assumed unit agreement makes these equal. Since `H`
is a sheaf, separatedness gives equality of the values on `x,y` themselves.
Function and linear-map extensionality give equality of the two families. -/
theorem unique_bilinear_sheafification_extension
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (O : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (R : Sheaf J CommRingCat.{max u v w})
    (α : (O ⋙ forget₂ CommRingCat.{max u v w} RingCat.{max u v w}) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R).obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (F G : PresheafOfModules.{max u v w} (O ⋙ forget₂ CommRingCat.{max u v w} RingCat.{max u v w}))
    (H : SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R))
    {γ δ : ∀ X : Cᵒᵖ,
      ((sheafification α).obj F).val.obj X →ₗ[R.obj.obj X]
        ((sheafification α).obj G).val.obj X →ₗ[R.obj.obj X] H.val.obj X}
    (hγmap : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y)
      (x : ((sheafification α).obj F).val.obj X)
      (y : ((sheafification α).obj G).val.obj X),
      γ Y (((sheafification α).obj F).val.map f x)
        (((sheafification α).obj G).val.map f y) = H.val.map f (γ X x y))
    (hδmap : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y)
      (x : ((sheafification α).obj F).val.obj X)
      (y : ((sheafification α).obj G).val.obj X),
      δ Y (((sheafification α).obj F).val.map f x)
        (((sheafification α).obj G).val.map f y) = H.val.map f (δ X x y))
    (hγ : ∀ (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X),
      γ X (((sheafificationAdjunction α).unit.app F).app X x)
        (((sheafificationAdjunction α).unit.app G).app X y) =
        δ X (((sheafificationAdjunction α).unit.app F).app X x)
          (((sheafificationAdjunction α).unit.app G).app X y)) : γ = δ := by
  funext X
  ext x y
  let ηF := CategoryTheory.toSheafify J F.presheaf
  let ηG := CategoryTheory.toSheafify J G.presheaf
  apply H.isSheaf.isSeparated _ (Presheaf.imageSieve ηF x ⊓ Presheaf.imageSieve ηG y)
    (J.intersection_covering (Presheaf.imageSieve_mem J ηF x)
      (Presheaf.imageSieve_mem J ηG y))
  rintro Y f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  change H.val.map f.op (γ X x y) = H.val.map f.op (δ X x y)
  rw [← hγmap f.op x y, ← hδmap f.op x y]
  change ηF.app (Opposite.op Y) a = ((sheafification α).obj F).val.map f.op x at ha
  change ηG.app (Opposite.op Y) b = ((sheafification α).obj G).val.map f.op y at hb
  rw [← ha, ← hb]
  exact hγ (Opposite.op Y) a b
end PresheafOfModules
