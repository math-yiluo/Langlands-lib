/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorPairingIsIso

/-! # Tensor comparison for the algebraic inverse image

Source: Stacks Project, Modules on Sites, Tag 03EL.
(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.RingedTensor
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
  (uInv : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (I : AlgebraicInverseImage uInv R RI)

/-- The specified algebraic inverse image preserves tensor products with their pairings.
Source: Stacks Project, Modules on Sites, Tag 03EL, third equality of the proof.
(auxiliary; not a blueprint node).

Proof: The right adjoint preserves products. Transport its additive operations and the
RI-action along the adjunction to give its module direct image, with action of R through
the adjoint of I.ringUnderlying. The graph equations I.moduleAdd and I.moduleSMul,
tested on universal pairs and triples, identify the mates of the linearity equations.
Thus adjunction restricts to a natural bijection between bilinear maps on I(M), I(N)
and bilinear maps on M, N with values in that direct image. Apply the sheaf tensor
universal property before and after this bijection. The resulting natural Hom bijection
is represented by an isomorphism. Evaluating the bijection on identities gives the
isomorphism and its inverse; naturality gives their inverse equations and simultaneous
naturality. Evaluating on any pair of generalized sections gives the displayed pure
formula. This uses the given algebraic lift, including its underlying natural iso;
no arbitrary identification with a different inverse-image lift is used. -/
theorem exists_inverseImageTensorComparison
    (uPush : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv] :
    ∃ e : ∀ M N : SheafOfModules.{u} (ringSheaf R),
        I.modules.obj ((monoidalCategory R).tensorObj M N) ≅
          (monoidalCategory RI).tensorObj (I.modules.obj M) (I.modules.obj N),
      (∀ {M M' N N' : SheafOfModules.{u} (ringSheaf R)} (f : M ⟶ M') (g : N ⟶ N'),
        I.modules.map ((monoidalCategory R).tensorHom f g) ≫ (e M' N').hom =
          (e M N).hom ≫ (monoidalCategory RI).tensorHom (I.modules.map f) (I.modules.map g)) ∧
      ∀ (M N : SheafOfModules.{u} (ringSheaf R)) (Z : Sheaf J (Type u))
        (x : Z ⟶ (underlying R).obj M) (y : Z ⟶ (underlying R).obj N)
        (z : Z ⟶ (underlying R).obj ((monoidalCategory R).tensorObj M N)),
        (∀ W t, z.hom.app W t = pure R M N W (x.hom.app W t) (y.hom.app W t)) →
        ∀ W t, (e M N).hom.val.app W
          ((uInv.map z ≫ I.moduleUnderlying.inv.app
            ((monoidalCategory R).tensorObj M N)).hom.app W t) =
          pure RI _ _ W ((uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t)
            ((uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)  := by
  classical
  let := monoidalCategory R
  let := monoidalCategory RI
  choose b hb hp using exists_inverseImageTensorPairing R RI uInv I
  have hi (M N : SheafOfModules.{u} (ringSheaf R)) : IsIso (b M N) :=
    inverseImageTensorPairing_isIso R RI uInv uPush adj I M N (b M N) (hb M N)
  have hn {M M' N N' : SheafOfModules.{u} (ringSheaf R)} (f : M ⟶ M') (g : N ⟶ N') :
      (I.modules.map f ⊗ₘ I.modules.map g) ≫ b M' N' =
        b M N ≫ I.modules.map (f ⊗ₘ g) := by
    apply pure_hom_ext RI
    intro W m n
    change (b M' N').val.app W
      ((I.modules.map f ⊗ₘ I.modules.map g).val.app W (pure RI _ _ W m n)) =
      (I.modules.map (f ⊗ₘ g)).val.app W ((b M N).val.app W (pure RI _ _ W m n))
    have h := congrArg (fun k ↦ k.hom.app W (m, n))
      (inverseImagePurePairing_natural R RI uInv I f g)
    exact (congrArg ((b M' N').val.app W) (pure_map RI (I.modules.map f)
      (I.modules.map g) W m n)).trans
        ((hb M' N' W _ _).trans
          (h.trans (congrArg ((I.modules.map (f ⊗ₘ g)).val.app W)
            (hb M N W m n).symm)))
  refine ⟨fun M N ↦ (asIso (b M N)).symm, ?_, ?_⟩
  · intro M M' N N' f g
    change I.modules.map (f ⊗ₘ g) ≫ inv (b M' N') =
      inv (b M N) ≫ (I.modules.map f ⊗ₘ I.modules.map g)
    apply (cancel_mono (b M' N')).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [hn]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  · intro M N Z x y z hz W t
    have h := hp M N Z x y z hz W t
    have h' := congrArg ((inv (b M N)).val.app W) h.symm
    exact h'.trans (congrArg (fun f : I.modules.obj M ⊗ I.modules.obj N ⟶
      I.modules.obj M ⊗ I.modules.obj N ↦ f.val.app W
        (pure RI _ _ W ((uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t)
          ((uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)))
            (IsIso.hom_inv_id (b M N)))

end SheafOfModules.RingedTensor
