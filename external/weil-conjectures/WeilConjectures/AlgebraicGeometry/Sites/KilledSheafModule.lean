/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.CategoryTheory.Sites.ZModSheaf

/-!
# Abelian sheaves killed by `n` as sheaves of `ULift (ℤ/n)`-modules

An abelian sheaf `G` on a site with `n • 𝟙 G = 0` is the underlying abelian sheaf of a sheaf of
`ℤ/n`-modules (`CategoryTheory.Sheaf.mem_essImage_sheafCompose_forget₂_zmod_iff`). Restricting
scalars along `ULift (ℤ/n) ≃+* ℤ/n`, which does not change the underlying abelian groups,
it is also the underlying abelian sheaf of a sheaf of `ULift (ℤ/n)`-modules, the coefficient ring
living in the universe of the values.

## Main results

- `CategoryTheory.Sheaf.exists_ulift_zmod_module_sheaf_of_nsmul_id_eq_zero`
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w})]
  [J.HasSheafCompose (ModuleCat.restrictScalars.{w}
    (ULift.ringEquiv : ULift.{w} (ZMod n) ≃+* ZMod n).toRingHom)]

/-- An abelian sheaf `G` with `n • 𝟙 G = 0` is the underlying abelian sheaf of a sheaf of
`ULift (ℤ/n)`-modules. -/
lemma exists_ulift_zmod_module_sheaf_of_nsmul_id_eq_zero (G : Sheaf J AddCommGrpCat.{w})
    (h : n • 𝟙 G = 0) :
    ∃ M : Sheaf J (ModuleCat.{w} (ULift.{w} (ZMod n))),
      Nonempty ((sheafCompose J
        (forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w})).obj M ≅ G) := by
  obtain ⟨M, ⟨e⟩⟩ := (mem_essImage_sheafCompose_forget₂_zmod_iff J n G).2 h
  let φ := (ULift.ringEquiv : ULift.{w} (ZMod n) ≃+* ZMod n).toRingHom
  let i : ModuleCat.restrictScalars.{w} φ ⋙
      forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w} ≅
        forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  refine ⟨(sheafCompose J (ModuleCat.restrictScalars.{w} φ)).obj M,
    ⟨(fullyFaithfulSheafToPresheaf J _).preimageIso ?_ ≪≫ e⟩⟩
  exact Functor.isoWhiskerLeft M.obj i

end CategoryTheory.Sheaf
