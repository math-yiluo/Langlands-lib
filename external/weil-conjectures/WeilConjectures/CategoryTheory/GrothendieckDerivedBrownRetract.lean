/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetractData

/-! # The localization step in Grothendieck Brown representability

Source: Stacks Project, Tag 0F5X, `injectives-lemma-brown`, before the final
Karoubianity argument.
-/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

private theorem localization_retract
    {B : Type*} [Category.{max w vH} B] {C : Type*} [Category.{w} C]
    (F : Cᵒᵖ ⥤ Type (max w vH)) (L : B ⥤ C) (R : C ⥤ B)
    (adj : L ⊣ R) [IsIso adj.counit] (E : B)
    (e : uliftYoneda.{vH}.obj E ≅ L.op ⋙ F) :
    Nonempty (Retract F (uliftYoneda.{vH}.obj (L.obj E))) := by
  let t := adj.unit.app E
  have ht : L.map t = inv (adj.counit.app (L.obj E)) := by
    apply (cancel_mono (adj.counit.app (L.obj E))).mp
    simp [t]
  have : IsIso (L.map t) := by rw [ht]; infer_instance
  have : IsIso ((L.op ⋙ F).map t.op) := by
    change IsIso (F.map (L.map t).op)
    infer_instance
  have : IsIso ((uliftYoneda.{vH}.obj E).map t.op) :=
    (NatIso.isIso_map_iff e t.op).mpr inferInstance
  let s : R.obj (L.obj E) ⟶ E :=
    (inv ((uliftYoneda.{vH}.obj E).map t.op) (ULift.up (𝟙 E))).down
  have hts : t ≫ s = 𝟙 E := by
    have h := types_congr_hom
      (IsIso.inv_hom_id ((uliftYoneda.{vH}.obj E).map t.op)) (ULift.up (𝟙 E))
    exact congrArg ULift.down h
  let rB : Retract E (R.obj (L.obj E)) := ⟨t, s, hts⟩
  let gamma : F ≅ R.op ⋙ (L.op ⋙ F) :=
    (Functor.leftUnitor F).symm ≪≫
      Functor.isoWhiskerRight (NatIso.op (asIso adj.counit)) F
  let alpha : F ≅ R.op ⋙ uliftYoneda.{vH}.obj E :=
    gamma ≪≫ Functor.isoWhiskerLeft R.op e.symm
  let ff := adj.fullyFaithfulROfIsIsoCounit
  let beta : R.op ⋙ uliftYoneda.{vH}.obj (R.obj (L.obj E)) ≅
      uliftYoneda.{vH}.obj (L.obj E) :=
    NatIso.ofComponents (fun X ↦ Equiv.toIso
      { toFun := fun x ↦ ULift.up (ff.preimage x.down)
        invFun := fun x ↦ ULift.up (R.map x.down)
        left_inv := by intro x; apply ULift.ext; simp
        right_inv := by intro x; apply ULift.ext; simp }) (by
      intro X Y f
      ext x
      apply ULift.ext
      change ff.preimage (R.map f.unop ≫ x.down) = f.unop ≫ ff.preimage x.down
      rw [ff.preimage_comp, ff.preimage_map])
  exact ⟨(Retract.ofIso alpha).trans
    (((rB.map uliftYoneda.{vH}).map ((Functor.whiskeringLeft _ _ _).obj R.op)).trans
      (Retract.ofIso beta))⟩

/-- The localization construction makes a cohomological functor a natural retract
of a representable functor, before splitting any idempotent in the derived category.
Source: Stacks Project, Tag 0F5X, `injectives-lemma-brown`, first two paragraphs.
(auxiliary; not a blueprint node)

Proof in words: obtain the localization adjunction L left adjoint to R, its invertible
counit, and the representation of the pulled-back lifted underlying functor F from
`grothendieckDerived_localization_brown_data`. Write t for the unit at its representing
object E. The left triangle identity says L(t) is the inverse counit, so F(L(t)) is
invertible. The representing isomorphism therefore makes precomposition by t an
invertible map Hom(R(L(E)),E) -> Hom(E,E). Apply its inverse to the identity to obtain
s with t followed by s equal to the identity. Apply lifted Yoneda to this retract and
precompose with R.op. The opposite counit and the representing isomorphism identify
the first endpoint with F; full faithfulness of R identifies the second endpoint with
lifted Yoneda of L(E). Compose these natural retracts. Unlike the source's triangle
argument, this splitting uses only the adjunction and representation. This step does
not split an idempotent or assert that the retract itself is representable. -/
theorem grothendieckDerived_brown_retract
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)]
    (H : (DerivedCategory A)ᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w vA vH), PreservesLimitsOfShape (Discrete I) H) :
    ∃ E : DerivedCategory A,
      Nonempty (Retract (H ⋙ forget AddCommGrpCat ⋙ uliftFunctor.{w})
        (uliftYoneda.{vH}.obj E)) := by
  obtain ⟨B, cB, L, R, adj, hc, E, ⟨e⟩⟩ :=
    grothendieckDerived_localization_brown_data H hH
  let := cB
  have := hc
  exact ⟨L.obj E, localization_retract
    (H ⋙ forget AddCommGrpCat ⋙ uliftFunctor.{w}) L R adj E e⟩

end CategoryTheory
