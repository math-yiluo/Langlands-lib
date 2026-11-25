/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares

/-! # Universal cochain counit transported from homotopy localization

Source: the agent-written homotopy-to-cochain refinement of Stacks Tag 099M,
`proetale-lemma-naive-completion`, in the constant-completion argument for the blueprint's
completed pullback, `def-weil-pbc-completed-pullback`.
(blueprint: lem-weil-pbc-cochain-universal-counit-transport)
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uB vB wA wB

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem counitTransport_precomp
    {C₀ C₁ D H : Type*} [Category* C₀] [Category* C₁] [Category* D] [Category* H]
    (P : C₀ ⥤ C₁) (Q : C₁ ⥤ D) (T : C₁ ⥤ H) (K : D ⥤ H)
    (ε : Q ⋙ K ⟶ T) [K.IsRightKanExtension ε]
    [((Functor.whiskeringLeft C₀ C₁ H).obj P).Full]
    [((Functor.whiskeringLeft C₀ C₁ H).obj P).Faithful] :
    K.IsRightKanExtension ((Functor.associator P Q K).hom ≫ Functor.whiskerLeft P ε) := by
  let G := Functor.RightExtension.precomp Q T P
  have : G.IsEquivalence := by
    dsimp only [G, Functor.RightExtension.precomp]
    apply CostructuredArrow.isEquivalenceMap₂
  let : Limits.PreservesLimit (Functor.empty.{0} _) G :=
    (Adjunction.isEquivalencePreservesLimits G).preservesLimitsOfShape.preservesLimit
  let : Limits.ReflectsLimit (Functor.empty.{0} _) G :=
    (Functor.reflectsLimits_of_isEquivalence G).reflectsLimitsOfShape.reflectsLimit
  have h := (Limits.IsTerminal.isTerminalIffObj G (Functor.RightExtension.mk K ε)).1
    (K.isUniversalOfIsRightKanExtension ε)
  refine ⟨⟨Limits.IsTerminal.ofIso h (CostructuredArrow.isoMk (Iso.refl _) ?_)⟩⟩
  ext X
  dsimp [G, Functor.RightExtension.precomp, Functor.RightExtension.mk,
    Functor.whiskeringLeft]
  simp only [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem counitTransport_iso
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    {Q Q' : C ⥤ D} (s : Q ≅ Q') (T : C ⥤ H) (K : D ⥤ H)
    (ε : Q ⋙ K ⟶ T) [K.IsRightKanExtension ε] :
    K.IsRightKanExtension ((Functor.isoWhiskerRight s K).inv ≫ ε) := by
  let G := (Functor.rightExtensionEquivalenceOfIso₁ s T).functor
  let : Limits.PreservesLimit (Functor.empty.{0} _) G :=
    (Adjunction.isEquivalencePreservesLimits G).preservesLimitsOfShape.preservesLimit
  let : Limits.ReflectsLimit (Functor.empty.{0} _) G :=
    (Functor.reflectsLimits_of_isEquivalence G).reflectsLimitsOfShape.reflectsLimit
  have h := (Limits.IsTerminal.isTerminalIffObj G (Functor.RightExtension.mk K ε)).1
    (K.isUniversalOfIsRightKanExtension ε)
  refine ⟨⟨Limits.IsTerminal.ofIso h (CostructuredArrow.isoMk (Iso.refl _) ?_)⟩⟩
  ext X
  change (𝟙 _ ≫ K.map (s.inv.app X) ≫ ε.app X) = K.map (s.inv.app X) ≫ ε.app X
  rw [Category.id_comp]

/-- The specified cochain counit retains homotopy-level universality and precisely the
same invertible components, for an additive functor with no exactness assumption.

Source: agent-written categorical refinement of Stacks Tag 099M
(`proetale-lemma-naive-completion`), the constant-completion argument for the blueprint's
`def-weil-pbc-completed-pullback`.
(blueprint: lem-weil-pbc-cochain-universal-counit-transport)

Proof:
1. Put `p = HomotopyCategory.quotient A (.up ℤ)`, `H = F^h ⋙ Qh`,
   `s = DerivedCategory.quotientCompQhIso A`, and
   `t = (derivedCochainComparisonFactors F).symm`. The definition
   `derivedCochainCounit` gives beta at P as `L(s.inv.app P) ≫ ε.app (p.obj P) ≫ t.hom.app P`.
   For any `a : Q ⋙ G ⟶ F^c ⋙ Q`, conjugate its components to
   `G(s.hom.app P) ≫ a.app P ≫ t.inv.app P`; naturality follows from that of s, a, and t.
2. The quotient p has the complexes as objects and is full on arrows. The same components
   therefore descend uniquely to a transformation `Qh ⋙ G ⟶ H`: naturality at a homotopy
   class follows by choosing a representing cochain map. Equality of transformations is
   detected after p. The assumed homotopy Kan property supplies a unique `b : G ⟶ L`.
3. Naturality of any `c : G ⟶ L` at `s.inv.app P` identifies the conjugate of
   `(Functor.whiskerLeft Q c ≫ beta).app P` with
   `(Functor.whiskerLeft Qh c ≫ ε).app (p.obj P)`. Thus the cochain factorization equation
   is equivalent to the homotopy factorization equation, and the unique b in step 2
   proves the Kan property for the prescribed beta.
4. The outside factors `L(s.inv.app P)` and `t.hom.app P` are isomorphisms. If ε at pP
   is invertible, the inverse of beta is `t.inv.app P ≫ inv (ε.app (p.obj P)) ≫ L(s.hom.app P)`.
   Conversely, the inverse of ε at pP is
   `t.hom.app P ≫ inv (beta.app P) ≫ L(s.inv.app P)`. The inverse equations follow by
   cancellation. This proves the componentwise equivalence on every resolving class. -/
theorem cochainUniversalCounitTransport
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsRightKanExtension ε] :
    L.IsRightKanExtension (derivedCochainCounit F L ε) ∧
      ∀ P : CochainComplex A ℤ,
        IsIso ((derivedCochainCounit F L ε).app P) ↔
          IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) := by
  constructor
  · have := counitTransport_precomp (HomotopyCategory.quotient A (.up ℤ))
      DerivedCategory.Qh _ L ε
    have h := counitTransport_iso (DerivedCategory.quotientCompQhIso A) _ L
      ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) ε)
    exact (Functor.isRightKanExtension_iff_of_iso₂ _
      (derivedCochainCounit F L ε) (derivedCochainComparisonFactors F).symm (Iso.refl _)
      (by
        simp only [derivedCochainCounit, Iso.symm_hom, Iso.refl_hom,
          Functor.whiskerLeft_id', Category.id_comp, Category.assoc])).mp h
  · intro P
    dsimp only [derivedCochainCounit, derivedCochainComparisonFactors, NatTrans.comp_app,
      Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [isIso_comp_left_iff, isIso_comp_right_iff]

end CategoryTheory
