/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import WeilConjectures.CategoryTheory.LeftDerivedExactWhenDefined

/-! # Exactness on a chosen derived category

Source: Stacks Project, Tag 05SE and the localization universal property.
(blueprint: lem-pur-left-derived-exact-chosen-localization).
-/

@[expose] public section

universe w v u v' u'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Exactness of an everywhere-defined left derived functor on the chosen derived category.
Source: Stacks Project, Tag 05SE, left derived part.
(blueprint: lem-pur-left-derived-exact-chosen-localization).

Proof: Let E be the equivalence from the strict constructed localization of the homotopy
category at quasi-isomorphisms to the chosen derived category. Descend the shift structure
of Qh along the constructed localization to E. The shift-compatible factorization and
representation of distinguished triangles make E exact. Precompose the supplied right Kan
extension LF with E: invariance of right Kan extensions under this equivalence makes E⋙LF
universal along the strict constructed localization. Apply `leftDerived_exact_when_defined`
there, using the supplied essential constancy at every object. Finally, E is itself a
localization at all isomorphisms. Descend the shift structure of E⋙LF along E to LF; the
comparison is shift-compatible. Representation of distinguished triangles along the exact
equivalence E then descends preservation of distinguished triangles from E⋙LF to LF.
Strict factorization is needed only for the constructed localization, not for Qh. -/
theorem leftDerived_exact_of_localization
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (D' : Type u') [Category.{v'} D'] [Preadditive D'] [HasZeroObject D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D')
    [F.CommShift ℤ] [F.IsTriangulated]
    (hS : MorphismProperty.IsSaturatedTriangulatedMultiplicativeSystem
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (LF : DerivedCategory A ⥤ D') (ε : DerivedCategory.Qh ⋙ LF ⟶ F)
    (hLF : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hdefined : ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
      F.IsTriangulatedLeftDerivedDefinedAt
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) hS X) :
    ∃ (_ : LF.CommShift ℤ), LF.IsTriangulated := by
  classical
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := A)
  let : W.HasLeftCalculusOfFractions := hS.1.1.1
  let : W.HasRightCalculusOfFractions := hS.1.1.2
  let : W.IsCompatibleWithTriangulation := hS.2
  let E := (Localization.equivalenceFromModel Q W).functor
  let e := Localization.qCompEquivalenceFromModelFunctorIso Q W
  let : Localization.Lifting W.Q W Q E := ⟨e⟩
  let : E.CommShift ℤ := commShiftOfLocalization W.Q W ℤ Q E
  have : NatTrans.CommShift e.hom ℤ := by
    exact NatTrans.commShift_iso_hom_of_localization W.Q W ℤ Q E
  have := Localization.essSurj_mapArrow W.Q W
  have : E.IsTriangulated := isTriangulated_of_precomp_iso e
  have hstrict : IsStrictLocalizationAt.{max u v, v, max u v, max u v, u', v'}
      W.Q W := by
    refine ⟨Localization.inverts W.Q W, ?_⟩
    intro H hH
    refine ⟨⟨Localization.strictUniversalPropertyFixedTargetQ W H⟩, ?_⟩
    intro G G'
    exact (Localization.fullyFaithfulWhiskeringLeft W.Q W H).map_bijective G G'
  let β := (associator W.Q E LF).inv ≫ whiskerRight e.hom LF ≫ ε
  have : LF.IsRightKanExtension ε := hLF.isRightKanExtension
  have hG : (E ⋙ LF).IsRightKanExtension β :=
    (isRightKanExtension_iff_postcomp₁ E e ε).1 inferInstance
  obtain ⟨hshift, hexact⟩ := leftDerived_exact_when_defined
    (HomotopyCategory A (ComplexShape.up ℤ)) D' W.Localization F W hS W.Q hstrict
      (E ⋙ LF) β hG hdefined
  let : (E ⋙ LF).CommShift ℤ := hshift
  have : (E ⋙ LF).IsTriangulated := hexact
  let V := MorphismProperty.isomorphisms W.Localization
  let : E.IsLocalization V := IsLocalization.of_isEquivalence E V (by
    intro X Y f hf
    exact hf)
  let : Localization.Lifting E V (E ⋙ LF) LF := ⟨Iso.refl _⟩
  let : LF.CommShift ℤ := commShiftOfLocalization E V ℤ (E ⋙ LF) LF
  have hcompat : @NatTrans.CommShift _ _ _ _ _ _
      (Localization.Lifting.iso E V (E ⋙ LF) LF).hom ℤ _ _ _
      (CommShift.comp E LF) hshift :=
    NatTrans.commShift_iso_hom_of_localization E V ℤ (E ⋙ LF) LF
  refine ⟨inferInstance, ?_⟩
  exact isTriangulated_of_precomp_iso
    (Localization.Lifting.iso E V (E ⋙ LF) LF)

end CategoryTheory.Functor
