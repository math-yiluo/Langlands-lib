/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles

/-!
# Exactness of everywhere-defined left derived functors

Source: Stacks Project, Derived Categories, Definition 05S9 and Proposition 05SE
(blueprint: lem-pur-left-derived-exact-when-defined).
-/

@[expose] public section

universe u v u' v' u'' v''

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- In Situation 05S8, when the left derived values exist at every object, the
universal left derived functor is exact (Stacks Project, Tags 05S9 and 05SE)
(blueprint: lem-pur-left-derived-exact-when-defined).

The hypothesis `hLF` records that `LF` is characterized by the universal
(right Kan extension) property along the localization functor `Q`; the
conclusion supplies a compatible shift structure and exactness. The triangulation
on the localization is the induced one, expressed by exactness of `Q`.
The localization hypothesis uses Mathlib's universe-polymorphic localization interface.

Proof:
1. The right Kan universal property transports along shift equivalences, giving coherent
integer shifts on LF and making alpha commute with shifts.
2. Everywhere-defined denominator values give pointwise Kan limits. Lemma 05SC
(`lem-pur-derived-functor-triangles-05sc`) supplies a distinguished triangle of values
for every distinguished source triangle. Canonical limit comparisons, fraction squares,
and split-mono cancellation identify it with the image under Q followed by LF.
3. Proposition 05R6 (`lem-pur-localization-triangles-05r6`) represents every localized
distinguished triangle by a source triangle. Map the representing isomorphism by LF,
compose with the triangle-composition comparison, and use closure under isomorphisms
in D' to obtain exactness. -/
theorem leftDerived_exact_when_defined
    (D : Type u) [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (D' : Type u') [Category.{v'} D'] [HasZeroObject D'] [HasShift D' ℤ]
    [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (L : Type u'') [Category.{v''} L] [HasZeroObject L] [HasShift L ℤ]
    [Preadditive L] [∀ n : ℤ, (shiftFunctor L n).Additive]
    [Pretriangulated L] [CategoryTheory.IsTriangulated L]
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty D)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    (Q : D ⥤ L) [Q.CommShift ℤ] [Q.IsTriangulated]
    [Q.IsLocalization S]
    (_hQ : Q.IsStrictLocalizationAt S)
    (LF : L ⥤ D')
    (α : Q ⋙ LF ⟶ F)
    (hLF : LF.IsRightKanExtension α)
    (hdefined : ∀ X : D, F.IsTriangulatedLeftDerivedDefinedAt S hS X) :
    ∃ (_ : LF.CommShift ℤ), LF.IsTriangulated := by
  classical
  let : S.HasLeftCalculusOfFractions := hS.1.1.1
  obtain ⟨hshift, hα⟩ := rightKanExtension_coherentShift F Q LF α hLF
  let : LF.CommShift ℤ := hshift
  let : NatTrans.CommShift α ℤ := hα
  have hsource : (Q ⋙ LF).IsTriangulated := by
    constructor
    intro T hT
    exact leftDerived_kan_map_source_distinguished D D' L F S hS Q LF α hLF
      hdefined hα T hT
  let : (Q ⋙ LF).IsTriangulated := hsource
  have := Localization.essSurj_mapArrow Q S
  refine ⟨hshift, ⟨fun T hT ↦ ?_⟩⟩
  obtain ⟨T₀, e, hT₀⟩ := (Q.distTriang_iff T).1 hT
  exact Pretriangulated.isomorphic_distinguished _
    ((Q ⋙ LF).map_distinguished T₀ hT₀) _
    (LF.mapTriangle.mapIso e ≪≫ (mapTriangleCompIso Q LF).symm.app T₀)

end CategoryTheory.Functor
