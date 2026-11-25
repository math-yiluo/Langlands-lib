/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantProCriterion
import WeilConjectures.CategoryTheory.ThirdValueConstruction

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- The third vertex has a left-derived value when the first two do.
Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause
(blueprint: lem-pur-derived-functor-triangles-05sc-third-value).

Proof (dual of the source's construction): choose values A and B with their
essential-constancy cones, and form LF(f) by 05SA. Choose retraction stages for
the two cones. MS2 lifts f to a denominator square; the common-stage factorization
and cofiltered equalization refine the first stage until the retractions alpha
and beta satisfy alpha followed by LF(f) = F(f') followed by beta. Complete f'
to a distinguished triangle and use MS6 to supply its third denominator. Complete
LF(f) to a distinguished triangle (A,B,C). Exactness of F and TR3 extend alpha and
beta to gamma : F(Z') -> C. Use the cofiltered category of denominator triangles
of 05R9; its initial vertex projections transport the A and B cones by 0A1S.
For each W, apply Hom(-,W) to these F-image triangles and take the filtered
colimit over the opposite indexing category. Exactness of filtered colimits
and the five lemma make Hom(C,W) -> colim Hom(F(Z''),W), induced at the chosen
stage by gamma, bijective. The four outer comparisons are inverse to the cone
Hom-colimit bijections; for the shifted terms use W[-1]. The pro criterion 05PY
at gamma supplies an essentially constant cone with value C. Initiality of the
third projection transports it to S/Z. Thus C is a left-derived value at Z.
This construction does not use the parent theorem or any rotation case. -/
theorem leftDerived_definedAt_third_of_first_two
    {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty C)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    (T : Triangle C) (hT : T ∈ distTriang C)
    (hX : F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₁)
    (hY : F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₂) :
    F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₃ := by
  let : S.HasRightCalculusOfFractions := hS.1.1.2
  let : IsCofiltered (S.Over ⊤ T.obj₃) := by
    refine {
      nonempty := ⟨MorphismProperty.Over.mk (P := S) ⊤ (𝟙 T.obj₃) (S.id_mem _)⟩
      cone_objs := ?_
      cone_maps := ?_ }
    · intro a b
      obtain ⟨ψ, hψ⟩ :=
        (MorphismProperty.LeftFraction.mk a.hom b.hom b.prop).exists_rightFraction
      let q := MorphismProperty.Over.mk (P := S) ⊤ (ψ.s ≫ a.hom)
        (S.comp_mem _ _ ψ.hs a.prop)
      exact ⟨q, MorphismProperty.Over.homMk ψ.s,
        MorphismProperty.Over.homMk ψ.f hψ.symm, trivial⟩
    · intro a b f g
      obtain ⟨Z, t, ht, heq⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
        f.left g.left b.hom b.prop (f.w.trans g.w.symm)
      let q := MorphismProperty.Over.mk (P := S) ⊤ (t ≫ a.hom)
        (S.comp_mem _ _ ht a.prop)
      exact ⟨q, MorphismProperty.Over.homMk t, MorphismProperty.Over.Hom.ext heq⟩
  obtain ⟨A, hA⟩ := hX
  obtain ⟨B, hB⟩ := hY
  obtain ⟨Y, s, r, hbij⟩ := thirdValue_core F S hS T hT A B hA hB
  exact ⟨Y, (homColimit_essentiallyConstantProDiagram
    (MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F)
    Y s r hbij).1⟩

end CategoryTheory.Functor
