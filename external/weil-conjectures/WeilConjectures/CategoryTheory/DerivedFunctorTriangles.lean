/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import WeilConjectures.CategoryTheory.DerivedFunctorShift
import WeilConjectures.CategoryTheory.LeftDerivedValueMorphism
import WeilConjectures.CategoryTheory.DerivedFunctorThirdValue
import WeilConjectures.CategoryTheory.DerivedFunctorValueTriangle

/-!
# Left derived functors preserve distinguished triangles

Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause
(blueprint: lem-pur-derived-functor-triangles-05sc).
-/

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- In Situation 05S8, if a distinguished triangle has left-derived values at two
vertices, then the value at the third exists and the three values form a
distinguished triangle, with the third map viewed through the canonical shift
isomorphism.
Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause
(blueprint: lem-pur-derived-functor-triangles-05sc).

Proof (the LF dual of the source proof):
1. For values A at X and B at Y, use `lem-pur-derived-functor-morphisms-05sa`
   to obtain LF(f). Choose denominator stages with retractions alpha and beta
   using `def-pc-essentially-constant-pro-diagram`. MS2 and a common-stage
   refinement make beta composed with F(f') equal to LF(f) composed with alpha.
   Complete f' to a distinguished triangle; MS6 supplies its third denominator.
   Complete LF(f) to a distinguished triangle (A,B,C); exactness of F and TR3
   extend (alpha,beta) to a triangle morphism (alpha,beta,gamma).
2. Use `lem-pur-triangle-morphism-category-05r9`: the category of denominator
   triangle morphisms into T is cofiltered and its three projections are initial.
   By `lem-pur-essential-constant-cofinal-0a1s`, the first two diagrams have
   values A,B, and essential constancy of the third with value C suffices.
3. Apply Hom(-,W) to the F-image triangles. The colimit over the opposite
   indexing category is exact by `lem-weil-pbc-filtered-colimit-abelian-groups-exact`.
   Compare with the five-term exact Hom sequence of (A,B,C) using the retractions.
   The outer four maps are bijective by `lem-pc-essentially-constant-pro-hom-colimit`
   (use W[-1] for the shifted terms). `lem-weil-pbc-five-lemma` makes the middle
   comparison Hom(C,W) to the Hom colimit bijective.
4. `lem-pur-essential-constant-pro-criterion-05py`, with gamma at the chosen
   denominator triangle, supplies the cone with value C. Transport it along
   `lem-pur-essential-constant-cofinal-0a1s`. The cone equations and uniqueness
   in `lem-pur-derived-functor-morphisms-05sa` identify b with LF(g), and c with
   LF(h) followed by the inverse shift comparison of
   `lem-pur-derived-functor-shift-05su`. The shifted cone equation below expresses
   this identification directly. For the other pairs of defined vertices, rotate
   T once or twice, apply the first case, and rotate back, transporting values
   and definedness using `lem-pur-derived-functor-shift-05su`.
-/
theorem leftDerived_map_distinguished_of_two_defined
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
    (hdefined :
      (F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₁ ∧
          F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₂) ∨
      (F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₂ ∧
          F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₃) ∨
      (F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₃ ∧
          F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₁)) :
    ∃ (LX LY LZ : D),
      F.IsTriangulatedLeftDerivedValue S hS T.obj₁ LX ∧
        F.IsTriangulatedLeftDerivedValue S hS T.obj₂ LY ∧
          F.IsTriangulatedLeftDerivedValue S hS T.obj₃ LZ ∧
            ∃ (uX : (Functor.const (S.Over ⊤ T.obj₁)).obj LX ⟶
                MorphismProperty.Over.forget S ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F)
              (uY : (Functor.const (S.Over ⊤ T.obj₂)).obj LY ⟶
                MorphismProperty.Over.forget S ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F)
              (uZ : (Functor.const (S.Over ⊤ T.obj₃)).obj LZ ⟶
                MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F),
              (∃ s₀ : S.Over ⊤ T.obj₁, ∃ r : F.obj s₀.left ⟶ LX,
                uX.app s₀ ≫ r = 𝟙 LX ∧
                  ∀ s : S.Over ⊤ T.obj₁, ∃ t : S.Over ⊤ T.obj₁,
                    ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
                      F.map b.left = F.map a.left ≫ r ≫ uX.app s) ∧
              (∃ s₀ : S.Over ⊤ T.obj₂, ∃ r : F.obj s₀.left ⟶ LY,
                uY.app s₀ ≫ r = 𝟙 LY ∧
                  ∀ s : S.Over ⊤ T.obj₂, ∃ t : S.Over ⊤ T.obj₂,
                    ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
                      F.map b.left = F.map a.left ≫ r ≫ uY.app s) ∧
              (∃ s₀ : S.Over ⊤ T.obj₃, ∃ r : F.obj s₀.left ⟶ LZ,
                uZ.app s₀ ≫ r = 𝟙 LZ ∧
                  ∀ s : S.Over ⊤ T.obj₃, ∃ t : S.Over ⊤ T.obj₃,
                    ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
                      F.map b.left = F.map a.left ≫ r ≫ uZ.app s) ∧
              ∃ (lf : LX ⟶ LY) (lg : LY ⟶ LZ)
                (lh : LZ ⟶ (shiftFunctor D (1 : ℤ)).obj LX),
                (∀ (s : S.Over ⊤ T.obj₁) (s' : S.Over ⊤ T.obj₂)
                  (f' : s.left ⟶ s'.left),
                  s.hom ≫ T.mor₁ = f' ≫ s'.hom →
                    uX.app s ≫ F.map f' = lf ≫ uY.app s') ∧
                (∀ (s : S.Over ⊤ T.obj₂) (s' : S.Over ⊤ T.obj₃)
                  (g' : s.left ⟶ s'.left),
                  s.hom ≫ T.mor₂ = g' ≫ s'.hom →
                    uY.app s ≫ F.map g' = lg ≫ uZ.app s') ∧
                (∀ (s : S.Over ⊤ T.obj₃) (s' : S.Over ⊤ T.obj₁)
                  (h' : s.left ⟶ (shiftFunctor C (1 : ℤ)).obj s'.left),
                  s.hom ≫ T.mor₃ = h' ≫ (shiftFunctor C (1 : ℤ)).map s'.hom →
                    uZ.app s ≫ F.map h' =
                      lh ≫ (shiftFunctor D (1 : ℤ)).map (uX.app s') ≫
                        (F.commShiftIso (1 : ℤ)).inv.app s'.left) ∧
                Triangle.mk lf lg lh ∈ distTriang D := by
  have hshift (X : C) := (isTriangulatedLeftDerivedDefinedAt_shift_iff F S hS X 1).1
  have hall : F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₁ ∧
      F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₂ ∧
      F.IsTriangulatedLeftDerivedDefinedAt S hS T.obj₃ := by
    rcases hdefined with ⟨hX, hY⟩ | ⟨hY, hZ⟩ | ⟨hZ, hX⟩
    · exact ⟨hX, hY, leftDerived_definedAt_third_of_first_two F S hS T hT hX hY⟩
    · have hX := (hshift T.obj₁).mpr
        (leftDerived_definedAt_third_of_first_two F S hS T.rotate
          (rot_of_distTriang T hT) hY hZ)
      exact ⟨hX, hY, hZ⟩
    · have hY := (hshift T.obj₂).mpr
        (leftDerived_definedAt_third_of_first_two F S hS T.rotate.rotate
          (rot_of_distTriang T.rotate (rot_of_distTriang T hT)) hZ
          ((hshift T.obj₁).mp hX))
      exact ⟨hX, hY, hZ⟩
  obtain ⟨LX, hX⟩ := hall.1
  obtain ⟨LY, hY⟩ := hall.2.1
  obtain ⟨LZ, hZ⟩ := hall.2.2
  obtain ⟨uX, huX⟩ := hX.2
  obtain ⟨uY, huY⟩ := hY.2
  obtain ⟨uZ, huZ⟩ := hZ.2
  obtain ⟨lf, hf, _⟩ := leftDerived_value_morphism F S hS T.mor₁ LX LY hX hY uX uY huX huY
  obtain ⟨lg, hg, _⟩ := leftDerived_value_morphism F S hS T.mor₂ LY LZ hY hZ uY uZ huY huZ
  have hf' := fun s s' f' hf' ↦ (hf s s' f' hf').1
  have hg' := fun s s' g' hg' ↦ (hg s s' g' hg').1
  obtain ⟨lh, hh, hdist⟩ := leftDerived_value_triangle_extension F S hS T hT
    LX LY LZ hX hY hZ uX uY uZ huX huY huZ lf lg hf' hg'
  exact ⟨LX, LY, LZ, hX, hY, hZ, uX, uY, uZ, huX, huY, huZ, lf, lg, lh, hf', hg', hh,
    hdist⟩

end CategoryTheory.Functor
