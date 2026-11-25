/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import WeilConjectures.CategoryTheory.DerivedFunctorValueTriangleCompatibility

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- Supplied value cones and the first two induced maps extend to a distinguished triangle.
Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause
(blueprint: lem-pur-derived-functor-triangles-05sc-value-triangle).

Proof: complete the supplied lf to a distinguished triangle (LX,LY,C,lf,b,c).
Use MS2 and the common-stage clauses of huX and huY to choose a denominator
square for mor₁ with compatible retractions alpha and beta. TR1 and MS6 complete
this square to a denominator triangle, and TR3 extends alpha,beta to gamma into
(LX,LY,C). Over the cofiltered triangle-morphism category of 05R9, apply Hom(-,W)
and exact filtered colimits. The cone Hom-colimit comparisons at LX and LY and
the five lemma give Hom(C,W) -> colim Hom(F(Z'),W) bijective for every W; the
shifted terms use W[-1]. The pro criterion 05PY constructs a value cone at C,
and initiality (0A1S) transports it to S/T.obj₃. Its Hom-colimit bijections and
those of the supplied cone uZ yield the unique isomorphism C -> LZ matching
all cone legs. The triangle square for b and uniqueness of the induced map in
05SA identify b followed by this isomorphism with the supplied lg, since hg
is exactly its defining denominator-square equation. Define lh by the inverse
isomorphism followed by c. The same cone comparison on the third square,
with the shift comparison 05SU, gives the displayed equation for every h'.
Explicitly its target leg is shift.map(uX.app s') followed by commShiftIso.inv;
MS5 makes the shifted denominator admissible. Transport the distinguished
triangle along identities at LX,LY and the isomorphism C -> LZ. This proves
both the universal shifted equation and distinguishedness for the supplied
objects and maps, without assuming either conclusion. -/
theorem leftDerived_value_triangle_extension
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
    (LX LY LZ : D)
    (hX : F.IsTriangulatedLeftDerivedValue S hS T.obj₁ LX)
    (hY : F.IsTriangulatedLeftDerivedValue S hS T.obj₂ LY)
    (hZ : F.IsTriangulatedLeftDerivedValue S hS T.obj₃ LZ)
    (uX : (Functor.const (S.Over ⊤ T.obj₁)).obj LX ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F)
    (uY : (Functor.const (S.Over ⊤ T.obj₂)).obj LY ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F)
    (uZ : (Functor.const (S.Over ⊤ T.obj₃)).obj LZ ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F)
    (huX : ∃ s₀ : S.Over ⊤ T.obj₁, ∃ r : F.obj s₀.left ⟶ LX,
      uX.app s₀ ≫ r = 𝟙 LX ∧
        ∀ s : S.Over ⊤ T.obj₁, ∃ t : S.Over ⊤ T.obj₁,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uX.app s)
    (huY : ∃ s₀ : S.Over ⊤ T.obj₂, ∃ r : F.obj s₀.left ⟶ LY,
      uY.app s₀ ≫ r = 𝟙 LY ∧
        ∀ s : S.Over ⊤ T.obj₂, ∃ t : S.Over ⊤ T.obj₂,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uY.app s)
    (huZ : ∃ s₀ : S.Over ⊤ T.obj₃, ∃ r : F.obj s₀.left ⟶ LZ,
      uZ.app s₀ ≫ r = 𝟙 LZ ∧
        ∀ s : S.Over ⊤ T.obj₃, ∃ t : S.Over ⊤ T.obj₃,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uZ.app s)
    (lf : LX ⟶ LY) (lg : LY ⟶ LZ)
    (hf : ∀ (s : S.Over ⊤ T.obj₁) (s' : S.Over ⊤ T.obj₂)
        (f' : s.left ⟶ s'.left),
        s.hom ≫ T.mor₁ = f' ≫ s'.hom →
          uX.app s ≫ F.map f' = lf ≫ uY.app s')
    (hg : ∀ (s : S.Over ⊤ T.obj₂) (s' : S.Over ⊤ T.obj₃)
        (g' : s.left ⟶ s'.left),
        s.hom ≫ T.mor₂ = g' ≫ s'.hom →
          uY.app s ≫ F.map g' = lg ≫ uZ.app s')
    : ∃ lh : LZ ⟶ (shiftFunctor D (1 : ℤ)).obj LX,
      (∀ (s : S.Over ⊤ T.obj₃) (s' : S.Over ⊤ T.obj₁)
        (h' : s.left ⟶ (shiftFunctor C (1 : ℤ)).obj s'.left),
        s.hom ≫ T.mor₃ = h' ≫ (shiftFunctor C (1 : ℤ)).map s'.hom →
          uZ.app s ≫ F.map h' =
            lh ≫ (shiftFunctor D (1 : ℤ)).map (uX.app s') ≫
              (F.commShiftIso (1 : ℤ)).inv.app s'.left) ∧
      Triangle.mk lf lg lh ∈ distTriang D  := by
  obtain ⟨lh, hdist, hcompat⟩ :=
    leftDerived_value_triangle_extension_compat F S hS T hT LX LY LZ hX hY hZ
      uX uY uZ huX huY huZ lf lg hf hg
  exact ⟨lh, hcompat, hdist⟩

end CategoryTheory.Functor
