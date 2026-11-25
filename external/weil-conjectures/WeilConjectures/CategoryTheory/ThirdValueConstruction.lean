/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit
import WeilConjectures.CategoryTheory.LeftDerivedValueMorphism
import WeilConjectures.CategoryTheory.TriangleMorphismCategory
import WeilConjectures.CategoryTheory.TriangulatedHomColimitComparison
import Mathlib.CategoryTheory.Limits.Final.Type

/-! # Construction of the third denominator Hom comparison

Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause, dualized.
(blueprint: lem-pur-derived-functor-triangles-05sc-third-value-core).
-/

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

private theorem bijective_retraction_hom_colimit
    {J : Type u} {D : Type uD} [Category.{v} J] [Category.{vD} D]
    (G : J ⥤ D) (A : D) (h : IsEssentiallyConstantProDiagram G A)
    (u : (Functor.const J).obj A ⟶ G)
    (hu : ∃ j₀ : J, ∃ r : G.obj j₀ ⟶ A, u.app j₀ ≫ r = 𝟙 A ∧
      ∀ j : J, ∃ k : J, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j,
        G.map b = G.map a ≫ r ≫ u.app j)
    (j : J) (r : G.obj j ⟶ A) (hr : u.app j ≫ r = 𝟙 A) (W : D) :
    Function.Bijective (fun φ : A ⟶ W ↦
      (G.op ⋙ yoneda.obj W).ιColimitType (Opposite.op j) (r ≫ φ)) := by
  obtain ⟨q, hq, hqrep⟩ := essentiallyConstantPro_hom_colimit G A h u hu W
  have hcomp (φ : A ⟶ W) :
      q ((G.op ⋙ yoneda.obj W).ιColimitType (Opposite.op j) (r ≫ φ)) = φ := by
    rw [hqrep, ← Category.assoc, hr]
    exact Category.id_comp φ
  constructor
  · intro φ ψ he
    exact (hcomp φ).symm.trans ((congrArg q he).trans (hcomp ψ))
  · intro x
    refine ⟨q x, hq.1 ?_⟩
    exact hcomp (q x)

/-- The third denominator diagram has a stage whose map to a candidate value induces
Hom-colimit bijections.

Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause, dualized;
Categories, initial-functor colimit comparison in Tag 0A1T.
(blueprint: lem-pur-derived-functor-triangles-05sc-third-value-core).

Proof: Extract the cones for the supplied values A and B and use 05SA to obtain
lf : A -> B. Choose a retraction rY at sY. MS2 completes the first triangle arrow
against sY to a denominator square at s₁. Apply the common-stage clause of the A
cone to s₁, obtaining p : s -> sX and q : s -> s₁ with
F(q) = F(p) followed by rX followed by uX(s₁). Set alpha = F(p) followed by rX
and f = q followed by the square's first arrow. Naturality makes alpha a retraction
of uX(s). The factorization equation, the defining equation for lf, and the
retraction identity at sY give F(f) followed by rY = alpha followed by lf.
No extra equalization or denominator condition on p or q is needed.

Complete f and lf to distinguished triangles T' and U. MS6 completes the denominator
square to d : T' -> T with all three components in S. Exactness of F and TR3 extend
alpha and rY to m : F(T') -> U. These are actual triangle constructions.

The incoming denominator-triangle category of 05R9 is cofiltered and its vertex
projections p₁, p₂, p₃ are initial. At the chosen stage j₀ corresponding to d, the
first two Hom comparisons are bijective: their composites with the canonical final
colimit comparisons are the inverses of the cone Hom-colimit bijections of 05PZ.
The proved private helper checks these inverses using the retraction identities.
Apply triangulated_hom_colimit_comparison to H, the diagram of F-image triangles,
and m. This is the remaining general five-term Hom comparison step, stated in a
separate module. Finally compose its third comparison with the bijective colimit
map induced by p₃ opposite. The representative is exactly gamma at p₃(j₀).
Return U.obj₃, this denominator, and gamma. -/
theorem thirdValue_core
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
    (A B : D)
    (hX : F.IsTriangulatedLeftDerivedValue S hS T.obj₁ A)
    (hY : F.IsTriangulatedLeftDerivedValue S hS T.obj₂ B) :
    ∃ (Y : D) (s : S.Over ⊤ T.obj₃) (r : F.obj s.left ⟶ Y),
      ∀ W : D, Function.Bijective (fun φ : Y ⟶ W ↦
        (((MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F).op ⋙
          yoneda.obj W).ιColimitType (Opposite.op s) (r ≫ φ))) := by
  classical
  let : S.HasLeftCalculusOfFractions := hS.1.1.1
  let : S.HasRightCalculusOfFractions := hS.1.1.2
  let : S.IsCompatibleWithTriangulation := hS.2
  obtain ⟨uX, huX⟩ := hX.2
  obtain ⟨uY, huY⟩ := hY.2
  obtain ⟨lf, hlf, _⟩ :=
    leftDerived_value_morphism F S hS T.mor₁ A B hX hY uX uY huX huY
  obtain ⟨sX, rX, hrX, hfacX⟩ := huX
  obtain ⟨sY, rY, hrY, hfacY⟩ := huY
  obtain ⟨a, ha⟩ :=
    (MorphismProperty.LeftFraction.mk T.mor₁ sY.hom sY.prop).exists_rightFraction
  let s₁ : S.Over ⊤ T.obj₁ := ⟨Over.mk a.s, a.hs⟩
  obtain ⟨s, p, q, hpq⟩ := hfacX s₁
  change F.map q.left = F.map p.left ≫ rX ≫ uX.app s₁ at hpq
  change F.obj sX.left ⟶ A at rX
  change F.obj sY.left ⟶ B at rY
  let α : F.obj s.left ⟶ A := F.map p.left ≫ rX
  let f : s.left ⟶ sY.left := q.left ≫ a.f
  have hsquare : s.hom ≫ T.mor₁ = f ≫ sY.hom := by
    dsimp [f]
    rw [Category.assoc, ← ha]
    change s.hom ≫ T.mor₁ = q.left ≫ s₁.hom ≫ T.mor₁
    rw [← Category.assoc, MorphismProperty.Over.w q]
  have hα : uX.app s ≫ α = 𝟙 A := by
    dsimp [α]
    rw [← Category.assoc]
    have hn : uX.app s ≫ F.map p.left = uX.app sX := by
      simpa using (uX.naturality p).symm
    rw [hn, hrX]
  have hcomm : F.map f ≫ rY = α ≫ lf := by
    dsimp [f, α]
    rw [F.map_comp, hpq]
    simp only [Category.assoc]
    rw [← Category.assoc (uX.app s₁), (hlf s₁ sY a.f ha).1]
    simp only [Category.assoc, hrY, Category.comp_id]
  obtain ⟨Z', g', h', hT'⟩ := distinguished_cocone_triangle f
  let T' : Triangle C := Triangle.mk f g' h'
  obtain ⟨t, ht, ht₂, ht₃⟩ := MorphismProperty.compatible_with_triangulation
    T' T hT' hT s.hom sY.hom s.prop sY.prop hsquare.symm
  let d : T' ⟶ T := ⟨s.hom, sY.hom, t, hsquare.symm, ht₂, ht₃⟩
  obtain ⟨Y, g, h, hU⟩ := distinguished_cocone_triangle lf
  let U : Triangle D := Triangle.mk lf g h
  obtain ⟨γ, hγ₂, hγ₃⟩ := complete_distinguished_triangle_morphism
    (F.mapTriangle.obj T') U (F.map_distinguished T' hT') hU α rY hcomm
  let m : F.mapTriangle.obj T' ⟶ U := ⟨α, rY, γ, hcomm, hγ₂, hγ₃⟩
  let W : MorphismProperty (Triangle C) :=
      S.inverseImage Triangle.π₁ ⊓ (S.inverseImage Triangle.π₂ ⊓ S.inverseImage Triangle.π₃)
  let P : ObjectProperty (W.Over W T) := fun x ↦ x.left ∈ distTriang C
  let p₁ : P.FullSubcategory ⥤ S.Over ⊤ T.obj₁ := {
      obj := fun x ↦ MorphismProperty.Over.mk ⊤ x.obj.hom.hom₁ x.obj.prop.1
      map := fun f ↦ MorphismProperty.Over.homMk f.hom.left.hom₁
        (Triangle.π₁.congr_map (MorphismProperty.Over.w f.hom))
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  let p₂ : P.FullSubcategory ⥤ S.Over ⊤ T.obj₂ := {
      obj := fun x ↦ MorphismProperty.Over.mk ⊤ x.obj.hom.hom₂ x.obj.prop.2.1
      map := fun f ↦ MorphismProperty.Over.homMk f.hom.left.hom₂
        (Triangle.π₂.congr_map (MorphismProperty.Over.w f.hom))
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  let p₃ : P.FullSubcategory ⥤ S.Over ⊤ T.obj₃ := {
      obj := fun x ↦ MorphismProperty.Over.mk ⊤ x.obj.hom.hom₃ x.obj.prop.2.2
      map := fun f ↦ MorphismProperty.Over.homMk f.hom.left.hom₃
        (Triangle.π₃.congr_map (MorphismProperty.Over.w f.hom))
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  have hcat := triangle_morphism_category_cofiltered_initial S hS.1 T hT
  change IsCofiltered P.FullSubcategory ∧ p₁.Initial ∧ p₂.Initial ∧ p₃.Initial at hcat
  let : IsCofiltered P.FullSubcategory := hcat.1
  let : p₁.Initial := hcat.2.1
  let : p₂.Initial := hcat.2.2.1
  let : p₃.Initial := hcat.2.2.2
  let H : P.FullSubcategory ⥤ Triangle D :=
    P.ι ⋙ MorphismProperty.Over.forget W W T ⋙ Over.forget T ⋙ F.mapTriangle
  let j₀ : P.FullSubcategory :=
    ⟨MorphismProperty.Over.mk W d ⟨s.prop, sY.prop, ht⟩, hT'⟩
  have h₁ (V : D) : Function.Bijective (fun φ : U.obj₁ ⟶ V ↦
      (((H ⋙ Triangle.π₁).op ⋙ yoneda.obj V).ιColimitType
        (Opposite.op j₀) (m.hom₁ ≫ φ))) := by
    let G := MorphismProperty.Over.forget S ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F
    let K := G.op ⋙ yoneda.obj V
    have hb := bijective_retraction_hom_colimit G A hX uX
      ⟨sX, rX, hrX, hfacX⟩ s α hα V
    have hc := p₁.op.bijective_colimitTypePrecomp K
    apply Function.Bijective.of_comp_left (f := p₁.op.colimitTypePrecomp K)
      (g := fun φ : U.obj₁ ⟶ V ↦
        (((H ⋙ Triangle.π₁).op ⋙ yoneda.obj V).ιColimitType
          (Opposite.op j₀) (m.hom₁ ≫ φ))) ?_ hc.1
    exact hb
  have h₂ (V : D) : Function.Bijective (fun φ : U.obj₂ ⟶ V ↦
      (((H ⋙ Triangle.π₂).op ⋙ yoneda.obj V).ιColimitType
        (Opposite.op j₀) (m.hom₂ ≫ φ))) := by
    let G := MorphismProperty.Over.forget S ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F
    let K := G.op ⋙ yoneda.obj V
    have hb := bijective_retraction_hom_colimit G B hY uY
      ⟨sY, rY, hrY, hfacY⟩ sY rY hrY V
    have hc := p₂.op.bijective_colimitTypePrecomp K
    apply Function.Bijective.of_comp_left (f := p₂.op.colimitTypePrecomp K)
      (g := fun φ : U.obj₂ ⟶ V ↦
        (((H ⋙ Triangle.π₂).op ⋙ yoneda.obj V).ιColimitType
          (Opposite.op j₀) (m.hom₂ ≫ φ))) ?_ hc.1
    exact hb
  have h₃ := triangulated_hom_colimit_comparison H
    (fun j ↦ F.map_distinguished j.obj.left j.property) U hU j₀ m h₁ h₂
  refine ⟨Y, p₃.obj j₀, γ, ?_⟩
  intro V
  let K :=
    (MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F).op ⋙ yoneda.obj V
  exact (p₃.op.bijective_colimitTypePrecomp K).comp (h₃ V)

end CategoryTheory.Functor
