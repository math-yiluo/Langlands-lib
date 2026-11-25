/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.CategoryTheory.TriangleMorphismCategory
import WeilConjectures.CategoryTheory.TriangulatedHomColimitComparison
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit
import Mathlib.CategoryTheory.Limits.Final.Type

/-! # Five-lemma comparison for a triangle retraction

Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause (dual argument).
-/

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

private theorem retraction_homColimit_bijective
    {J : Type u} {E : Type uD} [Category.{v} J] [Category.{vD} E]
    (M : J ⥤ E) (X : E) (hM : IsEssentiallyConstantProDiagram M X)
    (u : (Functor.const J).obj X ⟶ M)
    (hu : ∃ j0 : J, ∃ r : M.obj j0 ⟶ X, u.app j0 ≫ r = 𝟙 X ∧
      ∀ j : J, ∃ k : J, ∃ a : k ⟶ j0, ∃ b : k ⟶ j,
        M.map b = M.map a ≫ r ≫ u.app j)
    (j : J) (r : M.obj j ⟶ X) (hr : u.app j ≫ r = 𝟙 X) (W : E) :
    Function.Bijective (fun f : X ⟶ W ↦
      (M.op ⋙ yoneda.obj W).ιColimitType (Opposite.op j) (r ≫ f)) := by
  obtain ⟨q, hq, hrep⟩ := essentiallyConstantPro_hom_colimit M X hM u hu W
  let g := fun f : X ⟶ W ↦
    (M.op ⋙ yoneda.obj W).ιColimitType (Opposite.op j) (r ≫ f)
  have hcomp (f : X ⟶ W) : q (g f) = f := by
    rw [hrep]
    rw [← Category.assoc, hr]
    exact Category.id_comp f
  constructor
  · intro f f' he
    exact (hcomp f).symm.trans ((congrArg q he).trans (hcomp f'))
  · intro x
    exact ⟨q x, hq.1 (hcomp (q x))⟩

/-- A triangle retraction on the first two vertices induces a third Hom-colimit bijection.
Source: Stacks Project, Derived Categories, Lemma 05SC, the five-term Hom diagram,
dualized to LF; Categories, Tag 05PZ and the initial colimit comparison Tag 0A1T.
(blueprint: lem-pur-triangle-retraction-hom-colimit).

Proof: Take I to be the cofiltered category of incoming distinguished denominator
triangles over T from Tag 05R9. Its three vertex projections p1, p2, p3 are initial.
The supplied sigma defines an object i0 of I with source U. Restrict uX and uY
along p1 and p2; initial_iff_essentiallyConstantProDiagram gives both essential
constancy and the common-stage certificates for these very cones. Tag 05PZ gives
a bijection from each restricted Hom-colimit to Hom(LX,W) or Hom(LY,W), with its
representative formula. At i0, precomposition with rho.hom1 or rho.hom2 is its
inverse: composing with the canonical bijection gives the identity by hretract1
or hretract2. Hence both first-vertex and second-vertex comparisons are bijective
for every W. The functor G sends each source triangle to its F-image; exactness of
F makes every G(i) distinguished. Apply triangulated_hom_colimit_comparison to G,
the fixed distinguished triangle, i0 and rho to obtain the third comparison.
Finally p3.op is final, so Mathlib's bijective_colimitTypePrecomp transports this
bijection to the full third denominator Hom-colimit. Its representative equation
sends i0 to sigma.hom3 and leaves rho.hom3 followed by phi unchanged. Working over
T directly avoids denominator postcomposition with sigma and its initiality proof.
No third derived value or completion theorem is used.

Edge cases: when rho is the identity comparison and S contains only isomorphisms,
the function is the ordinary canonical Hom-colimit bijection. Contractible and split
triangles satisfy the same exact-sequence argument. The retraction equations are
essential: merely supplying arbitrary maps at the first two vertices would be false. -/
theorem leftDerived_triangle_retraction_homColimit
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
    (LX LY : D)
    (hX : F.IsTriangulatedLeftDerivedValue S hS T.obj₁ LX)
    (hY : F.IsTriangulatedLeftDerivedValue S hS T.obj₂ LY)
    (uX : (Functor.const (S.Over ⊤ T.obj₁)).obj LX ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F)
    (uY : (Functor.const (S.Over ⊤ T.obj₂)).obj LY ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F)
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
    (lf : LX ⟶ LY) (K : D) (b : LY ⟶ K)
    (c : K ⟶ (shiftFunctor D (1 : ℤ)).obj LX)
    (hK : Triangle.mk lf b c ∈ distTriang D)
    (U : Triangle C) (hU : U ∈ distTriang C) (sigma : U ⟶ T)
    (hsigma₁ : S sigma.hom₁) (hsigma₂ : S sigma.hom₂) (hsigma₃ : S sigma.hom₃)
    (rho : F.mapTriangle.obj U ⟶ Triangle.mk lf b c)
    (hretract₁ : uX.app (MorphismProperty.Over.mk ⊤ sigma.hom₁ hsigma₁) ≫
      rho.hom₁ = 𝟙 LX)
    (hretract₂ : uY.app (MorphismProperty.Over.mk ⊤ sigma.hom₂ hsigma₂) ≫
      rho.hom₂ = 𝟙 LY) :
    ∀ W : D, Function.Bijective (fun phi : K ⟶ W ↦
      ((MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F).op ⋙
        yoneda.obj W).ιColimitType
          (Opposite.op (MorphismProperty.Over.mk ⊤ sigma.hom₃ hsigma₃))
          (rho.hom₃ ≫ phi)) := by
  classical
  let : S.HasLeftCalculusOfFractions := hS.1.1.1
  let : S.IsCompatibleWithTriangulation := hS.2
  let V : MorphismProperty (Triangle C) :=
    S.inverseImage Triangle.π₁ ⊓ (S.inverseImage Triangle.π₂ ⊓ S.inverseImage Triangle.π₃)
  let P : ObjectProperty (V.Over V T) := fun x ↦ x.left ∈ distTriang C
  let p1 : P.FullSubcategory ⥤ S.Over ⊤ T.obj₁ := {
    obj := fun x ↦ MorphismProperty.Over.mk ⊤ x.obj.hom.hom₁ x.obj.prop.1
    map := fun f ↦ MorphismProperty.Over.homMk f.hom.left.hom₁
      (Triangle.π₁.congr_map (MorphismProperty.Over.w f.hom)) }
  let p2 : P.FullSubcategory ⥤ S.Over ⊤ T.obj₂ := {
    obj := fun x ↦ MorphismProperty.Over.mk ⊤ x.obj.hom.hom₂ x.obj.prop.2.1
    map := fun f ↦ MorphismProperty.Over.homMk f.hom.left.hom₂
      (Triangle.π₂.congr_map (MorphismProperty.Over.w f.hom)) }
  let p3 : P.FullSubcategory ⥤ S.Over ⊤ T.obj₃ := {
    obj := fun x ↦ MorphismProperty.Over.mk ⊤ x.obj.hom.hom₃ x.obj.prop.2.2
    map := fun f ↦ MorphismProperty.Over.homMk f.hom.left.hom₃
      (Triangle.π₃.congr_map (MorphismProperty.Over.w f.hom)) }
  obtain ⟨hI, hp1, hp2, hp3⟩ := triangle_morphism_category_cofiltered_initial S hS.1 T hT
  let : IsCofiltered P.FullSubcategory := hI
  let : p1.Initial := hp1
  let : p2.Initial := hp2
  let : p3.Initial := hp3
  let MX := MorphismProperty.Over.forget S ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F
  let MY := MorphismProperty.Over.forget S ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F
  let : IsCofiltered (S.Over ⊤ T.obj₁) := hX.1
  let : IsCofiltered (S.Over ⊤ T.obj₂) := hY.1
  let vx : (Functor.const P.FullSubcategory).obj LX ⟶ p1 ⋙ MX := {
    app := fun i ↦ uX.app (p1.obj i)
    naturality := fun _ _ f ↦ by simpa [MX] using uX.naturality (p1.map f) }
  let vy : (Functor.const P.FullSubcategory).obj LY ⟶ p2 ⋙ MY := {
    app := fun i ↦ uY.app (p2.obj i)
    naturality := fun _ _ f ↦ by simpa [MY] using uY.naturality (p2.map f) }
  have hx := initial_iff_essentiallyConstantProDiagram p1 MX LX
  have hy := initial_iff_essentiallyConstantProDiagram p2 MY LY
  let G : P.FullSubcategory ⥤ Triangle D :=
    P.ι ⋙ MorphismProperty.Over.forget V V T ⋙ Over.forget T ⋙ F.mapTriangle
  let i0 : P.FullSubcategory :=
    ⟨MorphismProperty.Over.mk V sigma ⟨hsigma₁, hsigma₂, hsigma₃⟩, hU⟩
  have h1 (W : D) : Function.Bijective (fun f : LX ⟶ W ↦
      ((G ⋙ Triangle.π₁).op ⋙ yoneda.obj W).ιColimitType
        (Opposite.op i0) (rho.hom₁ ≫ f)) := by
    exact retraction_homColimit_bijective (p1 ⋙ MX) LX (hx.1.mp hX) vx
      (hx.2.1 uX huX) i0 rho.hom₁ hretract₁ W
  have h2 (W : D) : Function.Bijective (fun f : LY ⟶ W ↦
      ((G ⋙ Triangle.π₂).op ⋙ yoneda.obj W).ιColimitType
        (Opposite.op i0) (rho.hom₂ ≫ f)) := by
    exact retraction_homColimit_bijective (p2 ⋙ MY) LY (hy.1.mp hY) vy
      (hy.2.1 uY huY) i0 rho.hom₂ hretract₂ W
  have hmid := triangulated_hom_colimit_comparison G
    (fun i ↦ F.map_distinguished _ i.property) (Triangle.mk lf b c) hK i0 rho h1 h2
  intro W
  let H := (MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F).op ⋙
    yoneda.obj W
  exact (p3.op.bijective_colimitTypePrecomp H).comp (hmid W)

end CategoryTheory.Functor
