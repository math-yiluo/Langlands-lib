/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge

/-! # Morphisms between pointwise left-derived values

Source: Stacks Project, Derived Categories, Lemma 05SA(2)
(blueprint: lem-pur-derived-functor-morphisms-05sa).
-/

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- In Situation 05S8, a morphism between objects where `LF` is defined induces a unique
morphism between its values, compatible with every denominator square. The supplied
natural transformations are the cone maps exhibiting these values as essentially
constant pro-objects: `huX` and `huY` are precisely the retraction and common-stage
conditions of `IsEssentiallyConstantProDiagram`, with its existential cone made explicit.
Source: Stacks Project, Derived Categories, Lemma 05SA(2)
(blueprint: lem-pur-derived-functor-morphisms-05sa).

Proof: (1) The bridge `lem-pur-left-derived-defined-pointwise-kan-bridge` supplies limit
cones over `(Q(X) ↓ Q)` and `(Q(Y) ↓ Q)`, whose denominator projections are the given
cone maps. (2) Precomposition with `Q(f)` sends `(Z', φ)` over `Q(Y)` to `(Z', Q(f) ≫ φ)`
over `Q(X)`. Restrict the first limit cone along this functor and use the second limit's
universal property to obtain the morphism between values.
(3) For a denominator square, the identity
`Q(f) ≫ inv (Q(s')) = inv (Q(s)) ≫ Q(f')` and cone naturality give the first square.
Applying `F` to the original square gives the second square, hence the outer rectangle.
(4) For uniqueness, `lem-pc-right-localization-hom-colimit` writes every structured-arrow
projection as a denominator projection followed by `F(g)`. MS2 completes `f` and that
denominator to a square. The required first-square equation makes both candidate maps
agree after every projection; the limit universal property then makes them equal. -/
theorem leftDerived_value_morphism
    {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty C) (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    {X Y : C} (f : X ⟶ Y) (LX LY : D)
    (hX : F.IsTriangulatedLeftDerivedValue S hS X LX)
    (hY : F.IsTriangulatedLeftDerivedValue S hS Y LY)
    (uX : (Functor.const (S.Over ⊤ X)).obj LX ⟶
      MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F)
    (uY : (Functor.const (S.Over ⊤ Y)).obj LY ⟶
      MorphismProperty.Over.forget S ⊤ Y ⋙ Over.forget Y ⋙ F)
    (huX : ∃ s₀ : S.Over ⊤ X, ∃ r : F.obj s₀.left ⟶ LX,
      uX.app s₀ ≫ r = 𝟙 LX ∧
        ∀ s : S.Over ⊤ X, ∃ t : S.Over ⊤ X, ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
          F.map b.left = F.map a.left ≫ r ≫ uX.app s)
    (huY : ∃ s₀ : S.Over ⊤ Y, ∃ r : F.obj s₀.left ⟶ LY,
      uY.app s₀ ≫ r = 𝟙 LY ∧
        ∀ s : S.Over ⊤ Y, ∃ t : S.Over ⊤ Y, ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
          F.map b.left = F.map a.left ≫ r ≫ uY.app s) :
    ∃! lf : LX ⟶ LY,
      ∀ (s : S.Over ⊤ X) (s' : S.Over ⊤ Y) (f' : s.left ⟶ s'.left),
        s.hom ≫ f = f' ≫ s'.hom →
          uX.app s ≫ F.map f' = lf ≫ uY.app s' ∧
            (uX.app s ≫ F.map s.hom) ≫ F.map f =
              lf ≫ uY.app s' ≫ F.map s'.hom := by
  classical
  let : S.HasRightCalculusOfFractions := hS.1.1.2
  let Q := S.Q
  obtain ⟨_, πX, _, hdenX, _⟩ :=
    leftDerived_defined_pointwiseKan_bridge S Q F X LX hX uX huX
  obtain ⟨_, πY, ⟨hπY⟩, hdenY, _⟩ :=
    leftDerived_defined_pointwiseKan_bridge S Q F Y LY hY uY huY
  let c : Cone (StructuredArrow.proj (Q.obj Y) Q ⋙ F) :=
    Cone.mk LX
      { app := fun j ↦ πX.app ((StructuredArrow.map (Q.map f)).obj j)
        naturality := fun i j g ↦ by
          simpa using (πX.naturality ((StructuredArrow.map (Q.map f)).map g)) }
  let lf : LX ⟶ LY := hπY.lift c
  have hlf (s : S.Over ⊤ X) (s' : S.Over ⊤ Y) (f' : s.left ⟶ s'.left)
      (hsq : s.hom ≫ f = f' ≫ s'.hom) :
      uX.app s ≫ F.map f' = lf ≫ uY.app s' := by
    let i := StructuredArrow.mk (Localization.isoOfHom Q S s.hom s.prop).inv
    let j := StructuredArrow.mk (Localization.isoOfHom Q S s'.hom s'.prop).inv
    let g : i ⟶ (StructuredArrow.map (Q.map f)).obj j :=
      StructuredArrow.homMk f' (by
        apply (cancel_mono (Localization.isoOfHom Q S s'.hom s'.prop).hom).mp
        simp only [Category.assoc, Localization.isoOfHom_hom,
          StructuredArrow.map_obj_hom]
        rw [← Q.map_comp, ← hsq, Q.map_comp]
        change (Localization.isoOfHom Q S s.hom s.prop).inv ≫ Q.map s.hom ≫ Q.map f =
          Q.map f ≫ (Localization.isoOfHom Q S s'.hom s'.prop).inv ≫ Q.map s'.hom
        simp only [Localization.isoOfHom_inv_hom_id_assoc,
          Localization.isoOfHom_inv_hom_id]
        exact (Category.comp_id (Q.map f)).symm)
    have hn := πX.naturality g
    change 𝟙 LX ≫ πX.app ((StructuredArrow.map (Q.map f)).obj j) =
      πX.app i ≫ F.map f' at hn
    rw [Category.id_comp] at hn
    have hn' := hn.symm
    rw [hdenX s] at hn'
    rw [hn', ← hdenY s']
    exact (hπY.fac c j).symm
  refine ⟨lf, ?_, ?_⟩
  · intro s s' f' hsq
    refine ⟨hlf s s' f' hsq, ?_⟩
    calc
      (uX.app s ≫ F.map s.hom) ≫ F.map f =
          uX.app s ≫ F.map (s.hom ≫ f) := by rw [F.map_comp, Category.assoc]
      _ = uX.app s ≫ F.map (f' ≫ s'.hom) := by rw [hsq]
      _ = lf ≫ uY.app s' ≫ F.map s'.hom := by
        rw [F.map_comp, ← Category.assoc, hlf s s' f' hsq, Category.assoc]
  · intro m hm
    -- One denominator leg suffices: it has the supplied right inverse.
    obtain ⟨s₀, r, hr, _⟩ := huY
    obtain ⟨a, ha⟩ :=
      (MorphismProperty.LeftFraction.mk f s₀.hom s₀.prop).exists_rightFraction
    let s : S.Over ⊤ X := ⟨Over.mk a.s, a.hs⟩
    have he : m ≫ uY.app s₀ = lf ≫ uY.app s₀ :=
      (hm s s₀ a.f ha).1.symm.trans (hlf s s₀ a.f ha)
    calc
      m = (m ≫ uY.app s₀) ≫ r := by rw [Category.assoc, hr, Category.comp_id]
      _ = (lf ≫ uY.app s₀) ≫ r := by rw [he]
      _ = lf := by rw [Category.assoc, hr, Category.comp_id]

end CategoryTheory.Functor
