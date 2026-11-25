/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismDualizable
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-!

# Künneth maps as natural transformations

Let `F ⊣ G` be an adjunction between monoidal categories with `F` strong monoidal, let
`P : 𝒳 ⥤ D` and `Q : 𝒳 ⥤ C` be functors with `e : P ⋙ F ≅ Q`, and let `c : F C₀ ⟶ D₀` be a
morphism. The *Künneth map* at `M : 𝒳` is the transpose along `F ⊣ G` of
```
F (P M ⊗ C₀) ⟶ F (P M) ⊗ F C₀ ⟶ Q M ⊗ D₀,
```
the oplax structure map followed by `e_M ⊗ c`. This file packages it as a natural transformation
`P ⋙ (- ⊗ C₀) ⟶ (Q ⋙ (- ⊗ D₀)) ⋙ G` (`CategoryTheory.Adjunction.kunnethNatTrans`), proves that it
commutes with shifts when its ingredients do
(`CategoryTheory.Adjunction.commShift_kunnethNatTrans`),
and that its component at `M` is an isomorphism when `P M` is dualizable and the transpose of `c`
is an isomorphism (`CategoryTheory.Adjunction.isIso_kunnethNatTrans_app_of_isDualizable`).

All constructions are generic, so that concrete instances (for instance the ordinary Künneth map
of `WeilConjectures.TraceFormula.OrdinaryKunneth`) are obtained by specialisation and their
properties by unification with these lemmas.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (F : D ⥤ C) [F.OplaxMonoidal]

/-- The oplax structure map `F (A ⊗ C₀) ⟶ F A ⊗ F C₀` for a fixed second variable `C₀`, as a
natural transformation in `A`. -/
@[simps]
def OplaxMonoidal.δFlip (C₀ : D) :
    (curriedTensor D).flip.obj C₀ ⋙ F ⟶ F ⋙ (curriedTensor C).flip.obj (F.obj C₀) where
  app A := OplaxMonoidal.δ F A C₀
  naturality _ _ φ := (OplaxMonoidal.δ_natural_left F φ C₀).symm

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {𝒳 : Type u₃} [Category.{v₃} 𝒳] {P : 𝒳 ⥤ D} {Q : 𝒳 ⥤ C} (e : P ⋙ F ≅ Q)
  {C₀ : D} {D₀ : C} (c : F.obj C₀ ⟶ D₀)

section Oplax

variable [F.OplaxMonoidal]

/-- The transpose of the Künneth map, `F (P M ⊗ C₀) ⟶ Q M ⊗ D₀`, as a natural transformation in
`M`: the oplax structure map of `F` followed by `e_M ⊗ c`,
```
F (P M ⊗ C₀) ──δ──▶ F (P M) ⊗ F C₀ ──e_M ⊗ c──▶ Q M ⊗ D₀.
```
-/
def kunnethAdjointNatTrans :
    (P ⋙ (curriedTensor D).flip.obj C₀) ⋙ F ⟶ Q ⋙ (curriedTensor C).flip.obj D₀ :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft P (Functor.OplaxMonoidal.δFlip F C₀) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight e.hom _ ≫
    Functor.whiskerLeft Q ((curriedTensor C).flip.map c)

lemma kunnethAdjointNatTrans_app (M : 𝒳) :
    (kunnethAdjointNatTrans e c).app M =
      Functor.OplaxMonoidal.δ F (P.obj M) C₀ ≫ (e.hom.app M ⊗ₘ c) := by
  simp [kunnethAdjointNatTrans, tensorHom_def]

/-- **The Künneth map** `P M ⊗ C₀ ⟶ G (Q M ⊗ D₀)`, as a natural transformation in `M`: the
transpose along `F ⊣ G` of `kunnethAdjointNatTrans`, that is, the composite
```
P M ⊗ C₀ ──η──▶ G F (P M ⊗ C₀) ──G (δ ≫ (e_M ⊗ c))──▶ G (Q M ⊗ D₀).
```
-/
def kunnethNatTrans :
    P ⋙ (curriedTensor D).flip.obj C₀ ⟶ (Q ⋙ (curriedTensor C).flip.obj D₀) ⋙ G :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft _ adj.unit ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (kunnethAdjointNatTrans e c) G

lemma kunnethNatTrans_app_eq_homEquiv (M : 𝒳) :
    (adj.kunnethNatTrans e c).app M =
      adj.homEquiv _ _ ((kunnethAdjointNatTrans e c).app M) := by
  simp [kunnethNatTrans, homEquiv_unit]

lemma kunnethNatTrans_app (M : 𝒳) :
    (adj.kunnethNatTrans e c).app M =
      adj.homEquiv _ _ (Functor.OplaxMonoidal.δ F (P.obj M) C₀ ≫ (e.hom.app M ⊗ₘ c)) := by
  rw [kunnethNatTrans_app_eq_homEquiv, kunnethAdjointNatTrans_app]
  rfl

end Oplax

/-- The invertibility of the transpose `C₀ ⟶ G D₀` of the second factor `c`, with `adj`, `e` and
`c` read off from a statement about the Künneth map. This instantiates them by unification with
the body of a concrete Künneth map, whose terms may differ from separately elaborated ones. -/
lemma isIso_homEquiv_of_isIso_kunnethNatTrans_app [F.OplaxMonoidal] {M : 𝒳}
    (_ : IsIso ((adj.kunnethNatTrans e c).app M))
    (hc : IsIso (adj.homEquiv _ _ c)) : IsIso (adj.homEquiv _ _ c) :=
  hc

/-- **Künneth maps at dualizable objects**: if `F` is strong monoidal, `P M` is dualizable and the
transpose `C₀ ⟶ G D₀` of `c` is an isomorphism, the Künneth map at `M` is an isomorphism. -/
lemma isIso_kunnethNatTrans_app_of_isDualizable [F.Monoidal] {M : 𝒳}
    (hM : IsDualizable (P.obj M)) (hc : IsIso (adj.homEquiv _ _ c)) :
    IsIso ((adj.kunnethNatTrans e c).app M) := by
  rw [kunnethNatTrans_app]
  exact adj.isIso_homEquiv_δ_tensorHom_of_isDualizable hM (e.hom.app M) inferInstance c hc

section Shift

variable (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift 𝒳 A]
  [F.CommShift A] [G.CommShift A] [adj.CommShift A] [P.CommShift A] [Q.CommShift A]
  [((curriedTensor D).flip.obj C₀).CommShift A] [((curriedTensor C).flip.obj D₀).CommShift A]
  [((curriedTensor C).flip.obj (F.obj C₀)).CommShift A]

/-- The Künneth map commutes with shifts if its ingredients do: the oplax structure map, the
isomorphism `e` and the morphism `- ⊗ c`. -/
lemma commShift_kunnethNatTrans [F.OplaxMonoidal]
    [NatTrans.CommShift (Functor.OplaxMonoidal.δFlip F C₀) A] [NatTrans.CommShift e.hom A]
    [NatTrans.CommShift ((curriedTensor C).flip.map c) A] :
    NatTrans.CommShift (adj.kunnethNatTrans e c) A :=
  have : NatTrans.CommShift (kunnethAdjointNatTrans e c) A := by
    dsimp only [kunnethAdjointNatTrans]
    infer_instance
  NatTrans.CommShift.of_homEquiv adj (kunnethAdjointNatTrans e c) _
    (kunnethNatTrans_app_eq_homEquiv adj e c)

end Shift

end CategoryTheory.Adjunction
