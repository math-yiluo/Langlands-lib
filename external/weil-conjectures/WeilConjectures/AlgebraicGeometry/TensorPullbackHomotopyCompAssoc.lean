/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.Algebra.Homology.HomotopyCategory

/-! Associativity of the pinned tensor pullback comparisons on homotopy categories. -/

@[expose] public section

universe u₁
open CategoryTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry

-- Prove the termwise compatibility with abstract functors so that checking it does not
-- repeatedly reduce the concrete tensor pullbacks and their chosen adjunctions.
private theorem mapHomotopyCategory_leftAdjointCompIso_assoc
    {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    [Preadditive C₀] [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃}
    {F₀₂ : C₀ ⥤ C₂} {F₁₃ : C₁ ⥤ C₃} {F₀₃ : C₀ ⥤ C₃}
    [F₀₁.Additive] [F₁₂.Additive] [F₂₃.Additive]
    [F₀₂.Additive] [F₁₃.Additive] [F₀₃.Additive]
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₃₂ : C₃ ⥤ C₂}
    {G₂₀ : C₂ ⥤ C₀} {G₃₁ : C₃ ⥤ C₁} {G₃₀ : C₃ ⥤ C₀}
    (a₀₁ : F₀₁ ⊣ G₁₀) (a₁₂ : F₁₂ ⊣ G₂₁) (a₂₃ : F₂₃ ⊣ G₃₂)
    (a₀₂ : F₀₂ ⊣ G₂₀) (a₁₃ : F₁₃ ⊣ G₃₁) (a₀₃ : F₀₃ ⊣ G₃₀)
    (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) (e₁₂₃ : G₃₂ ⋙ G₂₁ ≅ G₃₁)
    (e₀₁₃ : G₃₁ ⋙ G₁₀ ≅ G₃₀) (e₀₂₃ : G₃₂ ⋙ G₂₀ ≅ G₃₀)
    (he : Functor.isoWhiskerLeft G₃₂ e₀₁₂ ≪≫ e₀₂₃ =
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₁₂₃ _ ≪≫ e₀₁₃)
    {ι : Type*} (c : ComplexShape ι) (H : HomotopyCategory C₀ c) :
    (F₂₃.mapHomotopyCategory c).map
        ((Functor.mapHomotopyCategoryCompIso
          (Adjunction.leftAdjointCompIso a₀₁ a₁₂ a₀₂ e₀₁₂) c).hom.app H) ≫
      (Functor.mapHomotopyCategoryCompIso
        (Adjunction.leftAdjointCompIso a₀₂ a₂₃ a₀₃ e₀₂₃) c).hom.app H =
    (Functor.mapHomotopyCategoryCompIso
        (Adjunction.leftAdjointCompIso a₁₂ a₂₃ a₁₃ e₁₂₃) c).hom.app
          ((F₀₁.mapHomotopyCategory c).obj H) ≫
      (Functor.mapHomotopyCategoryCompIso
        (Adjunction.leftAdjointCompIso a₀₁ a₁₃ a₀₃ e₀₁₃) c).hom.app H := by
  have hi := Adjunction.leftAdjointCompIso_assoc a₀₁ a₁₂ a₂₃ a₀₂ a₁₃ a₀₃
    e₀₁₂ e₁₂₃ e₀₁₃ e₀₂₃ he
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  let q := HomotopyCategory.quotient C₃ c
  change q.map ((F₂₃.mapHomologicalComplex c).map
      ((Functor.mapHomologicalComplexCompIso
        (Adjunction.leftAdjointCompIso a₀₁ a₁₂ a₀₂ e₀₁₂) c).hom.app P)) ≫
      q.map ((Functor.mapHomologicalComplexCompIso
        (Adjunction.leftAdjointCompIso a₀₂ a₂₃ a₀₃ e₀₂₃) c).hom.app P) =
    q.map ((Functor.mapHomologicalComplexCompIso
      (Adjunction.leftAdjointCompIso a₁₂ a₂₃ a₁₃ e₁₂₃) c).hom.app
        ((F₀₁.mapHomologicalComplex c).obj P)) ≫
      q.map ((Functor.mapHomologicalComplexCompIso
        (Adjunction.leftAdjointCompIso a₀₁ a₁₃ a₀₃ e₀₁₃) c).hom.app P)
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg q.map
  ext i : 1
  have hh := congrArg (fun e ↦ e.hom.app (P.X i)) hi
  change F₂₃.map ((Adjunction.leftAdjointCompIso a₀₁ a₁₂ a₀₂ e₀₁₂).hom.app (P.X i)) ≫
      (Adjunction.leftAdjointCompIso a₀₂ a₂₃ a₀₃ e₀₂₃).hom.app (P.X i) =
    (Adjunction.leftAdjointCompIso a₁₂ a₂₃ a₁₃ e₁₂₃).hom.app (F₀₁.obj (P.X i)) ≫
      (Adjunction.leftAdjointCompIso a₀₁ a₁₃ a₀₃ e₀₁₃).hom.app (P.X i)
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp] using hh.symm

/-- The tensor pullback composition mates are associative after passage to homotopy.
Source: Mathlib `Adjunction.leftAdjointCompIso_assoc` and
the component formulas for `Scheme.Modules.pushforwardComp`; Stacks Project, Cohomology, Tag 0D5S.
(blueprint: lem-pc-tensor-pullback-homotopy-comp-assoc).
Proof: For each scheme morphism choose the adjunction pinned by
`exists_tensorPullbackAdjunction`. Its composition comparison is exactly the inverse
mate of `pushforwardComp`. Apply `Adjunction.leftAdjointCompIso_assoc` to the six
adjunctions belonging to h, f, g, h≫f, f≫g, and the total composite. The hypothesis
is the pushforward associativity identity, inverted to match these mates. Identify
the two total composites by Category.assoc, transporting the chosen adjunction too;
proof irrelevance identifies the equality transports. This gives equality of the
underived triple comparisons. Apply the additive functors termwise to complexes
and then pass to the homotopy quotient. The comparison between termwise composition
and composition of termwise functors is natural and its components are identity
maps, so both sides become precisely the two composites displayed here. Evaluate
at H. This argument uses no derived category, counit, or K-flatness. It applies to
zero complexes, empty schemes and identity morphisms without extra hypotheses. -/
theorem tensorPullback_homotopy_comp_assoc
    (a : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive)
    {W X Y Z : Scheme.{u₁}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (H : HomotopyCategory Z.Modules (ComplexShape.up ℤ)) :
    let T {X Y : Scheme.{u₁}} (f : X ⟶ Y) :=
    (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ)
    let t {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
    Functor.mapHomotopyCategoryCompIso
      ((conjugateIsoEquiv
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
        (Scheme.Modules.pushforwardComp f g).symm) (ComplexShape.up ℤ)
    (T h).map ((t f g).hom.app H) ≫ (t h (f ≫ g)).hom.app H =
      (t h f).hom.app ((T g).obj H) ≫ (t (h ≫ f) g).hom.app H := by
  let b {X Y : Scheme.{u₁}} (k : X ⟶ Y) :=
    Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)
  exact mapHomotopyCategory_leftAdjointCompIso_assoc
    (b g) (b f) (b h) (b (f ≫ g)) (b (h ≫ f)) (b (h ≫ f ≫ g))
    (Scheme.Modules.pushforwardComp f g) (Scheme.Modules.pushforwardComp h f)
    (Scheme.Modules.pushforwardComp (h ≫ f) g)
    (Scheme.Modules.pushforwardComp h (f ≫ g)) (by
      ext M U
      simp) (ComplexShape.up ℤ) H

end AlgebraicGeometry
