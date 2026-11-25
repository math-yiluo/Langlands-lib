/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.CategoryTheory.Monoidal.Braided.Multifunctor
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric

/-!
# The braiding of the derived tensor product, and the symmetry of `D(C)`

Let `C` be an abelian monoidal category satisfying the hypotheses under which the derived
category `D(C)` is monoidal for the derived tensor product, i.e. those of
`WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`: the derived tensor
product is the binary left derived functor of the tensor product on
`K(C) := HomotopyCategory C (ComplexShape.up ℤ)`. This file constructs, for `C` braided, the
braiding isomorphisms of `K(C)` and of `D(C)` as natural isomorphisms of bifunctors, and states
that `D(C)` is symmetric if `C` is.

The construction follows the chain
`C braided ⟹ Koszul braiding on CochainComplex C ℤ ⟹ K(C) braided ⟹ D(C) braided`:

1. **The Koszul braiding on complexes (the step carrying the sign content).** The braiding of
   `C` cannot be transported degreewise: on the summand `X p ⊗ Y q` of the tensor product of
   complexes the correct map is `(-1) ^ (p * q) • β_ (X p) (Y q)`, the Koszul sign being what
   makes the flip commute with the total differential. It is *assembled*, not recomputed
   (`HomologicalComplex.braiding`): the braiding of `C` transported through `mapBifunctor`
   (`HomologicalComplex.mapBifunctorIsoOfIso`), followed by the flip isomorphism
   `HomologicalComplex.mapBifunctorFlipIso` of the total complex, which carries the sign
   `σ` of the complex shape sign formalism.
2. **Descent to the homotopy category.** The braiding is an honest isomorphism of complexes,
   natural in both variables, so it descends along the quotient functor
   (`HomotopyCategory.MonoidalCategory.braiding`, via `Quotient.natIsoLift₂`).
3. **Transport through the derived tensor.** Write `T := curriedTensor K(C)` and
   `T^L := curriedTensor D(C)`, so that `T^L` is the binary left derived functor of `T`. A
   morphism `τ : T.flip ⟶ T` lifts to `T^L.flip ⟶ T^L` by the binary left derived lifting
   property (`DerivedMonoidal.flipLift`). The derived braiding `DerivedMonoidal.braiding` is
   the lift of the braiding of `K(C)`, evaluated at swapped arguments, with inverse the lift of
   its inverse; the two are mutually inverse by binary left derived uniqueness
   (`Functor.leftDerived₂_ext`).

## Implementation notes

No braided structure is declared here. For a general complex shape `c`, the sign of
`TotalComplexShapeSymmetry c c c` is only determined up to a global sign, and replacing `σ` by
`-σ` breaks the hexagon identities, so the braiding of `K(C)` is only claimed to be braided for
`c = ComplexShape.up ℤ`, where this is proved (`HomotopyCategory.braidedCategory`). The braided
structure on `D(C)` is the proved `DerivedCategory.braidedCategory'` (see
`CategoryTheory.DerivedMonoidal.braidedCategory'`); it is not a global instance, and the
symmetric structure `DerivedCategory.symmetricCategory` built on it is a `def` as well.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

/-! ### Natural transformations between bifunctors on quotient categories -/

namespace CategoryTheory.Quotient

open _root_.CategoryTheory.Functor

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  (r₁ : HomRel C₁) (r₂ : HomRel C₂)

/-- A natural transformation between bifunctors on quotient categories, from one between their
precompositions with the quotient functors. -/
def natTransLift₂ {F G : Quotient r₁ ⥤ Quotient r₂ ⥤ D}
    (τ : (((whiskeringLeft₂ D).obj (functor r₁)).obj (functor r₂)).obj F ⟶
      (((whiskeringLeft₂ D).obj (functor r₁)).obj (functor r₂)).obj G) :
    F ⟶ G where
  app X₁ :=
    { app X₂ := (τ.app X₁.as).app X₂.as
      naturality := by
        rintro _ _ ⟨f₂⟩
        exact (τ.app X₁.as).naturality f₂ }
  naturality := by
    rintro _ _ ⟨f₁⟩
    ext ⟨X₂⟩
    exact NatTrans.congr_app (τ.naturality f₁) X₂

@[simp]
lemma natTransLift₂_app_app {F G : Quotient r₁ ⥤ Quotient r₂ ⥤ D}
    (τ : (((whiskeringLeft₂ D).obj (functor r₁)).obj (functor r₂)).obj F ⟶
      (((whiskeringLeft₂ D).obj (functor r₁)).obj (functor r₂)).obj G) (X₁ : C₁) (X₂ : C₂) :
    ((natTransLift₂ r₁ r₂ τ).app ((functor r₁).obj X₁)).app ((functor r₂).obj X₂) =
      (τ.app X₁).app X₂ := rfl

/-- A natural isomorphism between bifunctors on quotient categories, from one between their
precompositions with the quotient functors. -/
@[simps]
def natIsoLift₂ {F G : Quotient r₁ ⥤ Quotient r₂ ⥤ D}
    (τ : (((whiskeringLeft₂ D).obj (functor r₁)).obj (functor r₂)).obj F ≅
      (((whiskeringLeft₂ D).obj (functor r₁)).obj (functor r₂)).obj G) :
    F ≅ G where
  hom := natTransLift₂ _ _ τ.hom
  inv := natTransLift₂ _ _ τ.inv
  hom_inv_id := by
    ext ⟨X₁⟩ ⟨X₂⟩
    exact NatTrans.congr_app (NatTrans.congr_app τ.hom_inv_id X₁) X₂
  inv_hom_id := by
    ext ⟨X₁⟩ ⟨X₂⟩
    exact NatTrans.congr_app (NatTrans.congr_app τ.inv_hom_id X₁) X₂

end CategoryTheory.Quotient

/-! ### The Koszul braiding on complexes -/

namespace HomologicalComplex

section MapBifunctor

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  {F G : C₁ ⥤ C₂ ⥤ D} [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms] [∀ X₁, (G.obj X₁).PreservesZeroMorphisms]
  (e : F ≅ G) (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)

/-- The isomorphism of bicomplexes `F(K₁, K₂) ≅ G(K₁, K₂)` induced by an isomorphism of
bifunctors `e : F ≅ G`. -/
@[simps]
noncomputable def mapBifunctorHomologicalComplexObjObjIso :
    ((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂ ≅
      ((G.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂ where
  hom := HomologicalComplex₂.homMk (fun ⟨i₁, i₂⟩ ↦ (e.hom.app (K₁.X i₁)).app (K₂.X i₂))
    (fun _ _ _ _ ↦ (NatTrans.congr_app (e.hom.naturality _) _).symm)
    (fun _ _ _ _ ↦ ((e.hom.app _).naturality _).symm)
  inv := HomologicalComplex₂.homMk (fun ⟨i₁, i₂⟩ ↦ (e.inv.app (K₁.X i₁)).app (K₂.X i₂))
    (fun _ _ _ _ ↦ (NatTrans.congr_app (e.inv.naturality _) _).symm)
    (fun _ _ _ _ ↦ ((e.inv.app _).naturality _).symm)
  hom_inv_id := by ext; simp [← NatTrans.comp_app]; rfl
  inv_hom_id := by ext; simp [← NatTrans.comp_app]; rfl

variable (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor K₁ K₂ G c]

/-- The isomorphism `mapBifunctor K₁ K₂ F c ≅ mapBifunctor K₁ K₂ G c` induced by an
isomorphism of bifunctors `e : F ≅ G`. -/
noncomputable def mapBifunctorIsoOfIso :
    mapBifunctor K₁ K₂ F c ≅ mapBifunctor K₁ K₂ G c :=
  HomologicalComplex₂.total.mapIso (mapBifunctorHomologicalComplexObjObjIso e K₁ K₂) c

variable {K₁ K₂} {L₁ : HomologicalComplex C₁ c₁} {L₂ : HomologicalComplex C₂ c₂}
  (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) [HasMapBifunctor L₁ L₂ F c] [HasMapBifunctor L₁ L₂ G c]

@[reassoc (attr := simp)]
lemma mapBifunctorIsoOfIso_hom_naturality :
    mapBifunctorMap φ₁ φ₂ F c ≫ (mapBifunctorIsoOfIso e L₁ L₂ c).hom =
      (mapBifunctorIsoOfIso e K₁ K₂ c).hom ≫ mapBifunctorMap φ₁ φ₂ G c := by
  ext j i₁ i₂ h
  simp [mapBifunctorIsoOfIso, ιMapBifunctor]

end MapBifunctor

section Braiding

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]
  [MonoidalPreadditive C] {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I}
  [c.TensorSigns] [TotalComplexShapeSymmetry c c c]

/-- The **Koszul braiding** `K₁ ⊗ K₂ ≅ K₂ ⊗ K₁` of complexes, which on the summand
`K₁.X p ⊗ K₂.X q` is `(-1) ^ (p * q) • β_ (K₁.X p) (K₂.X q)` (for `c = ComplexShape.up ℤ`): the
braiding of `C` transported through `mapBifunctor`, followed by the flip isomorphism of the
total complex, which carries the sign `ComplexShape.σ`. -/
noncomputable def braiding (K₁ K₂ : HomologicalComplex C c)
    [HasMapBifunctor K₁ K₂ (curriedTensor C) c] [HasMapBifunctor K₂ K₁ (curriedTensor C) c] :
    mapBifunctor K₁ K₂ (curriedTensor C) c ≅ mapBifunctor K₂ K₁ (curriedTensor C) c :=
  mapBifunctorIsoOfIso (BraidedCategory.curriedBraidingNatIso C) K₁ K₂ c ≪≫
    mapBifunctorFlipIso K₂ K₁ (curriedTensor C) c

@[reassoc]
lemma braiding_hom_naturality {K₁ K₂ L₁ L₂ : HomologicalComplex C c}
    [HasMapBifunctor K₁ K₂ (curriedTensor C) c] [HasMapBifunctor K₂ K₁ (curriedTensor C) c]
    [HasMapBifunctor L₁ L₂ (curriedTensor C) c] [HasMapBifunctor L₂ L₁ (curriedTensor C) c]
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) :
    mapBifunctorMap f₁ f₂ (curriedTensor C) c ≫ (braiding L₁ L₂).hom =
      (braiding K₁ K₂).hom ≫ mapBifunctorMap f₂ f₁ (curriedTensor C) c := by
  simp [braiding]

end Braiding

end HomologicalComplex

/-! ### The braiding on the homotopy category -/

namespace HomotopyCategory.MonoidalCategory

variable (C : Type*) [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [(curriedTensor C).Additive]
  [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns]
  [∀ (X₁ X₂ : GradedObject I C), X₁.HasTensor X₂]
  [∀ (X₁ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).obj X₁)]
  [∀ (X₂ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] [DecidableEq I]
  [∀ (K₁ K₂ : HomologicalComplex C c),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor C) c]
  [BraidedCategory C] [MonoidalPreadditive C] [TotalComplexShapeSymmetry c c c]

/-- The braiding `bifunctor C c ≅ (bifunctor C c).flip` of the homotopy category `K(C)`: the
image of the Koszul braiding `HomologicalComplex.braiding` of complexes under the quotient
functor. -/
noncomputable def braiding : bifunctor C c ≅ (bifunctor C c).flip :=
  Quotient.natIsoLift₂ _ _ (NatIso.ofComponents (fun K₁ ↦ NatIso.ofComponents
    (fun K₂ ↦ (quotient C c).mapIso (HomologicalComplex.braiding K₁ K₂)) (fun f₂ ↦ by
      change (quotient C c).map (HomologicalComplex.mapBifunctorMap (𝟙 K₁) f₂ _ c) ≫ _ =
        _ ≫ (quotient C c).map (HomologicalComplex.mapBifunctorMap f₂ (𝟙 K₁) _ c)
      exact ((quotient C c).map_comp _ _).symm.trans (((quotient C c).congr_map
        (HomologicalComplex.braiding_hom_naturality (𝟙 K₁) f₂)).trans
          ((quotient C c).map_comp _ _))))
    (fun {K₁ L₁} f₁ ↦ by
      ext K₂
      change (quotient C c).map (HomologicalComplex.mapBifunctorMap f₁ (𝟙 K₂) _ c) ≫
          (quotient C c).map (HomologicalComplex.braiding L₁ K₂).hom =
        (quotient C c).map (HomologicalComplex.braiding K₁ K₂).hom ≫
          (quotient C c).map (HomologicalComplex.mapBifunctorMap (𝟙 K₂) f₁ _ c)
      exact ((quotient C c).map_comp _ _).symm.trans (((quotient C c).congr_map
        (HomologicalComplex.braiding_hom_naturality f₁ (𝟙 K₂))).trans
          ((quotient C c).map_comp _ _))))

end HomotopyCategory.MonoidalCategory

/-! ### Transport of a braiding through a derived monoidal structure -/

namespace CategoryTheory.DerivedMonoidal

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.ContainsIdentities]
  [L.HasDerivedMonoidalCategory W]

/-- The morphism `(-⊗ᴸ-).flip ⟶ (-⊗ᴸ-)` of derived tensor products induced by a morphism
`τ : (-⊗-).flip ⟶ (-⊗-)` of tensor products in `C`: the lift, by the universal property of the
binary left derived functor `-⊗ᴸ-`, of `L(X₂) ⊗ᴸ L(X₁) ⟶ L(X₂ ⊗ X₁) ⟶ L(X₁ ⊗ X₂)`. -/
noncomputable def flipLift (τ : (curriedTensor C).flip ⟶ curriedTensor C) :
    (bifunctor L W).flip ⟶ bifunctor L W :=
  (bifunctor L W).leftDerived₂Lift (counit L W) W W (bifunctor L W).flip
    ((flipFunctor _ _ _).map (counit L W) ≫
      whiskerRight τ ((whiskeringRight _ _ _).obj (toDerivedMonoidal L W)))

@[reassoc (attr := simp)]
lemma flipLift_fac_app_app (τ : (curriedTensor C).flip ⟶ curriedTensor C) (X₁ X₂ : C) :
    ((flipLift L W τ).app ((toDerivedMonoidal L W).obj X₁)).app
        ((toDerivedMonoidal L W).obj X₂) ≫ ((counit L W).app X₁).app X₂ =
      ((counit L W).app X₂).app X₁ ≫ (toDerivedMonoidal L W).map ((τ.app X₁).app X₂) :=
  leftDerived₂_fac_app_app _ _ _ _ _ _ _ _

variable [BraidedCategory C]

/-- The derived braiding `X₁ ⊗ᴸ X₂ ≅ X₂ ⊗ᴸ X₁`: the braiding of `C`, transported to the derived
tensor product by the universal property of the binary left derived functor, in both
directions. -/
noncomputable def braiding : bifunctor L W ≅ (bifunctor L W).flip where
  hom := (flipFunctor _ _ _).map
    (flipLift L W ((flipFunctor _ _ _).map (BraidedCategory.curriedBraidingNatIso C).hom))
  inv := flipLift L W (BraidedCategory.curriedBraidingNatIso C).inv
  hom_inv_id := by
    apply leftDerived₂_ext (bifunctor L W) (counit L W) W W
    ext X₁ X₂
    dsimp
    rw [Category.assoc, flipLift_fac_app_app, flipLift_fac_app_app_assoc]
    simp [← Functor.map_comp]
  inv_hom_id := by
    have key :
        (flipFunctor _ _ _).map (flipLift L W (BraidedCategory.curriedBraidingNatIso C).inv) ≫
        flipLift L W ((flipFunctor _ _ _).map (BraidedCategory.curriedBraidingNatIso C).hom) =
          𝟙 _ := by
      apply leftDerived₂_ext (bifunctor L W) (counit L W) W W
      ext X₁ X₂
      dsimp
      rw [Category.assoc, flipLift_fac_app_app, flipLift_fac_app_app_assoc]
      simp [← Functor.map_comp]
    ext X₁ X₂
    exact NatTrans.congr_app (NatTrans.congr_app key X₂) X₁

end CategoryTheory.DerivedMonoidal

/-! ### The derived category -/

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

local instance hasColimitsOfSize_symmetricCategory : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]

/-- The derived category of a symmetric abelian monoidal category is symmetric for the
derived tensor product, with the braiding `DerivedCategory.braidedCategory'`. Only the symmetry
identity law has to be proved. Being an identity in two variables, it follows from the symmetry of
`K(C)` by binary left derived extensionality. -/
@[instance_reducible]
noncomputable def symmetricCategory : SymmetricCategory (DerivedCategory C) where
  __ := braidedCategory' C
  symmetry X Y := by
    exact braiding_hom_braiding_hom C (fun _ _ ↦ SymmetricCategory.symmetry _ _) X Y

end DerivedCategory
