/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Internal homs along exact monoidal functors

Let `C` be a braided monoidal closed preadditive category. The internal hom `[-, Q]` turns
cokernels into kernels (`CategoryTheory.MonoidalClosed.isLimitKernelForkPreApp`): if
`π : P₀ ⟶ P` is a cokernel of `f : P₁ ⟶ P₀`, then `[π, Q] : [P, Q] ⟶ [P₀, Q]` is a kernel of
`[f, Q]`. It is additive in the first variable (`CategoryTheory.MonoidalClosed.pre_add_app`).

Let `F : C ⥤ D` be a lax monoidal functor to another monoidal closed category. We give criteria
for the comparison map `F [P, Q] ⟶ [F P, F Q]`
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) to be an isomorphism: this holds

- for `P = 𝟙_ C` if the unit map `ε F` is an isomorphism
  (`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_app_unit`);
- for `P` isomorphic to an object for which it holds
  (`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_app_iff_of_iso_left`);
- for `P` a finite biproduct of objects for which it holds, if `F` is additive
  (`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_app_biproduct`);
- for `P` the cokernel of a morphism `P₁ ⟶ P₀` between objects for which it holds, if `F`
  preserves the kernel of `[P₀, Q] ⟶ [P₁, Q]` and maps the projection onto the cokernel to an
  epimorphism (`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_app_of_isColimit`).

For instance, an exact monoidal functor out of the category of modules over a commutative ring
preserves internal homs out of finitely presented modules.
-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory

namespace MonoidalClosed

/-- The internal hom `[𝟙_ C, X]` out of the unit is `X`, through evaluation. -/
lemma isIso_leftUnitor_inv_comp_ev {C : Type*} [Category* C] [MonoidalCategory C]
    [MonoidalClosed C] (X : C) :
    IsIso ((λ_ ((ihom (𝟙_ C)).obj X)).inv ≫ (ihom.ev (𝟙_ C)).app X) := by
  refine ⟨curry (λ_ X).hom, ?_, ?_⟩
  · rw [← curry_natural_left, leftUnitor_naturality, Iso.hom_inv_id_assoc, ← uncurry_id_eq_ev,
      curry_uncurry]
  · rw [leftUnitor_inv_naturality_assoc, ← uncurry_eq, uncurry_curry]
    exact (λ_ X).inv_hom_id

section Braided

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]

/-- In a braided monoidal closed category, tensoring on the right preserves epimorphisms. -/
lemma epi_whiskerRight {A B : C} (f : B ⟶ A) [Epi f] (Z : C) : Epi (f ▷ Z) := by
  have : Epi (Z ◁ f) := (tensorLeft Z).map_epi f
  rw [← Category.comp_id (f ▷ Z), ← Iso.hom_inv_id (β_ A Z),
    BraidedCategory.braiding_naturality_left_assoc]
  infer_instance

/-- In a braided monoidal closed category, precomposition `[A, X] ⟶ [B, X]` with an epimorphism
`B ⟶ A` is a monomorphism. -/
lemma mono_pre_app {A B : C} (f : B ⟶ A) [Epi f] (X : C) : Mono ((pre f).app X) := by
  refine ⟨fun {T} a b h ↦ uncurry_injective ?_⟩
  have := epi_whiskerRight f T
  rw [← cancel_epi (f ▷ T), ← uncurry_pre_app, ← uncurry_pre_app, h]

/-- In a braided monoidal closed category, tensoring on the right preserves colimits, being
isomorphic to tensoring on the left. -/
lemma preservesColimitsOfSize_tensorRight (Z : C) : PreservesColimitsOfSize (tensorRight Z) :=
  have := (ihom.adjunction Z).leftAdjoint_preservesColimits
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight Z)

/-- A preadditive braided monoidal closed category is monoidal preadditive: tensoring on the left
is a left adjoint, hence additive, and tensoring on the right is isomorphic to it. -/
lemma monoidalPreadditive_of_braided [Preadditive C] [HasBinaryBiproducts C] :
    MonoidalPreadditive C := by
  have (X : C) : (tensorLeft X).Additive := by
    have := (ihom.adjunction X).isLeftAdjoint
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft X)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have hr {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z = (β_ X Z).hom ≫ Z ◁ f ≫ (β_ Y Z).inv := by
    rw [← BraidedCategory.braiding_naturality_left_assoc, Iso.hom_inv_id, Category.comp_id]
  have h0 (X Y Z : C) : Z ◁ (0 : X ⟶ Y) = 0 := (tensorLeft Z).map_zero X Y
  have hadd (X Y Z : C) (f g : X ⟶ Y) : Z ◁ (f + g) = Z ◁ f + Z ◁ g :=
    (tensorLeft Z).map_add
  exact
    { whiskerLeft_zero := h0 _ _ _
      zero_whiskerRight := by
        intro X Y Z
        rw [hr, h0, zero_comp, comp_zero]
      whiskerLeft_add := by
        intro X Y Z f g
        exact hadd _ _ _ f g
      add_whiskerRight := by
        intro X Y Z f g
        rw [hr, hr, hr, hadd, Preadditive.add_comp, Preadditive.comp_add] }

end Braided

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C]

/-- Precomposition `[A, X] ⟶ [B, X]` is additive in the morphism `B ⟶ A`. -/
lemma pre_add_app {A B : C} (f g : B ⟶ A) (X : C) :
    (pre (f + g)).app X = (pre f).app X + (pre g).app X :=
  uncurry_injective (by
    rw [uncurry_pre, uncurry_add, uncurry_pre, uncurry_pre,
      MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp])

/-- Precomposition `[A, X] ⟶ [B, X]`, as an additive map in the morphism `B ⟶ A`. -/
@[simps]
def preAppAddHom (A B X : C) : (B ⟶ A) →+ ((ihom A).obj X ⟶ (ihom B).obj X) where
  toFun f := (pre f).app X
  map_zero' := pre_zero_app X
  map_add' f g := pre_add_app f g X

variable [BraidedCategory C]

/-- **The internal hom turns cokernels into kernels**: if `π : P₀ ⟶ P` is a cokernel of
`f : P₁ ⟶ P₀`, then `[π, Q] : [P, Q] ⟶ [P₀, Q]` is a kernel of `[f, Q] : [P₀, Q] ⟶ [P₁, Q]`. -/
noncomputable def isLimitKernelForkPreApp {P₁ P₀ P : C} {f : P₁ ⟶ P₀} {π : P₀ ⟶ P}
    (w : f ≫ π = 0) (hπ : IsColimit (CokernelCofork.ofπ π w)) (Q : C) :
    IsLimit (KernelFork.ofι (f := (pre f).app Q) ((pre π).app Q)
      (by rw [← NatTrans.comp_app, ← pre_map, w, pre_zero_app])) := by
  have hT (T : C) : IsColimit (CokernelCofork.ofπ (f := f ▷ T) (π ▷ T)
      (by rw [← comp_whiskerRight, w, MonoidalPreadditive.zero_whiskerRight])) :=
    have := preservesColimitsOfSize_tensorRight T
    CokernelCofork.mapIsColimit _ hπ (tensorRight T)
  refine KernelFork.IsLimit.ofι _ _
    (fun {T} g hg ↦ curry ((hT T).desc (CokernelCofork.ofπ (uncurry g) ?_))) ?_ ?_
  · rw [← uncurry_pre_app, hg]
    simp [uncurry_eq]
  · intro T g hg
    refine uncurry_injective ?_
    rw [uncurry_pre_app, uncurry_curry]
    exact (hT T).fac _ WalkingParallelPair.one
  · intro T g hg m hm
    rw [eq_curry_iff]
    refine Cofork.IsColimit.hom_ext (hT T) ?_
    simp only [CokernelCofork.π_ofπ]
    rw [← uncurry_pre_app, hm]
    exact ((hT T).fac (CokernelCofork.ofπ (uncurry g) _) WalkingParallelPair.one).symm

end Preadditive

end MonoidalClosed

namespace Functor.LaxMonoidal

open MonoidalClosed

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (F : C ⥤ D) [F.LaxMonoidal]

/-- **A lax monoidal functor with invertible unit map preserves internal homs out of the unit**:
the comparison map `F [𝟙_ C, Q] ⟶ [F (𝟙_ C), F Q]` is an isomorphism, since composed with
`[ε F, F Q]` and evaluation it is `F` applied to the evaluation `[𝟙_ C, Q] ≅ Q`. -/
theorem isIso_ihomComparison_app_unit [IsIso (ε F)] (Q : C) :
    IsIso ((ihomComparison F (𝟙_ C)).app Q) := by
  have h : (ihomComparison F (𝟙_ C)).app Q ≫ (pre (ε F)).app (F.obj Q) ≫
      (λ_ _).inv ≫ (ihom.ev (𝟙_ D)).app (F.obj Q) =
      F.map ((λ_ _).inv ≫ (ihom.ev (𝟙_ C)).app Q) := by
    rw [leftUnitor_inv_naturality_assoc, leftUnitor_inv_naturality_assoc,
      id_tensor_pre_app_comp_ev]
    dsimp only [Functor.comp_obj]
    rw [whisker_exchange_assoc, ihomComparison_ev, F.map_comp,
      ← left_unitality_inv_assoc]
  have := isIso_leftUnitor_inv_comp_ev (F.obj Q)
  have := isIso_leftUnitor_inv_comp_ev Q
  have : IsIso ((ihomComparison F (𝟙_ C)).app Q ≫ (pre (ε F)).app (F.obj Q) ≫
      (λ_ _).inv ≫ (ihom.ev (𝟙_ D)).app (F.obj Q)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((pre (ε F)).app (F.obj Q) ≫
      (λ_ _).inv ≫ (ihom.ev (𝟙_ D)).app (F.obj Q))

/-- The comparison map `F [A, B] ⟶ [F A, F B]` is an isomorphism at `B` if and only if it is one
at any `B'` isomorphic to `B`. -/
lemma isIso_ihomComparison_app_iff_of_iso_right (A : C) {B B' : C} (e : B ≅ B') :
    IsIso ((ihomComparison F A).app B) ↔ IsIso ((ihomComparison F A).app B') :=
  NatTrans.isIso_app_iff_of_iso _ e

/-- The comparison map `F [A, B] ⟶ [F A, F B]` is an isomorphism at `A` if and only if it is one
at any `A'` isomorphic to `A`
(`CategoryTheory.Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app`). -/
lemma isIso_ihomComparison_app_iff_of_iso_left {A A' : C} (e : A ≅ A') (B : C) :
    IsIso ((ihomComparison F A).app B) ↔ IsIso ((ihomComparison F A').app B) := by
  have h := map_pre_app_comp_ihomComparison_app F e.hom B
  constructor
  · intro _
    have : IsIso ((ihomComparison F A').app B ≫ (pre (F.map e.hom)).app (F.obj B)) := by
      rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((pre (F.map e.hom)).app (F.obj B))
  · intro _
    have : IsIso (F.map ((pre e.hom).app B) ≫ (ihomComparison F A).app B) := by
      rw [h]; infer_instance
    exact IsIso.of_isIso_comp_left (F.map ((pre e.hom).app B)) _

section Preadditive

variable [Preadditive C] [Preadditive D] [MonoidalPreadditive C] [MonoidalPreadditive D]

/-- **An additive lax monoidal functor preserves internal homs out of finite biproducts** of
objects out of which it preserves internal homs: an inverse of the comparison map of `⨁ P` is
assembled from the inverses for the summands, `[-, Q]` being additive. -/
theorem isIso_ihomComparison_app_biproduct [F.Additive] {J : Type} [Finite J] (P : J → C)
    [HasBiproduct P] (Q : C) [∀ j, IsIso ((ihomComparison F (P j)).app Q)] :
    IsIso ((ihomComparison F (⨁ P)).app Q) := by
  have := Fintype.ofFinite J
  refine ⟨∑ j, (pre (F.map (biproduct.ι P j))).app (F.obj Q) ≫
    CategoryTheory.inv ((ihomComparison F (P j)).app Q) ≫
      F.map ((pre (biproduct.π P j)).app Q),
    ?_, ?_⟩
  · rw [Preadditive.comp_sum]
    simp_rw [← map_pre_app_comp_ihomComparison_app_assoc, IsIso.hom_inv_id_assoc,
      ← F.map_comp, ← NatTrans.comp_app, ← pre_map]
    rw [← F.map_sum]
    have h := _root_.map_sum (preAppAddHom (⨁ P) (⨁ P) Q)
      (fun j ↦ biproduct.π P j ≫ biproduct.ι P j) Finset.univ
    simp only [preAppAddHom_apply] at h
    rw [← h, biproduct.total, pre_id, NatTrans.id_app, F.map_id]
    rfl
  · rw [Preadditive.sum_comp]
    simp_rw [Category.assoc, map_pre_app_comp_ihomComparison_app, IsIso.inv_hom_id_assoc,
      ← NatTrans.comp_app, ← pre_map, ← F.map_comp]
    have h := _root_.map_sum (preAppAddHom (F.obj (⨁ P)) (F.obj (⨁ P)) (F.obj Q))
      (fun j ↦ F.map (biproduct.π P j ≫ biproduct.ι P j)) Finset.univ
    simp only [preAppAddHom_apply] at h
    rw [← h, ← F.map_sum, biproduct.total, F.map_id, pre_id, NatTrans.id_app]
    rfl

variable [BraidedCategory C] [BraidedCategory D]

/-- **A lax monoidal functor preserves internal homs out of cokernels** of morphisms between
objects out of which it preserves internal homs, provided it preserves the kernel of
`[P₀, Q] ⟶ [P₁, Q]` and maps the projection onto the cokernel to an epimorphism: the
comparison map is then a morphism between two kernels of isomorphic morphisms. -/
theorem isIso_ihomComparison_app_of_isColimit [F.PreservesZeroMorphisms] {P₁ P₀ P : C}
    {f : P₁ ⟶ P₀} {π : P₀ ⟶ P} (w : f ≫ π = 0) (hπ : IsColimit (CokernelCofork.ofπ π w))
    (Q : C) [PreservesLimit (parallelPair ((pre f).app Q) 0) F] [Epi (F.map π)]
    [IsIso ((ihomComparison F P₀).app Q)]
    [IsIso ((ihomComparison F P₁).app Q)] :
    IsIso ((ihomComparison F P).app Q) := by
  have ht : IsLimit (KernelFork.ofι (f := F.map ((pre f).app Q)) (F.map ((pre π).app Q))
      (by rw [← F.map_comp, ← NatTrans.comp_app, ← pre_map, w, pre_zero_app, F.map_zero])) :=
    KernelFork.mapIsLimit _ (isLimitKernelForkPreApp w hπ Q) F
  have := mono_pre_app (F.map π) (F.obj Q)
  have h₀ := map_pre_app_comp_ihomComparison_app F π Q
  have h₁ : CategoryTheory.inv ((ihomComparison F P₀).app Q) ≫
      F.map ((pre f).app Q) = (pre (F.map f)).app (F.obj Q) ≫
        CategoryTheory.inv ((ihomComparison F P₁).app Q) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv,
      map_pre_app_comp_ihomComparison_app]
  obtain ⟨d, hd⟩ := KernelFork.IsLimit.lift' ht
    ((pre (F.map π)).app (F.obj Q) ≫
      CategoryTheory.inv ((ihomComparison F P₀).app Q)) (by
      rw [Category.assoc, h₁, ← Category.assoc, ← NatTrans.comp_app,
        ← pre_map, ← F.map_comp, w, F.map_zero, pre_zero_app, zero_comp])
  simp only [Fork.ι_ofι] at hd
  refine ⟨d, ?_, ?_⟩
  · refine Fork.IsLimit.hom_ext ht ?_
    simp only [Fork.ι_ofι, Category.assoc, hd, Category.id_comp]
    rw [← Category.assoc, ← h₀, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · rw [← cancel_mono ((pre (F.map π)).app (F.obj Q)), Category.assoc, ← h₀,
      ← Category.assoc, hd, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      Category.id_comp]

end Preadditive

end Functor.LaxMonoidal

end CategoryTheory
