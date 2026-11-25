/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverNaturality
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawPullbackComposition

/-! # The raw cohomology diagram

Source: Stacks Project, Tag 09Z1, the canonical cohomology comparison maps.
(blueprint: lem-sbc-higher-image-raw-pullback-functorial).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private theorem five_factor_add
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} {P Q R T : D}
    (a : P ⟶ Q) (b : Q ⟶ F.obj X) (c : F.obj Y ⟶ R) (d : R ⟶ T)
    (x y : X ⟶ Y) :
    (a ≫ b) ≫ F.map (x + y) ≫ c ≫ d =
      ((a ≫ b) ≫ F.map x ≫ c ≫ d) + ((a ≫ b) ≫ F.map y ≫ c ≫ d) := by
  simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

private theorem five_factor_zero
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} {P Q R T : D}
    (a : P ⟶ Q) (b : Q ⟶ F.obj X) (c : F.obj Y ⟶ R) (d : R ⟶ T) :
    (a ≫ b) ≫ F.map (0 : X ⟶ Y) ≫ c ≫ d = 0 := by
  simp only [Functor.map_zero, Limits.comp_zero, Limits.zero_comp]


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- Expanding canonical derived inverse-image comparisons requires substantial reduction.
/-- The explicit raw pullbacks satisfy identity and composition, independently of any
limit, affineness, or quasi-compactness assumption.
Source: Stacks Project, Tag 09Z1, canonical comparison maps in lemma-relative-colimit.
(blueprint: lem-sbc-higher-image-raw-pullback-functorial).

Proof: The derived inverse-image functor is additive, and composition with fixed
morphisms is additive in each argument. Thus the five-factor formula preserves zero
and addition. Expand the five factors defining raw pullback. For an identity morphism, the
identity comparison for inverse image cancels the single-functor comparison and its
inverse. Naturality of the shift comparison cancels its identity factors, leaving the
original derived morphism. For composable arrows, functoriality of derived inverse image
moves the five factors of the first pullback through those of the second. Naturality of
the single-functor comparison cancels the adjacent inverse and direct comparisons.
The associativity coherence of inverse-image composition identifies the resulting
source comparison with that for the composite. Its coefficient comparison is identified
in the same way, using the two equations defining morphisms in Over W. Compatibility of
derived inverse image with shifts identifies the remaining shift comparison. Thus the
five surviving factors are exactly those of the composite raw pullback. -/
theorem higherDirectImageRawOverPullback_functorial
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale) :
    (∀ (A B : Over W) (f : A ⟶ B),
      higherDirectImageRawOverPullback Λ k G q f U 0 = 0) ∧
    (∀ (A B : Over W) (f : A ⟶ B)
      (x y : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)),
      higherDirectImageRawOverPullback Λ k G q f U (x + y) =
        higherDirectImageRawOverPullback Λ k G q f U x +
          higherDirectImageRawOverPullback Λ k G q f U y) ∧
    (∀ (A : Over W)
      (z : (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U)),
      higherDirectImageRawOverPullback Λ k G q (𝟙 A) U z = z) ∧
    (∀ (A B C : Over W) (f : A ⟶ B) (g : B ⟶ C)
      (z : (higherDirectImageRawOverPresheaf Λ k G q C).obj (op U)),
      higherDirectImageRawOverPullback Λ k G q (f ≫ g) U z =
        higherDirectImageRawOverPullback Λ k G q f U
          (higherDirectImageRawOverPullback Λ k G q g U z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B f
    simp only [higherDirectImageRawOverPullback,
      higherDirectImageRawTrianglePullback, rawTriangleMap,
      Functor.map_zero, Limits.comp_zero, Limits.zero_comp]
  · intro A B f x y
    change (DerivedCategory.Plus.singleFunctor
      (Sheaf B.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
        (((B.hom ≫ k)^*[ModuleCat.{u + 1} Λ]).obj ((freeSheaf Λ S).obj U)) ⟶
      (higherDirectImageRawOverComplex Λ G B)⟦q⟧ at x y
    unfold higherDirectImageRawOverPullback higherDirectImageRawTrianglePullback rawTriangleMap
    rw [Functor.map_add]
    simp only [Preadditive.comp_add, Preadditive.add_comp]
  · intro A z
    exact higherDirectImageRawOverPullback_id Λ k G q A U z
  · intro A B C f g z
    exact higherDirectImageRawOverPullback_comp Λ k G q f g U z

/-- The additive map on raw cohomology; its data are the explicit five-factor formula. 
(blueprint: def-sbc-higher-image-raw-diagram)
-/
noncomputable def higherDirectImageRawOverPullbackHom
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale) :
    (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U) ⟶
      (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U) :=
  ConcreteCategory.ofHom (C := AddCommGrpCat)
    { toFun := higherDirectImageRawOverPullback Λ k G q f U
      map_zero' := (higherDirectImageRawOverPullback_functorial Λ k G q U).1 A B f
      map_add' := (higherDirectImageRawOverPullback_functorial Λ k G q U).2.1 A B f }

/-- The bundled additive map is exactly the prescribed raw pullback. 
(blueprint: def-sbc-higher-image-raw-diagram)
-/
theorem higherDirectImageRawOverPullbackHom_apply
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    higherDirectImageRawOverPullbackHom Λ k G q f U z =
      higherDirectImageRawOverPullback Λ k G q f U z := rfl

/-- The contravariant raw cohomology functor on Over W. No data are chosen from an
existence theorem: objects and maps are the fixed raw presheaves and explicit pullbacks. 
(blueprint: def-sbc-higher-image-raw-diagram)
-/
noncomputable def higherDirectImageRawOverFunctor
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale) :
    (Over W)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj A := (higherDirectImageRawOverPresheaf Λ k G q A.unop).obj (op U)
  map f := higherDirectImageRawOverPullbackHom Λ k G q f.unop U
  map_id A := by
    apply AddCommGrpCat.ext
    intro z
    change higherDirectImageRawOverPullbackHom Λ k G q (𝟙 A.unop) U z = z
    rw [higherDirectImageRawOverPullbackHom_apply]
    exact (higherDirectImageRawOverPullback_functorial Λ k G q U).2.2.1 A.unop z
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro z
    change higherDirectImageRawOverPullbackHom Λ k G q (g.unop ≫ f.unop) U z =
      higherDirectImageRawOverPullbackHom Λ k G q g.unop U
        (higherDirectImageRawOverPullbackHom Λ k G q f.unop U z)
    simp only [higherDirectImageRawOverPullbackHom_apply]
    exact (higherDirectImageRawOverPullback_functorial Λ k G q U).2.2.2
      _ _ _ g.unop f.unop z

/-- The raw cohomology diagram of an inverse system. 
(blueprint: def-sbc-higher-image-raw-diagram)
-/
noncomputable abbrev higherDirectImageRawDiagram
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (U : S.Etale) :=
  D.op ⋙ higherDirectImageRawOverFunctor Λ k G q U

/-- The raw cohomology cocone of a scheme cone, before any assertion of continuity. 
(blueprint: def-sbc-higher-image-raw-diagram)
-/
noncomputable def higherDirectImageRawCocone
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (c : Cone D) (U : S.Etale) :
    Cocone (higherDirectImageRawDiagram Λ k G q D U) :=
  (higherDirectImageRawOverFunctor Λ k G q U).mapCocone c.op

end AlgebraicGeometry.Etale
