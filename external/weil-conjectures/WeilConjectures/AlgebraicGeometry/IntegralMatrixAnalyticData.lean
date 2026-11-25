/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import Mathlib.Data.Matrix.Basic

/-! # Continuous functions for integral matrix charts

The analytic part of the pivot argument supplies a dominating, nowhere zero entry.
The module-object block decomposition is constructed separately.
-/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The continuous coefficient of an integral regular-module endomorphism.
Source: the canonical coefficient realization, evaluated on the global unit.
(auxiliary; not a blueprint node) -/
noncomputable def integralRegularCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u})
    (p : Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
      Mod.regular (condensedRingObj (integralCoeff ℓ E) X)) :
    C(X, continuousIntegers ℓ E) :=
  let e := chartComparison X (continuousIntegers ℓ E)
  (((inv e ≫ p.hom ≫ e).hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down

/-- Evaluate the regular-module coefficients of a finite free map at the unit section,
after a supplied continuous-function realization of the coefficient ring.
Source: Bhatt--Scholze, Section 6.8, continuous coefficient realization.
(auxiliary; not a blueprint node) -/
noncomputable def integralMatrixFunctions (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u})
    (e : condensedRingObj (integralCoeff ℓ E) X ⟶
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X (continuousIntegers ℓ E))) [IsIso e]
    {n t : ℕ}
    (f : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t) :
    Matrix (Fin t) (Fin n) C(X, continuousIntegers ℓ E) := fun i j ↦
  let p := biproduct.ι _ j ≫ f ≫ biproduct.π _ i
  (((inv e ≫ p.hom ≫ e).hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down

/-- The inclusion of continuous integral functions into continuous field-valued functions.
Source: the continuous coefficient inclusion O_E to E.
(auxiliary; not a blueprint node) -/
noncomputable def integralFunctionInclusion (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap X (continuousIntegers ℓ E).subtype continuous_subtype_val)

instance (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) :
    IsMonHom (integralFunctionInclusion ℓ E X) := by
  dsimp [integralFunctionInclusion]
  infer_instance

/-- The regular-module isomorphism after normalized integral coefficient pullback.
Source: the monoidal inverse image and the coefficient pullback comparison.
(auxiliary; not a blueprint node) -/
@[irreducible] noncomputable def integralRegularPullbackIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    let R := condensedRingObj (integralCoeff ℓ E) X
    let T := (ProEtale.upperStar Ab.{u + 1} f).mapMod R ⋙
      Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) f))
    T.obj (Mod.regular R) ≅
      Mod.regular (condensedRingObj (integralCoeff ℓ E) Y) := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let P := (ProEtale.upperStar Ab.{u + 1} f).mapMod R
  let α := condensedPullbackHom (integralCoeff ℓ E) f
  let Q := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (inv α)
  let e₀ : P.obj (Mod.regular R) ≅
      Mod.regular ((ProEtale.upperStar Ab.{u + 1} f).obj R) :=
    Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  exact Q.mapIso e₀ ≪≫ Mod.regularIsoOfIsIso α

/-- The actual standard basis after normalized integral coefficient pullback.
Source: preservation of finite biproducts and the coefficient pullback isomorphism.
(auxiliary; not a blueprint node) -/
noncomputable def integralFiniteFreePullbackIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) :
    let R := condensedRingObj (integralCoeff ℓ E) X
    let T := (ProEtale.upperStar Ab.{u + 1} f).mapMod R ⋙
      Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) f))
    T.obj (Mod.finiteFree R n) ≅
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) Y) n := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let P := (ProEtale.upperStar Ab.{u + 1} f).mapMod R
  let α := condensedPullbackHom (integralCoeff ℓ E) f
  let Q := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (inv α)
  let T := P ⋙ Q
  let e₀ : P.obj (Mod.regular R) ≅
      Mod.regular ((ProEtale.upperStar Ab.{u + 1} f).obj R) :=
    Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  let e₁ : T.obj (Mod.regular R) ≅
      Mod.regular (condensedRingObj (integralCoeff ℓ E) Y) :=
    Q.mapIso e₀ ≪≫ Mod.regularIsoOfIsIso α
  exact T.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ e₁)

/-- Normalized pullback of the integral coefficient module category.
Source: preservation of module objects and the coefficient pullback comparison.
(auxiliary; not a blueprint node) -/
noncomputable abbrev integralMatrixPullback (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (g : Y ⟶ X) :=
  (ProEtale.upperStar Ab.{u + 1} g).mapMod (condensedRingObj (integralCoeff ℓ E) X) ⋙
    Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) g))

/-- The pulled-back matrix in the canonical finite-free bases.
Source: preservation of finite biproducts by normalized coefficient pullback.
(auxiliary; not a blueprint node) -/
noncomputable abbrev integralMatrixPullbackMap (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (g : Y ⟶ X) {n t : ℕ}
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t) :=
  (integralFiniteFreePullbackIso ℓ E g n).inv ≫
    (integralMatrixPullback ℓ E g).map a ≫ (integralFiniteFreePullbackIso ℓ E g t).hom

/-- The continuous coefficients of the canonical pulled-back matrix.
Source: continuous coefficient realization evaluated on the unit section.
(auxiliary; not a blueprint node) -/
@[irreducible] noncomputable def integralMatrixPullbackFunctions (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (g : Y ⟶ X) {n t : ℕ}
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t) :
    Matrix (Fin t) (Fin n) C(Y, continuousIntegers ℓ E) :=
  integralMatrixFunctions ℓ E Y (chartComparison Y (continuousIntegers ℓ E))
    (integralMatrixPullbackMap ℓ E g a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The sectionwise continuous-function map to scheme direct image.
Source: precomposition with the first projection of a scheme pullback.
(auxiliary; not a blueprint node) -/
@[irreducible] noncomputable def continuousFunctionPushforward {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type) [TopologicalSpace O] [Ring O] [IsTopologicalRing O] :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousMapRingSheaf X O) ⟶
    (ProEtale.lowerStar Ab.{u + 1} f).obj
      ((sheafCompose (Scheme.ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf Y O)) :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun s ↦ ULift.up
            (s.down.comp (pullback.fst U.unop.hom f).base.hom)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro U V g
       apply ConcreteCategory.hom_ext
       intro s
       apply ULift.ext
       change (s.down.comp g.unop.left.base.hom).comp
         (pullback.fst V.unop.hom f).base.hom =
           (s.down.comp (pullback.fst U.unop.hom f).base.hom).comp
             ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop).left.base.hom
       have h : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop).left ≫
           pullback.fst U.unop.hom f = pullback.fst V.unop.hom f ≫ g.unop.left := by
         exact pullback.lift_fst _ _ _
       ext x
       exact congrArg (fun h : pullback V.unop.hom f ⟶ U.unop.left ↦ s.down (h x)) h.symm }⟩

/-- Sections of continuous direct image are precomposed with the pullback projection.
Source: the defining section formula for continuousFunctionPushforward.
(auxiliary; not a blueprint node) -/
theorem continuousFunctionPushforward_app {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type) [TopologicalSpace O] [Ring O] [IsTopologicalRing O]
    (U : X.ProEt) (s : ULift.{u + 1} C(U.left, O)) :
    ((continuousFunctionPushforward f O).hom.app (op U)) s =
      ULift.up (s.down.comp (pullback.fst U.hom f).base.hom) := by
  unfold continuousFunctionPushforward
  rfl

/-- The sectionwise continuous direct image preserves the unit section.
Source: the defining section formula for continuousFunctionPushforward.
(auxiliary; not a blueprint node) -/
theorem continuousFunctionPushforward_app_one {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type) [TopologicalSpace O] [Ring O] [IsTopologicalRing O] (U : X.ProEt) :
    ((continuousFunctionPushforward f O).hom.app (op U)) (ULift.up 1) =
      ULift.up 1 := by
  rw [continuousFunctionPushforward_app]
  rfl


end AlgebraicGeometry.ProEtale.CondensedRing
