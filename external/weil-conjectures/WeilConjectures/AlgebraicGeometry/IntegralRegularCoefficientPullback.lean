/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData

import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality

/-! # The geometric input to analytic integral matrix charts -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

universe u₁ v₁ u₂ v₂

private theorem regular_map_hom_generic {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (R : C) [MonObj R]
    {S : D} [MonObj S] (α : F.obj R ⟶ S) [IsMonHom α] [IsIso α]
    (p : Mod.regular R ⟶ Mod.regular R) :
    let P := F.mapMod R
    let Q := Mod.comap (D := D) (inv α)
    let e₀ : P.obj (Mod.regular R) ≅ Mod.regular (F.obj R) :=
      Mod.isoMk (Iso.refl _) (by simp [Mod.act])
    let e := Q.mapIso e₀ ≪≫ Mod.regularIsoOfIsIso α
    (e.inv ≫ (P ⋙ Q).map p ≫ e.hom).hom = inv α ≫ F.map p.hom ≫ α := by
  dsimp only
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
    Functor.mapIso_hom]
  change (inv α ≫ 𝟙 _) ≫ F.map p.hom ≫ (𝟙 _ ≫ α) = _
  simp

private theorem regular_pullback_hom (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (p : Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
      Mod.regular (condensedRingObj (integralCoeff ℓ E) X)) :
    ((integralRegularPullbackIso ℓ E f).inv ≫
      (integralMatrixPullback ℓ E f).map p ≫
        (integralRegularPullbackIso ℓ E f).hom).hom =
      inv (condensedPullbackHom (integralCoeff ℓ E) f) ≫
        (ProEtale.upperStar Ab.{u + 1} f).map p.hom ≫
          condensedPullbackHom (integralCoeff ℓ E) f := by
  unfold integralRegularPullbackIso
  exact regular_map_hom_generic (ProEtale.upperStar Ab.{u + 1} f)
    (condensedRingObj (integralCoeff ℓ E) X)
    (condensedPullbackHom (integralCoeff ℓ E) f) p

attribute [local irreducible] condensedPushforwardHom

private theorem regular_pullback_naturality (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (p : Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
      Mod.regular (condensedRingObj (integralCoeff ℓ E) X)) :
    p.hom ≫ condensedPushforwardHom (integralCoeff ℓ E) f =
      condensedPushforwardHom (integralCoeff ℓ E) f ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          ((integralRegularPullbackIso ℓ E f).inv ≫
            (integralMatrixPullback ℓ E f).map p ≫
              (integralRegularPullbackIso ℓ E f).hom).hom := by
  rw [regular_pullback_hom, ← unitAlgHom_comp_map_condensedPullbackHom]
  let α := condensedPullbackHom (integralCoeff ℓ E) f
  let adj := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f
  change p.hom ≫ (adj.unit.app _ ≫ (ProEtale.lowerStar Ab.{u + 1} f).map α) =
    (adj.unit.app _ ≫ (ProEtale.lowerStar Ab.{u + 1} f).map α) ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map
        (inv α ≫ (ProEtale.upperStar Ab.{u + 1} f).map p.hom ≫ α)
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [Mod.regular, CategoryTheory.Functor.id_map, CategoryTheory.Functor.id_obj,
    CategoryTheory.Functor.comp_map,
    Category.assoc] using congrArg (fun h ↦ h ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map α) (adj.unit.naturality p.hom)

theorem conjugated_morphism_square
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (G : C ⥤ D) {A B : C} {R S : D}
    (eX : R ⟶ S) [IsIso eX] (eY : A ⟶ B) [IsIso eY]
    (ηf : R ⟶ G.obj A) (δ : S ⟶ G.obj B) (p : R ⟶ R) (q : A ⟶ A)
    (hs : ηf ≫ G.map eY = eX ≫ δ) (hp : p ≫ ηf = ηf ≫ G.map q) :
    δ ≫ G.map (inv eY ≫ q ≫ eY) = (inv eX ≫ p ≫ eX) ≫ δ := by
  apply (cancel_epi eX).1
  simp only [Functor.map_comp]
  calc
    eX ≫ δ ≫ (G.map (inv eY) ≫ G.map q ≫ G.map eY) =
        (ηf ≫ G.map eY) ≫ G.map (inv eY) ≫ G.map q ≫ G.map eY := by
      rw [hs]
      simp only [Category.assoc]
    _ = ηf ≫ G.map q ≫ G.map eY := by
      simp only [Category.assoc, ← Functor.map_comp_assoc, IsIso.hom_inv_id_assoc]
    _ = (p ≫ ηf) ≫ G.map eY := by rw [hp, Category.assoc]
    _ = eX ≫ (inv eX ≫ p ≫ eX) ≫ δ := by
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      rw [← hs]

theorem continuous_function_unit_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type) [TopologicalSpace O] [Ring O] [IsTopologicalRing O]
    (p : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X O) ⟶
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X O))
    (q : (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf Y O) ⟶
      (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf Y O))
    (h : continuousFunctionPushforward f O ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map q = p ≫ continuousFunctionPushforward f O)
    (y : Y) :
    ((q.hom.app (op (Scheme.ProEt.mk (𝟙 Y)))) (ULift.up 1)).down y =
      ((p.hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down (f y) := by
  let V : Y.ProEt := Scheme.ProEt.mk (pullback.snd (𝟙 X) f)
  let v : V ⟶ Scheme.ProEt.mk (𝟙 Y) := MorphismProperty.Over.homMk V.hom
  let w : Y ⟶ pullback (𝟙 X) f := pullback.lift f (𝟙 Y) (by simp)
  let z := w y
  have hs := congrArg (fun k ↦ ((k.hom.app (op (Scheme.ProEt.mk (𝟙 X))))
    (ULift.up 1)).down z) h
  have hn := congrArg (fun k : AddCommGrpCat.of (ULift.{u + 1} C(Y, O)) ⟶
      AddCommGrpCat.of (ULift.{u + 1} C(V.left, O)) ↦ (k (ULift.up 1)).down z)
    (q.hom.naturality v.op)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ProEtale.lowerStar_map_hom_app, AddCommGrpCat.comp_apply,
    continuousFunctionPushforward_app,
    ContinuousMap.comp_apply] at hs
  change ((q.hom.app (op V)) (ULift.up 1)).down z =
    ((p.hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down
      (pullback.fst (𝟙 X) f z) at hs
  change ((q.hom.app (op V)) (ULift.up 1)).down z =
    ((q.hom.app (op (Scheme.ProEt.mk (𝟙 Y)))) (ULift.up 1)).down (V.hom z) at hn
  have hw₁ : w ≫ pullback.fst (𝟙 X) f = f := pullback.lift_fst _ _ _
  have hw₂ : w ≫ V.hom = 𝟙 Y := pullback.lift_snd _ _ _
  have hz₁ : pullback.fst (𝟙 X) f z = f y :=
    congrArg (fun h : Y ⟶ X ↦ h y) hw₁
  have hz₂ : V.hom z = y := congrArg (fun h : Y ⟶ Y ↦ h y) hw₂
  rw [hz₁] at hs
  rw [hz₂] at hn
  exact hn.symm.trans hs

private theorem coefficient_conjugation_naturality (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (p : Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
      Mod.regular (condensedRingObj (integralCoeff ℓ E) X))
    (q : Mod.regular (condensedRingObj (integralCoeff ℓ E) Y) ⟶
      Mod.regular (condensedRingObj (integralCoeff ℓ E) Y))
    (hp : p.hom ≫ condensedPushforwardHom (integralCoeff ℓ E) f =
      condensedPushforwardHom (integralCoeff ℓ E) f ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map q.hom) (y : Y) :
    integralRegularCoefficient ℓ E Y q y = integralRegularCoefficient ℓ E X p (f y) := by
  apply continuous_function_unit_naturality f (continuousIntegers ℓ E)
  exact conjugated_morphism_square (ProEtale.lowerStar Ab.{u + 1} f)
    (chartComparison X (continuousIntegers ℓ E))
    (chartComparison Y (continuousIntegers ℓ E))
    (condensedPushforwardHom (integralCoeff ℓ E) f)
    (continuousFunctionPushforward f (continuousIntegers ℓ E)) _ _
    (continuousChart_scheme_naturality f (continuousIntegers ℓ E)) hp

/-- Continuous regular coefficients commute with the specified coefficient pullback.

Source: Bhatt--Scholze, Section 6.8, continuous coefficient realization, and its
canonical inverse-image comparison.
(auxiliary; not a blueprint node)

Proof: the underlying regular-module pullback is conjugation of the inverse image
of p by the coefficient pullback isomorphism. Naturality of the inverse-image
adjunction unit consequently commutes p with the canonical coefficient direct-image
map. The continuous chart's scheme naturality square transports this equality to
an equality of conjugated continuous-sheaf endomorphisms. Evaluate that square at
the global unit section over X. Its pullback is the unit section over the pullback
of the final site object. Naturality of the endomorphism on Y identifies its unit
value there with restriction of its global unit value. Finally evaluate at the
canonical section Y→X×_X Y: its two projections give f(y) and y. This is exactly
the asserted identity. No rational cokernel or matrix hypothesis is involved. -/
theorem integralRegularCoefficient_pullback (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (p : Mod.regular (condensedRingObj (integralCoeff ℓ E) X) ⟶
      Mod.regular (condensedRingObj (integralCoeff ℓ E) X)) (y : Y) :
    integralRegularCoefficient ℓ E Y
      ((integralRegularPullbackIso ℓ E f).inv ≫
        (integralMatrixPullback ℓ E f).map p ≫
          (integralRegularPullbackIso ℓ E f).hom) y =
      integralRegularCoefficient ℓ E X p (f y) := by
  exact coefficient_conjugation_naturality ℓ E f p _
    (regular_pullback_naturality ℓ E f p) y

end AlgebraicGeometry.ProEtale.CondensedRing
