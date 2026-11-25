/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit

/-!
# Base change of the Kummer boundary

The Kummer boundary `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` of a global function `f` is compatible with
pullback: for `e : U' ⟶ U`, the restriction of `∂κ(f)` to `U'`, through the restriction of
supports `Le^* Ri_! Ri^! ⟶ Ri'_! Ri'^! Le^*` (`AlgebraicGeometry.Etale.supportedRestriction`),
is `∂κ(e^* f)`. This is the naturality of the Kummer class
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_kummerClass`) combined with the base change of
the supported localization triangle
(`AlgebraicGeometry.Etale.supportedLocalizationBoundary_baseChange`).

We also read classes with supports as morphisms `Λ_Z ⟶ Ri^! L` and restrict these morphisms
along base changes (`AlgebraicGeometry.Etale.restrictSupportedHom`). Precomposition with
endomorphisms of the constant complexes, pulled back along the maps of schemes
(`AlgebraicGeometry.Etale.constantComplexEndPullback`), is compatible with this restriction.

## Main definitions

- `AlgebraicGeometry.Etale.constantComplexEndPullback`
- `AlgebraicGeometry.Etale.restrictSupportedHom`

## Main statements

- `AlgebraicGeometry.Etale.kummerBoundary_baseChange`
- `AlgebraicGeometry.Etale.restrictSupportedHom_constantComplexEndPullback_comp`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The exponent of `Λ` stays invertible on an open subscheme. -/
theorem _root_.AlgebraicGeometry.HasInvertibleExponent.opens {Λ : Type (u + 1)} [CommRing Λ]
    {X : Scheme.{u}} [HasInvertibleExponent Λ X] (V : X.Opens) : HasInvertibleExponent Λ V :=
  .of_hom V.ι

attribute [local instance] HasInvertibleExponent.opens

section Twist

variable {Λ : Type (u + 1)} [CommRing Λ] [HasTateTwist Λ]

/-- The pullback identifications of the twisting objects are compatible with composition, for
a composite given up to an equality. -/
lemma leftDerivedUpperStarTateObjectIso_comp {X Y S : Scheme.{u}} [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ S] (f : X ⟶ Y) (g : Y ⟶ S)
    (fg : X ⟶ S) (h : fg = f ≫ g) (m : ℤ) :
    leftDerivedUpperStarTateObjectIso fg m =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g fg h).app (tateObject Λ S m) ≪≫
        (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTateObjectIso g m) ≪≫
          leftDerivedUpperStarTateObjectIso f m := by
  subst h
  exact HasTateTwist.leftDerivedUpperStarTwistObjectIso_comp f g m

omit [HasTateTwist Λ] in
variable (Λ) in
/-- The pullback identifications of the constant complexes are compatible with composition: this
is the compatibility of the composition isomorphism of the derived pullbacks with their counits
(`AlgebraicGeometry.Etale.leftDerivedUpperStarComp_hom_app_unit`). -/
lemma leftDerivedUpperStarConstantComplexIso_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (fg : X ⟶ S) (h : fg = f ≫ g) :
    leftDerivedUpperStarConstantComplexIso Λ fg =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g fg h).app (constantComplex Λ S) ≪≫
        (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarConstantComplexIso Λ g) ≪≫
          leftDerivedUpperStarConstantComplexIso Λ f := by
  ext
  exact (leftDerivedUpperStarComp_hom_app_unit (ModuleCat.{u + 1} Λ) f g fg h).symm

variable {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The derived square isomorphism of a commutative square `g' ≫ f = f' ≫ g` is compatible with
the pullback identifications of the twisting objects:

```
Lf'^* Lg^* Λ_Y(m) ──≅──▶ Lg'^* Lf^* Λ_Y(m) ──Lg'^* ≅──▶ Lg'^* Λ_X(m)
        │                                                 │
Lf'^* ≅ │                                                 │ ≅
        ▼                                                 ▼
  Lf'^* Λ_{Y'}(m) ──────────────────≅─────────────────▶ Λ_{X'}(m)
```
-/
lemma derivedSquareUpperStarIso_hom_app_tateObject [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ X'] [HasInvertibleExponent Λ Y']
    (sq : CommSq g' f' f g) (m : ℤ) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app (tateObject Λ Y m) ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateObjectIso f m).hom ≫
          (leftDerivedUpperStarTateObjectIso g' m).hom =
      (L((f')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateObjectIso g m).hom ≫
        (leftDerivedUpperStarTateObjectIso f' m).hom := by
  have h₁ := leftDerivedUpperStarTateObjectIso_comp (Λ := Λ) g' f (g' ≫ f) rfl m
  have h₂ := leftDerivedUpperStarTateObjectIso_comp (Λ := Λ) f' g (g' ≫ f) sq.w m
  rw [h₁] at h₂
  have h₃ := congrArg Iso.hom h₂
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h₃
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, h₃, Iso.inv_hom_id_app_assoc]

omit [HasTateTwist Λ] in
variable (Λ) in
/-- The derived square isomorphism of a commutative square `g' ≫ f = f' ≫ g` is compatible with
the pullback identifications of the constant complexes. -/
lemma derivedSquareUpperStarIso_hom_app_constantComplex (sq : CommSq g' f' f g) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app (constantComplex Λ Y) ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
          (leftDerivedUpperStarConstantComplexIso Λ g').hom =
      (L((f')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ g).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ f').hom := by
  have h₁ := leftDerivedUpperStarConstantComplexIso_comp Λ g' f (g' ≫ f) rfl
  have h₂ := leftDerivedUpperStarConstantComplexIso_comp Λ f' g (g' ≫ f) sq.w
  rw [h₁] at h₂
  have h₃ := congrArg Iso.hom h₂
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h₃
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, h₃, Iso.inv_hom_id_app_assoc]

omit [HasTateTwist Λ] in
variable (Λ) in
/-- The constant-complex form of `derivedSquareUpperStarIso_hom_app_constantComplex`, solved
for the identification along `f'`. -/
lemma leftDerivedUpperStarConstantComplexIso_square (sq : CommSq g' f' f g) :
    (L((f')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ g).inv ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app (constantComplex Λ Y) ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
          (leftDerivedUpperStarConstantComplexIso Λ g').hom =
      (leftDerivedUpperStarConstantComplexIso Λ f').hom := by
  rw [derivedSquareUpperStarIso_hom_app_constantComplex, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The twist form of `derivedSquareUpperStarIso_hom_app_tateObject`, solved for the inverse
identification along `f'`. -/
lemma leftDerivedUpperStarTateObjectIso_square [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ X'] [HasInvertibleExponent Λ Y']
    (sq : CommSq g' f' f g) (m : ℤ) :
    (leftDerivedUpperStarTateObjectIso g' m).inv ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateObjectIso f m).inv ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).inv.app (tateObject Λ Y m) ≫
          (L((f')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarTateObjectIso g m).hom =
      (leftDerivedUpperStarTateObjectIso f' m).inv := by
  have h := derivedSquareUpperStarIso_hom_app_tateObject (Λ := Λ) sq m
  rw [← cancel_mono (leftDerivedUpperStarTateObjectIso f' m).hom, Iso.inv_hom_id,
    Category.assoc, Category.assoc, Category.assoc, ← h, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id]

end Twist

private lemma kummerBoundary_comp_baseChange
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {K X Y : C} {K' X' Y' : D}
    (σ : K' ⟶ F.obj K) (a : K ⟶ X⟦(1 : ℤ)⟧) (a' : K' ⟶ X'⟦(1 : ℤ)⟧)
    (δ : X ⟶ Y⟦(1 : ℤ)⟧) (δ' : X' ⟶ Y'⟦(1 : ℤ)⟧)
    (b : F.obj X ⟶ X') (ψ : F.obj Y ⟶ Y')
    (γ : K ⟶ Y⟦(2 : ℤ)⟧) (γ' : K' ⟶ Y'⟦(2 : ℤ)⟧)
    (hγ : γ = a ≫ (δ⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C (1 : ℤ) 1 2 rfl).inv.app Y))
    (hγ' : γ' = a' ≫ (δ'⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' D (1 : ℤ) 1 2 rfl).inv.app Y'))
    (hδ : F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app Y ≫ ψ⟦(1 : ℤ)⟧' = b ≫ δ')
    (ha : σ ≫ F.map a ≫ (F.commShiftIso (1 : ℤ)).hom.app X ≫ b⟦(1 : ℤ)⟧' = a') :
    σ ≫ F.map γ ≫ (F.commShiftIso (2 : ℤ)).hom.app Y ≫ ψ⟦(2 : ℤ)⟧' = γ' := by
  rw [hγ, hγ', F.map_comp, Category.assoc,
    Functor.map_shift_comp_shiftFunctorAdd'_inv, hδ,
    (shiftFunctor D (1 : ℤ)).map_comp, Category.assoc, reassoc_of% ha]

section Kummer

variable (Λ : Type (u + 1)) [CommRing Λ] [HasKummerClass Λ]

variable {U U' D D' : Scheme.{u}} {e₁ : D' ⟶ D} {j' : D' ⟶ U'} {j : D ⟶ U} {e : U' ⟶ U}

/-- The Kummer class `κ(u)` on `D ⊆ U`, read on `U` through `Lj^* Λ_U ≅ Λ_D` and
`Lj^* Λ_U(1) ≅ Λ_D(1)`, is compatible with a commutative square `e₁ ≫ j = j' ≫ e`: its pullback
along `e₁`, read through the derived square isomorphism, is the Kummer class of the pulled back
unit on `D'`:

```
Lj'^* Λ_{U'} ──≅──▶ Le₁^* Lj^* Λ_U ──Le₁^*(κ(u) read on U)──▶ Le₁^* ((Lj^* Λ_U(1))[1])
     │                                                                  │
   ≅ │                                                                  │ ≅
     ▼                                                                  ▼
   Λ_{D'} ──κ(u')──▶ Λ_{D'}(1)[1] ──────────≅──────────▶ (Lj'^* Λ_{U'}(1))[1]
```
-/
lemma kummerClass_square [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ U']
    [HasInvertibleExponent Λ D] [HasInvertibleExponent Λ D'] (sq : CommSq e₁ j' j e)
    (u : Γ(D, ⊤)ˣ) (u' : Γ(D', ⊤)ˣ)
    (hu : Units.map e₁.appTop.hom.toMonoidHom u = u') :
    (L((j')^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app (constantComplex Λ U) ≫
        (L((e₁)^*[ModuleCat.{u + 1} Λ])).map
          ((leftDerivedUpperStarConstantComplexIso Λ j).hom ≫ kummerClass Λ u ≫
            (leftDerivedUpperStarTateObjectIso j 1).inv⟦(1 : ℤ)⟧') ≫
        ((L((e₁)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _ ≫
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).inv.app (tateObject Λ U 1) ≫
          (L((j')^*[ModuleCat.{u + 1} Λ])).map
            (leftDerivedUpperStarTateObjectIso e 1).hom)⟦(1 : ℤ)⟧' =
      (leftDerivedUpperStarConstantComplexIso Λ j').hom ≫ kummerClass Λ u' ≫
        (leftDerivedUpperStarTateObjectIso j' 1).inv⟦(1 : ℤ)⟧' := by
  have hκ := leftDerivedUpperStar_map_kummerClass Λ e₁ u
  rw [hu] at hκ
  have hκ' : (L((e₁)^*[ModuleCat.{u + 1} Λ])).map (kummerClass Λ u) ≫
      ((L((e₁)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _ =
        (leftDerivedUpperStarConstantComplexIso Λ e₁).hom ≫ kummerClass Λ u' ≫
          (leftDerivedUpperStarTateObjectIso e₁ 1).inv⟦(1 : ℤ)⟧' := by
    rw [← cancel_mono ((leftDerivedUpperStarTateObjectIso e₁ 1).hom⟦(1 : ℤ)⟧'),
      Category.assoc, hκ, Category.assoc, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  erw [((L((e₁)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.naturality_assoc]
  rw [reassoc_of% hκ', reassoc_of% (leftDerivedUpperStarConstantComplexIso_square Λ sq)]
  simp only [Functor.comp_map, ← Functor.map_comp]
  rw [leftDerivedUpperStarTateObjectIso_square]

variable [Finite Λ] [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ U']

/-- The Kummer boundary `∂κ(f)` as the adjoint `Λ_U ⟶ (Rj_* Lj^* Λ_U(1))[1]` of the Kummer class
of `f` on `U_f`, followed by the boundary of the supported localization triangle. -/
lemma kummerBoundary_eq (f : Γ(U, ⊤)) :
    kummerBoundary Λ f =
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (U.basicOpen f).ι).unit.app _ ≫
        (R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ])).map
          ((leftDerivedUpperStarConstantComplexIso Λ (U.basicOpen f).ι).hom ≫
            kummerClass Λ (U.basicOpenUnit f) ≫
              (leftDerivedUpperStarTateObjectIso (U.basicOpen f).ι 1).inv⟦(1 : ℤ)⟧') ≫
        ((R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _) ≫
      ((supportedLocalizationBoundary Λ _ _
          (range_zeroLocusSubschemeι_singleton f) (tateObject Λ U 1))⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' _ (1 : ℤ) 1 2 rfl).inv.app _) := by
  rw [kummerBoundary, Adjunction.homEquiv_unit]
  simp only [Category.assoc]

/-- **Base change of the Kummer boundary.** For `e : U' ⟶ U` and a global function `f` on `U`, the
restriction of `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` to `U'` — the pullback `Le^* ∂κ(f)` read through
`Λ_{U'} ≅ Le^* Λ_U`, the shift compatibility of `Le^*` and the restriction of supports
`Le^* Ri_! Ri^! Λ_U(1) ⟶ Ri'_! Ri'^! Λ_{U'}(1)` (`AlgebraicGeometry.Etale.supportedRestriction`)
— is `∂κ(e^* f)`. This is the step "the Kummer class is compatible with the pullback" of the
proof of `proposition-purity-vector-bundles`: the naturality of the Kummer class
(`AlgebraicGeometry.Etale.kummerClass_square`) combined with the base change of the supported
localization triangle (`AlgebraicGeometry.Etale.supportedLocalizationBoundary_baseChange`).

```
Λ_{U'} ──≅──▶ Le^* Λ_U ──Le^* ∂κ(f)──▶ Le^* ((Ri_! Ri^! Λ_U(1))[2])
   │                                              │
   │ ∂κ(e^* f)                                    │ ≅ ≫ ψ[2]
   ▼                                              ▼
(Ri'_! Ri'^! Λ_{U'}(1))[2] ════════════ (Ri'_! Ri'^! Λ_{U'}(1))[2]
```
-/
theorem kummerBoundary_baseChange (e : U' ⟶ U) (f : Γ(U, ⊤))
    (g : U'.zeroLocusSubscheme {e.appTop f} ⟶ U.zeroLocusSubscheme {f})
    (hg : IsPullback g (U'.zeroLocusSubschemeι {e.appTop f}) (U.zeroLocusSubschemeι {f}) e) :
    (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
        (L((e)^*[ModuleCat.{u + 1} Λ])).map (kummerBoundary Λ f) ≫
        ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 : ℤ)).hom.app _ ≫
        (supportedRestriction Λ e _ _ g hg _ _
          (leftDerivedUpperStarTateObjectIso e 1))⟦(2 : ℤ)⟧' =
      kummerBoundary Λ (e.appTop f) := by
  let e₁ : (U'.basicOpen (e.appTop f) : Scheme.{u}) ⟶ U.basicOpen f :=
    e.resLE _ _ (Scheme.preimage_basicOpen_top e f).ge
  have sq : CommSq e₁ (U'.basicOpen (e.appTop f)).ι (U.basicOpen f).ι e :=
    ⟨Scheme.Hom.resLE_comp_ι _ _⟩
  have hu : Units.map e₁.appTop.hom.toMonoidHom (U.basicOpenUnit f) =
      U'.basicOpenUnit (e.appTop f) := by
    ext
    simp only [Units.coe_map, Scheme.basicOpenUnit, IsUnit.unit_spec]
    change e₁.appTop ((U.basicOpen f).ι.appTop f) =
      (U'.basicOpen (e.appTop f)).ι.appTop (e.appTop f)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
      congrArg (fun p ↦ p.appTop f) sq.w
  have hG1 := supportedLocalizationBoundary_baseChange Λ e
    (U.zeroLocusSubschemeι {f}) (U.basicOpen f).ι (U'.zeroLocusSubschemeι {e.appTop f})
    (U'.basicOpen (e.appTop f)).ι g e₁ (range_zeroLocusSubschemeι_singleton f)
    (range_zeroLocusSubschemeι_singleton _) hg sq (tateObject Λ U 1) (tateObject Λ U' 1)
    (leftDerivedUpperStarTateObjectIso e 1)
  have hK := kummerClass_square Λ sq (U.basicOpenUnit f) _ hu
  have hA := comp_leftDerivedUpperStar_map_adjoint_comp_derivedBaseChangeMap
    (ModuleCat.{u + 1} Λ) sq (constantComplex Λ U) (constantComplex Λ U')
    (leftDerivedUpperStarConstantComplexIso Λ e).inv _
    ((leftDerivedUpperStarConstantComplexIso Λ (U.basicOpen f).ι).hom ≫
      kummerClass Λ (U.basicOpenUnit f) ≫
        (leftDerivedUpperStarTateObjectIso (U.basicOpen f).ι 1).inv⟦(1 : ℤ)⟧') _
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).inv.app (tateObject Λ U 1) ≫
      (L(((U'.basicOpen (e.appTop f)).ι)^*[ModuleCat.{u + 1} Λ])).map
        (leftDerivedUpperStarTateObjectIso e 1).hom)
  conv_rhs at hG1 => rw [← Category.assoc]
  rw [hK] at hA
  exact kummerBoundary_comp_baseChange (L((e)^*[ModuleCat.{u + 1} Λ]))
    (leftDerivedUpperStarConstantComplexIso Λ e).inv _ _ _ _ _ _ _ _
    (kummerBoundary_eq Λ f) (kummerBoundary_eq Λ (e.appTop f)) hG1 hA

/-- `AlgebraicGeometry.Etale.kummerBoundary_baseChange` for a function `f'` on `U'` equal to the
pullback of `f`. -/
theorem kummerBoundary_baseChange_of_eq (e : U' ⟶ U) (f : Γ(U, ⊤)) (f' : Γ(U', ⊤))
    (hf : e.appTop f = f') (g : U'.zeroLocusSubscheme {f'} ⟶ U.zeroLocusSubscheme {f})
    (hg : IsPullback g (U'.zeroLocusSubschemeι {f'}) (U.zeroLocusSubschemeι {f}) e) :
    (leftDerivedUpperStarConstantComplexIso Λ e).inv ≫
        (L((e)^*[ModuleCat.{u + 1} Λ])).map (kummerBoundary Λ f) ≫
        ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 : ℤ)).hom.app _ ≫
        (supportedRestriction Λ e _ _ g hg _ _
          (leftDerivedUpperStarTateObjectIso e 1))⟦(2 : ℤ)⟧' =
      kummerBoundary Λ f' := by
  subst hf
  exact kummerBoundary_baseChange Λ e f g hg

end Kummer

section Restriction

variable {Λ : Type (u + 1)} [CommRing Λ]

variable (Λ) in
/-- The pullback `f^♯ h : Λ_X ⟶ Λ_X` of an endomorphism `h` of the constant complex `Λ_S` along
`f : X ⟶ S`: the derived pullback `Lf^* h`, read through `Lf^* Λ_S ≅ Λ_X`. -/
noncomputable def constantComplexEndPullback {X S : Scheme.{u}} (f : X ⟶ S)
    (h : constantComplex Λ S ⟶ constantComplex Λ S) :
    constantComplex Λ X ⟶ constantComplex Λ X :=
  (leftDerivedUpperStarConstantComplexIso Λ f).inv ≫ (L((f)^*[ModuleCat.{u + 1} Λ])).map h ≫
    (leftDerivedUpperStarConstantComplexIso Λ f).hom

@[simp]
lemma constantComplexEndPullback_id {X S : Scheme.{u}} (f : X ⟶ S) :
    constantComplexEndPullback Λ f (𝟙 _) = 𝟙 _ := by
  simp [constantComplexEndPullback]

/-- The pullback of endomorphisms of the constant complexes is compatible with composition:
`f^♯ (g^♯ h) = (f ≫ g)^♯ h`. -/
lemma constantComplexEndPullback_constantComplexEndPullback {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) (fg : X ⟶ S) (hfg : fg = f ≫ g)
    (h : constantComplex Λ S ⟶ constantComplex Λ S) :
    constantComplexEndPullback Λ f (constantComplexEndPullback Λ g h) =
      constantComplexEndPullback Λ fg h := by
  rw [constantComplexEndPullback, constantComplexEndPullback, constantComplexEndPullback,
    leftDerivedUpperStarConstantComplexIso_comp Λ f g fg hfg]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  erw [(leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g fg hfg).hom.naturality_assoc h,
    Iso.inv_hom_id_app_assoc]
  rfl

variable {X Y : Scheme.{u}}

/-- Two endomorphisms of the constant complex `Λ_X` are equal if their pullbacks along every
geometric point `x : Spec Ω ⟶ X` are equal. -/
lemma constantComplexEnd_ext {a b : constantComplex Λ X ⟶ constantComplex Λ X}
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
      constantComplexEndPullback Λ x a = constantComplexEndPullback Λ x b) :
    a = b :=
  constantComplex_hom_ext_of_leftDerivedUpperStar_map_eq (Iso.refl _) fun Ω _ _ x ↦ by
    simpa only [constantComplexEndPullback, cancel_epi, cancel_mono] using h Ω x

variable (Λ Y) in
/-- Every endomorphism `c` of `Λ` on the zero locus `V(t₁, …)` of the coordinates of the affine
space `𝔸^n_Y` is the pullback `s^♯ h` of an endomorphism `h` of `Λ_{𝔸^n_Y}`: through
`Y ≅ V(t₁, …)`, take for `h` the pullback of `c` along the projection `𝔸^n_Y ⟶ Y`, a retraction
of the zero section. -/
lemma exists_constantComplexEndPullback_zeroLocusSubschemeι_eq (n : Type u)
    {s : Set Γ(𝔸(n; Y), ⊤)} (hs : Set.range (AffineSpace.coord Y) = s)
    (c : constantComplex Λ (𝔸(n; Y).zeroLocusSubscheme s) ⟶
      constantComplex Λ (𝔸(n; Y).zeroLocusSubscheme s)) :
    ∃ h : constantComplex Λ 𝔸(n; Y) ⟶ constantComplex Λ 𝔸(n; Y),
      constantComplexEndPullback Λ (𝔸(n; Y).zeroLocusSubschemeι s) h = c := by
  let e := AffineSpace.zeroSectionIsoZeroLocusSubscheme n Y hs
  refine ⟨constantComplexEndPullback Λ (𝔸(n; Y) ↘ Y)
    (constantComplexEndPullback Λ e.hom c), constantComplexEnd_ext fun Ω _ _ x ↦ ?_⟩
  rw [constantComplexEndPullback_constantComplexEndPullback _ _ e.inv rfl,
    constantComplexEndPullback_constantComplexEndPullback x e.inv _ rfl,
    constantComplexEndPullback_constantComplexEndPullback _ e.hom x (by simp)]

end Restriction

section SupportedRestriction

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

variable {X Z U Z' : Scheme.{u}}

/-- Precomposing a class with supports with an endomorphism `h` of `Λ_X` precomposes its adjoint
with the pullback `i^♯ h` of `h` to the support. -/
lemma supportedClassMap_comp (i : Z ⟶ X) [IsClosedImmersion i]
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : constantComplex Λ X ⟶ constantComplex Λ X)
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    supportedClassMap Λ i (h ≫ γ) =
      constantComplexEndPullback Λ i h ≫ supportedClassMap Λ i γ := by
  have hc := leftDerivedUpperStarConstantComplexIso_comp Λ
    (HasCompactification.compactification i).i (HasCompactification.compactification i).g i
    (HasCompactification.compactification i).comm
  have key : constantComplexEndPullback Λ i h =
      (compactificationConstantComplexIso Λ i).inv ≫
        (L(((HasCompactification.compactification i).i)^*[ModuleCat.{u + 1} Λ])).map
          ((L(((HasCompactification.compactification i).g)^*[ModuleCat.{u + 1} Λ])).map h) ≫
        (compactificationConstantComplexIso Λ i).hom := by
    rw [constantComplexEndPullback, hc]
    simp only [compactificationConstantComplexIso, Iso.trans_inv, Iso.trans_hom, Iso.app_inv,
      Iso.app_hom, Category.assoc]
    rw [← Functor.comp_map, ← NatIso.naturality_1 (leftDerivedUpperStarComp
      (ModuleCat.{u + 1} Λ) _ _ i (HasCompactification.compactification i).comm) h]
    simp only [Category.assoc]
  rw [key]
  simp only [supportedClassMap, rightDerivedLowerShriekTranspose, Category.assoc,
    Iso.hom_inv_id_assoc, Adjunction.homEquiv_naturality_left_symm]
  rfl

/-- Precomposing a class with supports with an endomorphism `h` of `Λ_X` commutes with the
restriction of supports along `e`, which replaces `h` by its pullback `e^♯ h`. -/
lemma restrictSupportedClass_comp (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U) [IsClosedImmersion i]
    [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L')
    (h : constantComplex Λ X ⟶ constantComplex Λ X)
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    restrictSupportedClass Λ e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv τ (h ≫ γ) =
      constantComplexEndPullback Λ e h ≫
        restrictSupportedClass Λ e i i' g hg
          (leftDerivedUpperStarConstantComplexIso Λ e).inv τ γ := by
  simp [restrictSupportedClass, constantComplexEndPullback]

variable (Λ) in
/-- Classes with supports on `Z` are morphisms `Λ_Z ⟶ Ri^! L`: the bijection
`AlgebraicGeometry.Etale.supportedClassMap_bijective` as an equivalence. -/
noncomputable def supportedClassMapEquiv (i : Z ⟶ X) [IsClosedImmersion i]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (constantComplex Λ X ⟶
        (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) ≃
      (constantComplex Λ Z ⟶ (R(i)^![Λ]).obj L) :=
  Equiv.ofBijective _ (supportedClassMap_bijective Λ i L)

@[simp]
lemma supportedClassMapEquiv_apply (i : Z ⟶ X) [IsClosedImmersion i]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    supportedClassMapEquiv Λ i L γ = supportedClassMap Λ i γ :=
  rfl

variable (Λ) in
/-- The *restriction* `Λ_{Z'} ⟶ Ri'^! L'` along `e : U ⟶ X` of a morphism `φ : Λ_Z ⟶ Ri^! L`,
for the base change `i'` of the closed immersion `i` and an identification `τ : Le^* L ≅ L'`:
`φ` is read as a class with supports on `Z`
(`AlgebraicGeometry.Etale.supportedClassMapEquiv`), restricted along `e`
(`AlgebraicGeometry.Etale.restrictSupportedClass`) and read back as a morphism. This is the
exceptional base change `Lg^* Ri^! L ⟶ Ri'^! L'` applied to the pullback `Lg^* φ`. -/
noncomputable def restrictSupportedHom (e : U ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ U)
    [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L')
    (φ : constantComplex Λ Z ⟶ (R(i)^![Λ]).obj L) :
    constantComplex Λ Z' ⟶ (R(i')^![Λ]).obj L' :=
  supportedClassMap Λ i' (restrictSupportedClass Λ e i i' g hg
    (leftDerivedUpperStarConstantComplexIso Λ e).inv τ ((supportedClassMapEquiv Λ i L).symm φ))

/-- The restriction of `i^♯ h ≫ φ` along `e` is `i'^♯ (e^♯ h)` followed by the restriction of
`φ`, for an endomorphism `h` of `Λ_X`. -/
lemma restrictSupportedHom_constantComplexEndPullback_comp (e : U ⟶ X) (i : Z ⟶ X)
    (i' : Z' ⟶ U) [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z)
    (hg : IsPullback g i' i e)
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L' : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L')
    (h : constantComplex Λ X ⟶ constantComplex Λ X)
    (φ : constantComplex Λ Z ⟶ (R(i)^![Λ]).obj L) :
    restrictSupportedHom Λ e i i' g hg τ (constantComplexEndPullback Λ i h ≫ φ) =
      constantComplexEndPullback Λ i' (constantComplexEndPullback Λ e h) ≫
        restrictSupportedHom Λ e i i' g hg τ φ := by
  have hφ : (supportedClassMapEquiv Λ i L).symm (constantComplexEndPullback Λ i h ≫ φ) =
      h ≫ (supportedClassMapEquiv Λ i L).symm φ := by
    rw [Equiv.symm_apply_eq, supportedClassMapEquiv_apply, supportedClassMap_comp,
      ← supportedClassMapEquiv_apply, Equiv.apply_symm_apply]
  rw [restrictSupportedHom, restrictSupportedHom, hφ, restrictSupportedClass_comp,
    supportedClassMap_comp]

end SupportedRestriction

end Etale

end AlgebraicGeometry
