/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Sites.Adjunction

/-! # Constructibility under restriction of constant scalars

Restriction of scalars along a map `A →+* B` of finite coefficient rings preserves
constructibility of pro-étale module sheaves over the constant ring sheaf
(`AlgebraicGeometry.Scheme.isConstructibleProEtaleModuleSheaf_restrictScalars`):
finite `B`-modules stay finite over `A`, and restriction of scalars commutes with
pro-étale inverse image and with constant sheaves.

## References

* Stacks Project, Tags 093I and 09AJ
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

open scoped TensorProduct

/-- Restriction of scalars commutes with pro-étale inverse image. -/
private noncomputable def restrictScalarsUpperStarIso
    {X Y : AlgebraicGeometry.Scheme.{u}} {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (f : A →+* B) (g : Y ⟶ X) :
    sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f) ⋙
        AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) g ≅
      AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} B) g ⋙
        sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f) :=
  (conjugateIsoEquiv
    ((AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction _ g).comp
      (CategoryTheory.Sheaf.restrictCoextendScalarsAdj (ProEt.topology Y) f))
    ((CategoryTheory.Sheaf.restrictCoextendScalarsAdj (ProEt.topology X) f).comp
      (AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction _ g))).symm (Iso.refl _)

/-- Restriction of scalars to a finite ring preserves finite local constancy. -/
private theorem isFiniteLocallyConstant_restrictScalars
    {X : AlgebraicGeometry.Scheme.{u}} {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite B] (f : A →+* B)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
    (hM : AlgebraicGeometry.ProEtale.IsFiniteLocallyConstant B M) :
    AlgebraicGeometry.ProEtale.IsFiniteLocallyConstant A
      ((sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)).obj M) := by
  let : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} f).isLeftAdjoint
  obtain ⟨I, W, g, hg, h⟩ := hM
  refine ⟨I, W, g, hg, fun i ↦ ?_⟩
  obtain ⟨N, hN, ⟨e⟩⟩ := h i
  let R := sheafCompose (ProEt.topology (W i)) (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)
  have : Finite N := Module.finite_of_finite B
  exact ⟨(ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f).obj N,
    @Module.Finite.of_finite _ _ _ _ _ (inferInstanceAs (Finite N)),
    ⟨(restrictScalarsUpperStarIso f (g i)).app M ≪≫
      R.mapIso e ≪≫ (constantCommuteCompose (ProEt.topology (W i))
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)).app N⟩⟩

/-- Restriction of scalars along a map to a finite ring preserves constructibility. -/
private theorem isConstructible_restrictScalars
    (X : AlgebraicGeometry.Scheme.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite B] (f : A →+* B)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
    (hM : AlgebraicGeometry.ProEtale.IsConstructible B M) :
    AlgebraicGeometry.ProEtale.IsConstructible A
      ((sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} f)).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun i ↦ ?_⟩
  exact AlgebraicGeometry.ProEtale.isFiniteLocallyConstant_of_iso
    ((restrictScalarsUpperStarIso f (S.immersion i)).app M).symm
    (isFiniteLocallyConstant_restrictScalars f _ (hS i))

/-- The constant-scalar units are natural in the coefficient ring. -/
private theorem constantScalarUnit_naturality
    (Y : AlgebraicGeometry.Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    proEtaleModuleScalarUnit Y A ≫
        ((adicLisseForget Y).map ((constantSheaf (ProEt.topology Y)
          CommRingCat.{u + 1}).map (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))).hom =
      Functor.whiskerRight
        ((Functor.const Y.ProEtᵒᵖ).map
          (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))
        (forget₂ CommRingCat RingCat) ≫ proEtaleModuleScalarUnit Y B := by
  ext U b
  exact ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))).symm U) b

/-- Restriction to constant scalars commutes with restriction along a coefficient map. -/
private noncomputable def restrictionEncodingIso
    (Y : AlgebraicGeometry.Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    pbcRestrict ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f))) ⋙
        proEtaleModuleRestriction Y A ≅
      proEtaleModuleRestriction Y B ⋙ sheafCompose (ProEt.topology Y)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (RingHom.ulift.{u + 1, u + 1} f)) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · let P := ((pbcRestrict ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f))) ⋙
        proEtaleModuleRestriction Y A).obj M).obj.obj U
    let Q := ((proEtaleModuleRestriction Y B ⋙ sheafCompose (ProEt.topology Y)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (RingHom.ulift.{u + 1, u + 1} f))).obj M).obj.obj U
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[ULift.{u + 1} A] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun b m ↦ ?_ }).toModuleIso
    exact congrArg (fun a ↦ a • (show M.val.obj U from m))
      (ConcreteCategory.congr_hom (congr_app (constantScalarUnit_naturality Y f) U) b)
  · intro U V a
    ext m
    rfl
  · intro M N a
    ext U m
    rfl

/-- Restriction of scalars along a map of finite coefficient rings preserves constructibility
of pro-étale module sheaves: finite modules over the target ring stay finite over the source. -/
theorem isConstructibleProEtaleModuleSheaf_restrictScalars (T : Scheme.{u}) {A B : Type u}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (f : A →+* B)
    (M : proEtaleRingModules T (proEtaleConstantRing T B))
    (hM : IsConstructibleProEtaleModuleSheaf T B M) :
    IsConstructibleProEtaleModuleSheaf T A
      ((pbcRestrict ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))).obj M) := by
  rw [proEtaleModuleRestriction_constructible_iff] at hM ⊢
  exact ProEtale.isConstructible_of_iso ((restrictionEncodingIso T f).app M).symm
    (isConstructible_restrictScalars T (RingHom.ulift.{u + 1, u + 1} f) _ hM)


end AlgebraicGeometry.Scheme
