/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-!
# Derived direct image commutes with restriction to an open

Source: Stacks Project, Cohomology, Lemma 20.32.4, Tag 08FE
(blueprint: lem-pc-restrict-derived-direct-image-open).
-/

@[expose] public section

universe u wX wY wU wV

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- The explicit additivity witnesses require a larger typeclass-search budget.
/-- Restricting `Rf_*` to an open `V` is naturally isomorphic to first restricting to
`f ⁻¹ᵁ V` and then applying the derived direct image of the induced morphism `f ∣_ V`.
The components of this functor isomorphism are the canonical comparisons for every E.
Source: Stacks Project, Cohomology, Lemma 20.32.4 (Tag 08FE)
(blueprint: lem-pc-restrict-derived-direct-image-open).

Proof:
1. Choose a K-injective resolution E → I on X. Its restriction to the inverse-image
   open is K-injective by `lem-sc-derived-k-injective-restrict-open` (Tag 08BS).
2. By `def-pc-ringed-spaces-derived-direct-image`, `Rf_*E` is represented by f_*I,
   and the derived direct image of the restricted E is represented by g_*(I|U).
   On every open W of V both complexes have sections I(f⁻¹W). These identifications
   commute with differentials and are natural in E, giving the natural isomorphism. -/
theorem schemeDerivedDirectImage_openRestriction {X Y : Scheme.{u}}
    (f : X ⟶ Y) (V : Y.Opens)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{wV} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))] :
    Nonempty
      ((schemeDerivedDirectImage f ⋙
          (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
            (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V ⋙
            Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
              (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv V))
            (Functor.additive_of_preserves_binary_products _)
            (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _))) ≅
        (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (f ⁻¹ᵁ V) ⋙
            Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (f ⁻¹ᵁ V)))
              (D := SheafOfModules.{u}
                (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv (f ⁻¹ᵁ V)))
          (Functor.additive_of_preserves_binary_products _)
          (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)) ⋙
          schemeDerivedDirectImage (f ∣_ V)) := by
  classical
  let rX := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (f ⁻¹ᵁ V)
  let eX := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (f ⁻¹ᵁ V)))
    (D := SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv (f ⁻¹ᵁ V))
  let rY := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V
  let eY := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
    (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv V)
  have : rX.Additive := Functor.additive_of_preserves_binary_products _
  have : eX.Additive := Functor.additive_of_preserves_binary_products _
  have : (rX ⋙ eX).Additive := Functor.additive_of_preserves_binary_products _
  have : (rY ⋙ eY).Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits (rX ⋙ eX) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (rX ⋙ eX) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (rY ⋙ eY) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (rY ⋙ eY) := comp_preservesFiniteColimits _ _
  have : rX.PreservesKInjectiveComplexes :=
    ⟨fun I _ ↦ kInjective_of_restrict_open X.toRingedSpace (f ⁻¹ᵁ V) I⟩
  have : eX.PreservesKInjectiveComplexes := inferInstance
  have : (rX ⋙ eX).PreservesKInjectiveComplexes := inferInstance
  -- The underived comparison is the sectionwise identity from Tag 08FE.
  have e : RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙ (rY ⋙ eY) ≅
      (rX ⋙ eX) ⋙ RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom := by
    refine Functor.isoWhiskerLeft _ (Scheme.Modules.overFunctorEquiv V) ≪≫
      ?_ ≪≫ Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ V)).symm _
    change Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙ Scheme.Modules.pushforward (f ∣_ V)
    refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫
      (SheafOfModules.pushforwardComp _ _).symm
    refine SheafOfModules.pushforwardCongr₂ _ ?_ ?_
    · refine NatIso.ofComponents (fun W ↦ eqToIso ?_) ?_
      · exact image_morphismRestrict_preimage f V W
      · cat_disch
    · ext W x
      simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
      dsimp
      exact congr($(morphismRestrict_app f V W.unop) x).symm
  -- Derive the comparison, using exactness on Y and K-injectivity preservation on X.
  exact ⟨(Functor.rightDerivedFunctorCompMapDerivedCategoryIso.{wX, wY, wV}
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) (rY ⋙ eY)).symm ≪≫
    Functor.rightDerivedFunctorNatIso.{u, u, u + 1, u + 1, wX, wV} e ≪≫
    Functor.rightDerivedFunctorCompIso.{u, u, u, u + 1, u + 1, u + 1,
      wX, wU, wV} (rX ⋙ eX)
      (RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom) ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory.{wX, wU} (rX ⋙ eX))
      (schemeDerivedDirectImage (f ∣_ V))⟩

end AlgebraicGeometry
