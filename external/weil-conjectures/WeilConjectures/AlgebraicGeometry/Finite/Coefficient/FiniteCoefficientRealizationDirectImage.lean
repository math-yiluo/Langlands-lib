/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage

/-! # Direct image and finite coefficient realization

Source: Stacks Project, Modules on Sites, sheafification of module presheaves
and the definition of pushforward (sites-modules.tex).
(blueprint: lem-weil-pbc-finite-coefficient-realization-direct-image)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

private theorem scalarDirectImage_square
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    finiteCoefficientScalarMap Y Λ ≫ (finiteCoefficientDirectImageRingMap f Λ).hom =
      Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (finiteCoefficientScalarMap X Λ) := by
  dsimp only [finiteCoefficientScalarMap, finiteCoefficientDirectImageRingMap]
  rw [Category.assoc]
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology Y) RingCat.{u + 1}).homEquiv
    (finiteCoefficientPresheaf Y Λ)
    ((Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
      (finiteCoefficientRingSheaf X Λ))).apply_symm_apply
      (finiteCoefficientPullbackPresheafMap f Λ ≫
        Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
          (toSheafify (Scheme.ProEt.topology X) (finiteCoefficientPresheaf X Λ)))
  rw [Adjunction.homEquiv_unit] at h
  change toSheafify (Scheme.ProEt.topology Y) (finiteCoefficientPresheaf Y Λ) ≫ _ = _ at h
  erw [h]
  rw [← Category.assoc]
  change (finiteCoefficientConstants Y Λ ≫ finiteCoefficientPullbackPresheafMap f Λ) ≫ _ = _
  have hc : finiteCoefficientConstants Y Λ ≫ finiteCoefficientPullbackPresheafMap f Λ =
      Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (finiteCoefficientConstants X Λ) := by
    ext U r
    rfl
  rw [hc]
  rfl

private noncomputable def coefficientEmbedding (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :=
  sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ) ⋙
    finiteCoefficientModulePresheaf T.ProEt Λ

private noncomputable def coefficientRestriction (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :=
  SheafOfModules.forget.{u + 1} (finiteCoefficientRingSheaf T Λ) ⋙
    PresheafOfModules.restrictScalars.{u + 1} (finiteCoefficientScalarMap T Λ)

private noncomputable def coefficientUnitIso (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    coefficientEmbedding T Λ ≅ finiteCoefficientRealization T Λ ⋙
      coefficientRestriction T Λ := by
  have hunit (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)) :
      IsIso ((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (finiteCoefficientScalarMap T Λ)).unit.app ((coefficientEmbedding T Λ).obj F)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F).property
  let η : coefficientEmbedding T Λ ⟶
      (coefficientEmbedding T Λ ⋙
        PresheafOfModules.sheafification.{u + 1} (finiteCoefficientScalarMap T Λ)) ⋙
          coefficientRestriction T Λ :=
    Functor.whiskerLeft (coefficientEmbedding T Λ)
      (PresheafOfModules.sheafificationAdjunction.{u + 1} (finiteCoefficientScalarMap T Λ)).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hunit
  exact asIso η

private noncomputable def restrictionDirectImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    finiteCoefficientModuleDirectImage f Λ ⋙ coefficientRestriction Y Λ ≅
      coefficientRestriction X Λ ⋙
        PresheafOfModules.pushforward₀ (Scheme.proEtaleBaseChange f)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of Λ)) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let L := ((finiteCoefficientModuleDirectImage f Λ ⋙ coefficientRestriction Y Λ).obj M)
    let R := ((coefficientRestriction X Λ ⋙
      PresheafOfModules.pushforward₀ (Scheme.proEtaleBaseChange f)
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of Λ))).obj M)
    change L ≅ R
    refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
    · let g : L.obj U ≃ₗ[Λ] R.obj U :=
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r m
            have h := congrArg (fun t ↦ (t.app U).hom r) (scalarDirectImage_square f Λ)
            change ((finiteCoefficientDirectImageRingMap f Λ).hom.app U)
              ((finiteCoefficientScalarMap Y Λ).app U r) •
                (show M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U) from m) =
                (finiteCoefficientScalarMap X Λ).app
                  ((Scheme.proEtaleBaseChange f).op.obj U) r •
                    (show M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U) from m)
            exact congrArg (fun a : (finiteCoefficientRingSheaf X Λ).obj.obj
              ((Scheme.proEtaleBaseChange f).op.obj U) ↦ a •
                (show M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U) from m)) h }
      exact g.toModuleIso
    · intro U V g
      ext x
      rfl
  · intro M N g
    ext U x
    rfl

end AlgebraicGeometry.ProEtale
