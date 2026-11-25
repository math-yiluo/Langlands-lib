/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
import WeilConjectures.CategoryTheory.Finite.FinitePowerComplex
import all WeilConjectures.Algebra.Homology.Finite.FiniteFreeScalarExtension
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Finite-free coordinates for a specified scalar presentation

Source: Stacks Project, Tags 03EK and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

local instance unitSMul_presentedScalarCoordinates (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M : proEtaleRingModules X R) (V : X.ProEtᵒᵖ) :
    SMul ((SheafOfModules.unit ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).val.obj V) (M.val.obj V) :=
  inferInstanceAs (SMul (R.obj.obj V) (M.val.obj V))

private def basisPowerIso (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (d : ℕ) :
    (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅
    SheafOfModules.free (R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (ULift.{u + 1} (Fin d)) := by
  let O : proEtaleRingModules X R := SheafOfModules.unit _
  letI : HasBiproduct (fun _ : Fin d ↦ O) := HasBiproduct.of_hasProduct _
  letI : HasBiproduct (fun _ : ULift.{u + 1} (Fin d) ↦ O) :=
    HasBiproduct.of_hasCoproduct _
  change (∏ᶜ fun _ : Fin d ↦ O) ≅ (∐ fun _ : ULift.{u + 1} (Fin d) ↦ O)
  exact (biproduct.isoProduct (fun _ : Fin d ↦ O)).symm ≪≫
    biproduct.whiskerEquiv (f := fun _ : Fin d ↦ O)
      (g := fun _ : ULift.{u + 1} (Fin d) ↦ O)
      (Equiv.ulift.{u + 1, 0} (α := Fin d)).symm (fun _ ↦ Iso.refl O) ≪≫
    biproduct.isoCoproduct (fun _ : ULift.{u + 1} (Fin d) ↦ O)

set_option maxHeartbeats 500000 in
-- Elaborating the presentation transport and tensor coordinates requires extra heartbeats.
/-- The tensor coordinates transported through the specified ordinary presentation.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sp-finite-free-presented-scalar-coordinates). -/
@[irreducible] private def presentedFiniteFreeCoordinates (X : Scheme.{u})
    (s : ScalarModel X) {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (d : ℕ)
    (θ : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅
      (proEtaleRingRestrictScalars a).obj (SheafOfModules.unit ((sheafCompose
        (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))) :
    (s.presentation a).ordinary ⋙ proEtaleRingRestrictScalars a ≅
      Functor.const (Discrete (Fin d)) ⋙ lim :=
  NatIso.ofComponents (fun M ↦ (proEtaleRingRestrictScalars a).mapIso
    (eqToIso ((s.presentation a).obj_eq M)) ≪≫
      SheafOfModules.scalarExtensionIso a d θ M) (by
    intro M N f
    let p := s.presentation a
    let U := proEtaleRingRestrictScalars a
    change U.map (p.ordinary.map f) ≫ U.map (eqToHom (p.obj_eq N)) ≫
      (SheafOfModules.scalarExtensionIso a d θ N).hom =
      U.map (eqToHom (p.obj_eq M)) ≫
        (SheafOfModules.scalarExtensionIso a d θ M).hom ≫ _
    rw [← U.map_comp_assoc]
    have hm : p.ordinary.map f ≫ eqToHom (p.obj_eq N) =
        eqToHom (p.obj_eq M) ≫ SheafOfModules.changeOfRingsHom a M f := by
      rw [p.map_eq]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [hm, U.map_comp, Category.assoc,
      SheafOfModules.scalarExtensionIso_naturality a d θ f]
    apply congrArg (fun g ↦ U.map (eqToHom (p.obj_eq M)) ≫
      (SheafOfModules.scalarExtensionIso a d θ M).hom ≫ g)
    apply Pi.hom_ext
    intro i
    erw [Pi.map_π])

/-- Finite-basis coordinates make presented scalar extension exact and its universal
counit invertible on every homotopy complex.
Source: Stacks Project, Tags 03EK and 06YY.
(blueprint: lem-sp-finite-free-presented-scalar-coordinates).

Proof: identify the free module with the finite product of regular modules, including
rank zero. Apply the finite-basis tensor coordinate isomorphism and transport its
components along the presentation's object equations. Its naturality follows from
the presentation's map equations. Finite powers are exact. Restriction of scalars is
exact and reflects isomorphisms, so exactness of its composite with scalar extension
implies exactness of scalar extension. The exact extension's homotopy functor followed
by localization inverts quasi-isomorphisms. The universal left-derived counit is
therefore an isomorphism, by uniqueness of localization factorizations. -/
theorem finiteFreeDirectImage_presentedScalarCoordinates (X : Scheme.{u})
    (s : ScalarModel X) {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (d : ℕ)
    (θ : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅
      (proEtaleRingRestrictScalars a).obj (SheafOfModules.unit ((sheafCompose
        (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))) :
    ∃ φ : (s.presentation a).ordinary ⋙ proEtaleRingRestrictScalars a ≅
        Functor.const (Discrete (Fin d)) ⋙ lim,
      PreservesFiniteLimits (s.presentation a).ordinary ∧
      PreservesFiniteColimits (s.presentation a).ordinary ∧
      (∀ H : HomotopyCategory (proEtaleRingModules X R) (.up ℤ),
        IsIso ((s.presentation a).counit.app H)) ∧
      ∀ (M : proEtaleRingModules X R) (V : X.ProEtᵒᵖ)
        (b : S.obj.obj V) (m : M.val.obj V) (i : Fin d),
        (φ.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) i).val.app V
          (SheafOfModules.SuccessiveDerivedQuotient.sectionTensor (s.presentation a) M V b m) =
        (θ.inv ≫ Pi.π (fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose
          (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) i).val.app V
            b • m := by
  let p := s.presentation a
  let U := proEtaleRingRestrictScalars a
  let φ := presentedFiniteFreeCoordinates X s a d θ
  have : PreservesFiniteLimits U := inferInstance
  have : PreservesFiniteColimits U := inferInstance
  have : (U ⋙ SheafOfModules.toSheaf _).ReflectsIsomorphisms :=
    inferInstanceAs (SheafOfModules.toSheaf ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)).ReflectsIsomorphisms
  have : U.ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_comp U (SheafOfModules.toSheaf _)
  have : PreservesFiniteLimits (p.ordinary ⋙ U) :=
    preservesFiniteLimits_of_natIso φ.symm
  have : PreservesFiniteColimits (Functor.const (Discrete (Fin d)) ⋙
      (lim : (Discrete (Fin d) ⥤ proEtaleRingModules X R) ⥤ _)) :=
    preservesFiniteColimits_of_natIso (finitePowerFunctorIso d).symm
  have : PreservesFiniteColimits (p.ordinary ⋙ U) :=
    preservesFiniteColimits_of_natIso φ.symm
  have : PreservesFiniteLimits p.ordinary :=
    preservesFiniteLimits_of_reflects_of_preserves p.ordinary U
  have : PreservesFiniteColimits p.ordinary :=
    preservesFiniteColimits_of_reflects_of_preserves p.ordinary U
  let _ := p.universal
  have hε : IsIso p.counit := by
    apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts p.derived p.counit
      (W := HomotopyCategory.quasiIso (proEtaleRingModules X R) (.up ℤ))
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso _ p.ordinary.mapDerivedCategoryFactorsh]
    exact MorphismProperty.IsInvertedBy.of_comp _ DerivedCategory.Qh
      (Localization.inverts DerivedCategory.Qh _) p.ordinary.mapDerivedCategory
  refine ⟨φ, inferInstance, inferInstance, (fun H ↦ inferInstance), ?_⟩
  intro M V b m i
  have ht := SheafOfModules.scalarExtensionIso_tmul a d θ M V b m i
  dsimp only [φ]
  unfold presentedFiniteFreeCoordinates
  change ((U.map (eqToHom (p.obj_eq M)) ≫
    (SheafOfModules.scalarExtensionIso a d θ M).hom) ≫ Pi.π _ i).val.app V
      ((eqToHom (p.obj_eq M).symm).val.app V
        (SheafOfModules.SuccessiveDerivedQuotient.pure a M V b m)) = _
  have he : U.map (eqToHom (p.obj_eq M).symm) ≫ U.map (eqToHom (p.obj_eq M)) =
      𝟙 _ := by simp only [← U.map_comp, eqToHom_trans, eqToHom_refl, U.map_id]
  have hh := congrArg (fun f ↦ f.val.app V
    (SheafOfModules.SuccessiveDerivedQuotient.pure a M V b m))
    (show U.map (eqToHom (p.obj_eq M).symm) ≫ U.map (eqToHom (p.obj_eq M)) ≫
      (SheafOfModules.scalarExtensionIso a d θ M).hom ≫ Pi.π _ i =
      (SheafOfModules.scalarExtensionIso a d θ M).hom ≫ Pi.π _ i by
        rw [← Category.assoc, ← Category.assoc, he, Category.id_comp])
  exact hh.trans ht

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
