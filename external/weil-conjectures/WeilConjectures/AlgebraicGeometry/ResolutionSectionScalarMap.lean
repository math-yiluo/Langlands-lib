/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.ResolutionScalarAction
import WeilConjectures.AlgebraicGeometry.ResolutionSectionsHomologyScalar

/-! # Scalar compatibility of the normalized resolution class

Source: Stacks Project, Tags 01E4, 01E5 and 03FD.
(blueprint: lem-pc-resolution-section-scalar-map)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical section class map intertwines multiplication endomorphisms.
No Ext comparison, affine open, finiteness or quasi-coherence is assumed.
Source: Stacks Project, Tags 01E4 and 01E5; naturality of derived functors.
(blueprint: lem-pc-resolution-section-scalar-map)

Proof: Module-valued derived global sections take multiplication by b on the module
M to scalar multiplication on cohomology, by moduleCohomology_map_smulHom. The
module-valued resolution comparison e is linear, so it preserves b. The middle
three arrows T preserve the pulled-back scalar by resolutionSectionsHomology_scalar.
The evaluated sectionCohomologyTheta is a module morphism and hence preserves a;
the same holds for the final inverse resolution comparison. Compose these four
pointwise equalities. No comparison of lifts or vanishing argument is needed.
Degree zero is multiplication on sections, and empty opens and zero modules are
covered by the same module and homology maps. -/
theorem resolutionSectionClass_map_smulHom
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (I : InjectiveResolution F)
    (p : ℕ) (V : S.Opens) (R : RestrictedResolutionSections I (f ⁻¹ᵁ V)) :
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let M := (restrictFunctor (f ⁻¹ᵁ V).ι).obj F
    let C := RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p
    let c := resolutionSectionClass R.resolution
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
      V R.sections p ≫ Hom.app (I.isoRightDerivedObj (pushforward f) p).inv V
    ∀ (a : Γ(S, V)) (x : C.obj M),
      c ((C.map (M.smulHom (((Scheme.ΓSpecIso Γ(S, V)).inv ≫ h.appTop).hom a))).hom x) =
        a • c x := by
  dsimp only
  intro a x
  let U := f ⁻¹ᵁ V
  let M := (restrictFunctor U.ι).obj F
  let b := ((Scheme.ΓSpecIso Γ(S, V)).inv ≫
    (f.resLE V U le_rfl ≫ V.toSpecΓ).appTop).hom a
  have hscalar := moduleCohomology_map_smulHom M R.resolution p b x
  let := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
  let e := R.resolution.isoRightDerivedObj
    (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) p
  have hs := resolutionSectionsHomology_scalar f F I p V R a (e.hom.hom x)
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let θ := (sectionCohomologyTheta K p).app (op V)
  have hi := Hom.app_smul (I.isoRightDerivedObj (pushforward f) p).inv a
  let T := (((RingedSpace.globalSectionsComplex R.resolution).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).inv ≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
      R.sections.hom ≫
    (((((SheafOfModules.forget S.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso
        (PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
          (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V))).hom
  let δ := Hom.app (I.isoRightDerivedObj (pushforward f) p).inv V
  dsimp only [resolutionSectionClass, AddCommGrpCat.comp_apply]
  change δ (θ.hom (T (e.hom.hom
    (((RingedSpace.moduleCohomology U.toScheme.toRingedSpace p).map
      (M.smulHom b)).hom x)))) = a • δ (θ.hom (T (e.hom.hom x)))
  exact (congrArg (fun z ↦ δ (θ.hom (T (e.hom.hom z)))) hscalar).trans
    ((congrArg (fun z ↦ δ (θ.hom (T z))) (e.hom.hom.map_smul b x)).trans
      ((congrArg (fun z ↦ δ (θ.hom z)) hs).trans
        ((congrArg (fun z ↦ δ z) (θ.hom.map_smul a _)).trans (hi _))))

end AlgebraicGeometry.Scheme.Modules
