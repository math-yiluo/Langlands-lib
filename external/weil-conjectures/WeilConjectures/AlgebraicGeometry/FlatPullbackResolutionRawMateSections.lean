/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
import WeilConjectures.AlgebraicGeometry.FlatUnitRawSections
import all WeilConjectures.AlgebraicGeometry.HigherDirectImageResolutionNaturality

/-! # The flat pullback unit on raw section cohomology

Source: Stacks Project, Cohomology, Tags 02N7 and 01E4.
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option Elab.async true
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackMap

private def rawSectionClass {Y : Scheme.{uBC}}
    (K : CochainComplex Y.Modules ℕ) (V : Y.Opens) (p : ℕ) :
    (((RingedSpace.openModuleSections Y.toRingedSpace V).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology p ⟶ (K.homology p).presheaf.obj (op V) :=
  let U := SheafOfModules.forget Y.ringCatSheaf
  let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op V)
  ((((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso E).hom ≫
    E.map (sectionCohomologyTheta K p)

attribute [local irreducible] sectionCohomologyTheta
attribute [local irreducible] flatBaseChangeResolutionQ flatBaseChangeResolutionC

-- Comparing the composite evaluation functor requires unfolding section interfaces.
private theorem rawSectionClass_naturality {Y : Scheme.{uBC}}
    {K K' : CochainComplex Y.Modules ℕ} (c : K ⟶ K') (p : ℕ) (V : Y.Opens) :
    HomologicalComplex.homologyMap
        (((RingedSpace.openModuleSections Y.toRingedSpace V).mapHomologicalComplex
          (ComplexShape.up ℕ)).map c) p ≫ rawSectionClass K' V p =
      rawSectionClass K V p ≫ Hom.app (HomologicalComplex.homologyMap c p) V := by
  let U := SheafOfModules.forget Y.ringCatSheaf
  let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op V)
  have hE := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map
      ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map c)) E
  change HomologicalComplex.homologyMap
      (((RingedSpace.openModuleSections Y.toRingedSpace V).mapHomologicalComplex
        (ComplexShape.up ℕ)).map c) p ≫
      ((((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K').sc p).mapHomologyIso E).hom =
    ((((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso E).hom ≫
      E.map (HomologicalComplex.homologyMap
        ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map c) p) at hE
  have hθ := congrArg E.map (AlgebraicGeometry.sectionCohomologyTheta_naturality c p)
  simp only [Functor.map_comp] at hθ
  dsimp only [rawSectionClass]
  rw [← Category.assoc]
  erw [hE]
  rw [Category.assoc]
  erw [hθ]
  rfl

set_option maxHeartbeats 200000 in
-- Comparing section and pushforward functor interfaces involves identity scalar restriction.
/-- The homology mate on a fixed pair of resolution complexes acts on raw section classes.
Source: Stacks Project, Cohomology, Tags 02N7 and 01E4.
(blueprint: lem-weil-pbc-flat-pullback-resolution-raw-mate-sections).

Proof: Apply the degreewise adjunction unit to a cycle of the source section complex.
Naturality for the cycle inclusion identifies the resulting section with the unit on
its cycle sheaf. Exactness of flat tensor pullback identifies both the cycle sheaf
and the homology quotient with those of the pulled back complex. Naturality of the
unit for the quotient therefore identifies the resulting raw homology class with
the mate of the inverse exact homology comparison. The cycle formula for the
sheafification comparison theta sends this class to its class in the homology sheaf.
Now compose with the termwise adjoint c of q. Theta is natural for c, as follows
from naturality of the sheafification counit and the exact homology comparison.
The complex adjunction identity eta followed by pushforward of c equals q.
Hence the composite class is precisely H(q) followed by theta on the target.
This proves the displayed raw-complex identity. There are no resolution-section
isomorphisms or derived-image isomorphisms in this statement. -/
theorem flatBaseChangeResolution_rawMate_sections {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S) [Flat g] {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex) (p : ℕ) (V : S.Opens) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let L := ((pushforward (pullback.fst g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex
    let U := SheafOfModules.forget S.ringCatSheaf
    let U' := SheafOfModules.forget S'.ringCatSheaf
    let E := PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op V)
    let E' := PresheafOfModules.toPresheaf S'.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S'.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op (g ⁻¹ᵁ V))
    let adj := Classical.choose (exists_tensorPullbackAdjunction g)
    ((((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso E).hom ≫
        E.map (sectionCohomologyTheta K p) ≫
        Hom.app (adj.homEquiv _ _
          (((K.sc p).mapHomologyIso (tensorPullback g)).inv ≫
            HomologicalComplex.homologyMap (flatBaseChangeResolutionC f g I J t) p)) V =
      HomologicalComplex.homologyMap
        (((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (flatBaseChangeResolutionQ f g I J t)) p ≫
        ((((U'.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).sc p)
          |>.mapHomologyIso E').hom ≫ E'.map (sectionCohomologyTheta L p) := by
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let L := ((pushforward (pullback.fst g f)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj J.cocomplex
  let adj := Classical.choose (exists_tensorPullbackAdjunction g)
  let A := (tensorPullback g).mapHomologicalComplex (ComplexShape.up ℕ)
  let B := (pushforward g).mapHomologicalComplex (ComplexShape.up ℕ)
  let c := flatBaseChangeResolutionC f g I J t
  let q := flatBaseChangeResolutionQ f g I J t
  let η := (adj.mapHomologicalComplex (ComplexShape.up ℕ)).unit.app K
  let T := (RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let T' := (RingedSpace.openModuleSections S'.toRingedSpace (g ⁻¹ᵁ V)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  have hunit : rawSectionClass K V p ≫
      Hom.app (adj.homEquiv _ _ ((K.sc p).mapHomologyIso (tensorPullback g)).inv) V =
      HomologicalComplex.homologyMap (T.map η) p ≫
        rawSectionClass (A.obj K) (g ⁻¹ᵁ V) p := by
    simpa only [rawSectionClass, Category.assoc] using flatUnit_raw_sections g K p V
  have hnat := rawSectionClass_naturality c p (g ⁻¹ᵁ V)
  have hmate : η ≫ B.map c = q := by
    simp only [η, c, flatBaseChangeResolutionC]
    change (adj.mapHomologicalComplex (ComplexShape.up ℕ)).unit.app K ≫
      B.map ((adj.mapHomologicalComplex (ComplexShape.up ℕ)).homEquiv _ _ |>.symm q) = q
    simpa only [Adjunction.homEquiv_unit] using
      ((adj.mapHomologicalComplex (ComplexShape.up ℕ)).homEquiv K L).apply_symm_apply q
  have hsections : T.map (B.map c) = T'.map c := by
    rfl
  suffices h : rawSectionClass K V p ≫
      Hom.app (adj.homEquiv _ _
        (((K.sc p).mapHomologyIso (tensorPullback g)).inv ≫
          HomologicalComplex.homologyMap c p)) V =
    HomologicalComplex.homologyMap (T.map q) p ≫ rawSectionClass L (g ⁻¹ᵁ V) p by
    simpa only [rawSectionClass, Category.assoc] using h
  rw [adj.homEquiv_naturality_right, Hom.comp_app, pushforward_map_app,
    ← Category.assoc, hunit, Category.assoc, ← hnat, ← Category.assoc]
  rw [← hsections, ← HomologicalComplex.homologyMap_comp, ← Functor.map_comp, hmate]

end AlgebraicGeometry.Scheme.Modules
