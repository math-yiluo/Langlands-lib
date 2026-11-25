/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

import WeilConjectures.AlgebraicGeometry.OpenModuleCohomologyComparison
import WeilConjectures.Topology.RestrictInjectiveResolution
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.Grp.Zero

@[expose] public section
universe u wC wV
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
namespace AlgebraicGeometry

-- Keep the original hypotheses hV and hq, although the proof works without them.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency.types true in
-- Comparing the transported injective resolution and its section complexes needs extra elaboration.
/-- Local vanishing on each affine open; this is the cohomological core of the
restricted lower-tail bound.
Source: Stacks Project, Tags 0D64, 01E1 and 03FD.
(blueprint: lem-sc-affine-basis-restricted-lower-tail-local-bound-aux).
The proof follows the restriction, truncation, and module/abelian cohomology
comparison argument in the parent node. -/
theorem affineBasisRestrictedLowerTail_local_vanishing
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wV} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    (F : CochainComplex X.Modules ℤ)
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1)))
    (a : ℤ) (U : Opens V.toScheme) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p)
    (q : ℤ) (hq : q < 0) :
    IsZero ((RingedSpace.openModuleCohomology V.toScheme.toRingedSpace p U).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) q).obj
        ((schemeOpenRestriction X V).mapDerivedCategory.obj
          (((DerivedCategory.TStructure.t
            (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).truncLT a).obj
            (DerivedCategory.Q.obj F))))) := by
  let R := schemeOpenRestriction X V
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let E : DerivedCategory.{wC} C := DerivedCategory.Q.obj F
  let t : CategoryTheory.Triangulated.TStructure (DerivedCategory.{wC} C) :=
    DerivedCategory.TStructure.t (C := C)
  let K := (t.truncLT a).obj E
  let H := DerivedCategory.homologyFunctor C q
  let S := RingedSpace.openModuleCohomology V.toScheme.toRingedSpace p U
  let : S.Additive := by
    dsimp [S, RingedSpace.openModuleCohomology]
    infer_instance
  let eR := (R.mapDerivedCategoryHomologyFunctorIso q).symm.app K
  apply IsZero.of_iso _ (S.mapIso eR)
  by_cases hqa : q < a
  · have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app
      E a q hqa
    let eH := asIso (H.map ((t.truncLTι a).app E)) ≪≫
      (DerivedCategory.homologyFunctorFactors C q).app F
    apply IsZero.of_iso _ (S.mapIso (R.mapIso eH))
    -- Compare sections on U after restriction with sections on its image in X.
    let W := V.ι ''ᵁ U
    have hW : IsAffineOpen W := hU.image_of_isOpenImmersion V.ι
    have hWV : W ≤ V := by
      simpa [W] using (Scheme.Hom.image_le_opensRange V.ι U)
    let M := F.homology q
    have eCoh : Nonempty ((S.obj (R.obj M)) ≅
        (RingedSpace.openModuleCohomology X.toRingedSpace p W).obj M) := by
      let : EnoughInjectives X.Modules :=
        (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
      let : EnoughInjectives V.toScheme.Modules :=
        (RingedSpace.moduleSheaves_abelian_enoughInjectives V.toScheme.toRingedSpace).2
      let I := injectiveResolution M
      have hinj (n : ℕ) : Injective (R.obj (I.cocomplex.X n)) := by
        have h := (RingedSpace.restrict_injectiveResolution
          X.toRingedSpace V M I).2 n
        exact (Scheme.Modules.overEquiv V).functor.injective_obj_of_injective h
      let e₀ := (HomologicalComplex.singleMapHomologicalComplex R (.up ℕ) 0).app M
      let J : InjectiveResolution (R.obj M) :=
        { cocomplex := (R.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
          injective := hinj
          ι := e₀.inv ≫ (R.mapHomologicalComplex (.up ℕ)).map I.ι
          quasiIso := by infer_instance }
      let T := RingedSpace.openModuleSections V.toScheme.toRingedSpace U
      let T' := RingedSpace.openModuleSections X.toRingedSpace W
      let : T.Additive := RingedSpace.openModuleSections_additive _ _
      let : T'.Additive := RingedSpace.openModuleSections_additive _ _
      let eS : Scheme.Modules.restrictFunctor V.ι ⋙ T ≅ T' :=
        NatIso.ofComponents (fun (N : X.Modules) ↦
          Scheme.Modules.restrictAppIso V.ι N U)
          (by
            intro N N' f
            change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
            simp only [Category.comp_id, Category.id_comp]
            rfl)
      let eSections : R ⋙ T ≅ T' :=
        Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv V) T ≪≫ eS
      let eComplex := (NatIso.mapHomologicalComplex eSections (.up ℕ)).app I.cocomplex
      exact ⟨J.isoRightDerivedObj T p ≪≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) p).mapIso eComplex ≪≫
        (I.isoRightDerivedObj T' p).symm⟩
    obtain ⟨eCoh⟩ := eCoh
    obtain ⟨eAb⟩ := nonempty_openModuleCohomology_addEquiv_restrict_H X M W p
    have hM : Subsingleton ((M.restrict W.ι).H p) := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
      exact hhomology W hW hWV q r
    have hS : Subsingleton ((RingedSpace.openModuleCohomology X.toRingedSpace p W).obj M) :=
      eAb.toEquiv.subsingleton
    exact (AddCommGrpCat.isZero_of_subsingleton _).of_iso eCoh
  · have hK : IsZero (H.obj K) :=
      DerivedCategory.isZero_of_isLE K (a - 1) q (by omega)
    exact S.map_isZero (R.map_isZero hK)

end AlgebraicGeometry
