/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.Topology.RestrictInjectiveResolution
import WeilConjectures.AlgebraicGeometry.ModuleAbelianZariskiCohomology

/-! # Open module cohomology and cohomology of the restricted abelian sheaf

Source: Stacks Project, Tags 01E1 and 03FD
(blueprint: lem-pqf-open-module-cohomology-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Module-derived sections over an open agree with abelian-sheaf cohomology of the
restricted module on its induced open subscheme. No affine or quasi-coherence
hypothesis is needed, and degree zero is included.

Source: Stacks Project, Cohomology, Tag 01E1 (2), and Cohomology on Sites, Tag 03FD
(blueprint: lem-pqf-open-module-cohomology-comparison).

Proof:
1. Choose an injective module resolution I of F. By
lem-sc-ringed-space-restrict-injective-resolution, I restricted to U is an injective
resolution of F.over U. Transport this resolution through Scheme.Modules.overEquiv U;
Mathlib's overFunctorEquiv identifies its augmentation and terms with restriction
along U.ι. Equivalences preserve injectivity and exactness.
2. The sections of each term on U are precisely the global sections of its restriction.
These identifications commute with the differentials, by naturality of restriction of
sections. Thus the two complexes of additive groups are isomorphic. The definition of
openModuleCohomology, Mathlib's InjectiveResolution.isoRightDerivedObj, and the
resolution computation of moduleCohomology give the
isomorphism between open cohomology and the underlying additive group of module
cohomology of the restricted module.
The exact forgetful functor from modules over the global ring to additive groups
preserves this homology, since it preserves kernels and cokernels.
3. Apply lem-sc-module-abelian-zariski-cohomology to the scheme U.toScheme and the
restricted module. Injective module sheaves are acyclic after forgetting to abelian
sheaves, as in Stacks 03FD; they need not be injective as abelian sheaves. Hence the
abelian cohomology is computed by the same section complex. At the terminal open,
Ext from the sheafified free abelian representable is Ext from the constant integer
sheaf, by the constant-sheaf adjunction; this identifies Sheaf.H' at top with Sheaf.H.
The latter is Scheme.Modules.H by definition. Compose the additive isomorphisms.
For the empty open both section complexes are zero. In degree zero the comparison is
ordinary restriction of sections, so no positive-degree assumption is required. -/
theorem nonempty_openModuleCohomology_addEquiv_restrict_H (X : Scheme.{u})
    (F : X.Modules) (U : X.Opens) (p : ℕ) :
    Nonempty (((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj F) ≃+
      ((Scheme.Modules.restrictFunctor U.ι).obj F).H p) := by
  let G := (Scheme.Modules.restrictFunctor U.ι).obj F
  let Y := U.toScheme
  have eOpen : Nonempty
      ((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj F ≅
        (forget₂ (ModuleCat.{u}
          ((moduleRings Y.toRingedSpace).obj.obj (Opposite.op ⊤))) AddCommGrpCat).obj
          ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj G)) := by
    let : EnoughInjectives X.Modules :=
      (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
    let : EnoughInjectives Y.Modules :=
      (RingedSpace.moduleSheaves_abelian_enoughInjectives Y.toRingedSpace).2
    let I := injectiveResolution F
    let R := Scheme.Modules.restrictFunctor U.ι
    let : R.Additive := ⟨rfl⟩
    let E := (Scheme.Modules.overEquiv U).functor
    let O := SheafOfModules.overFunctor X.ringCatSheaf U
    let eR := Scheme.Modules.overFunctorEquiv U
    obtain ⟨hlim, hcolim, _⟩ := open_restriction_adjunction_exact X.toRingedSpace U
    let : CategoryTheory.Limits.PreservesFiniteLimits O := hlim
    let : CategoryTheory.Limits.PreservesFiniteColimits O := hcolim
    let : CategoryTheory.Limits.PreservesFiniteLimits R :=
      CategoryTheory.Limits.preservesFiniteLimits_of_natIso eR
    let : CategoryTheory.Limits.PreservesFiniteColimits R :=
      CategoryTheory.Limits.preservesFiniteColimits_of_natIso eR
    have hinj (n : ℕ) : Injective (R.obj (I.cocomplex.X n)) := by
      have h := (RingedSpace.restrict_injectiveResolution X.toRingedSpace U F I).2 n
      exact Injective.of_iso (eR.app (I.cocomplex.X n))
        (E.injective_obj_of_injective h)
    let e₀ := (HomologicalComplex.singleMapHomologicalComplex R (.up ℕ) 0).app F
    let J : InjectiveResolution G :=
      { cocomplex := (R.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
        injective := hinj
        ι := e₀.inv ≫ (R.mapHomologicalComplex (.up ℕ)).map I.ι
        quasiIso := by infer_instance }
    let Q := forget₂ (ModuleCat.{u}
      ((moduleRings Y.toRingedSpace).obj.obj (Opposite.op ⊤))) AddCommGrpCat
    let S := RingedSpace.globalSectionsFunctor Y.toRingedSpace
    let T := RingedSpace.openModuleSections X.toRingedSpace U
    let : S.Additive := RingedSpace.globalSectionsFunctor_additive Y.toRingedSpace
    let : Q.Additive := inferInstance
    let : T.Additive := RingedSpace.openModuleSections_additive X.toRingedSpace U
    let eSections : T ≅ R ⋙ S ⋙ Q :=
      NatIso.ofComponents (fun (M : X.Modules) ↦ by
        change Γ(M, U) ≅ Γ(Scheme.Modules.restrict M U.ι, ⊤)
        exact ((Scheme.Modules.toPresheaf X).obj M |>.mapIso (eqToIso (by simp)).op) ≪≫
          (Scheme.Modules.restrictAppIso U.ι M ⊤).symm)
        (by
          intro M N f
          change ((Scheme.Modules.toPresheaf X).map f).app (Opposite.op U) ≫
              ((Scheme.Modules.toPresheaf X).obj N).map (eqToHom (by simp : U.ι ''ᵁ ⊤ = U)).op =
            ((Scheme.Modules.toPresheaf X).obj M).map (eqToHom (by simp : U.ι ''ᵁ ⊤ = U)).op ≫
              ((Scheme.Modules.toPresheaf X).map f).app (Opposite.op (U.ι ''ᵁ ⊤))
          exact ((Scheme.Modules.toPresheaf X).map f).naturality _ |>.symm)
    let eComplex := (NatIso.mapHomologicalComplex eSections (.up ℕ)).app I.cocomplex
    let K := (S.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
    let eHomology := (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) p).mapIso
      eComplex
    let eForget := (K.sc p).mapHomologyIso Q
    exact ⟨I.isoRightDerivedObj T p ≪≫ eHomology ≪≫ eForget ≪≫
      Q.mapIso (J.isoRightDerivedObj S p).symm⟩
  obtain ⟨e₁⟩ := eOpen
  obtain ⟨e₂⟩ := module_cohomology_iso_underlying_abelian Y G p
  let A := (SheafOfModules.toSheaf Y.ringCatSheaf).obj G
  let e : yoneda.obj (⊤ : Y.Opens) ⋙ AddCommGrpCat.free ≅
      (Functor.const Y.Opensᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    NatIso.ofComponents (fun V ↦ by
      letI : Unique (V.unop ⟶ (⊤ : Y.Opens)) :=
        ⟨⟨homOfLE le_top⟩, fun _ ↦ Subsingleton.elim _ _⟩
      exact ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro V W f
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro a
        simp [FreeAbelianGroup.uniqueEquiv])
  let eS := (presheafToSheaf (Opens.grothendieckTopology Y)
    AddCommGrpCat).mapIso e
  let eH : CategoryTheory.Sheaf.H' A p ⊤ ≃+ CategoryTheory.Sheaf.H.{u} A p :=
    (CategoryTheory.Abelian.Ext.precompAddEquiv eS A p).symm
  exact ⟨(e₁ ≪≫ e₂).addCommGroupIsoToAddEquiv.trans eH⟩

end AlgebraicGeometry
