/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ResolutionOpenComparisonMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.ResolutionSectionsHomologyScalar
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.Linear

/-! # The fixed comparison intertwines the scalar endomorphisms.
Source: Stacks Project, Tags 01E1 and 01E4.
(blueprint: lem-pc-resolution-open-scalar-core). -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

private lemma moduleCat_smul_asHom_apply {R : Type u} [Ring R]
    (M : ModuleCat.{u} R) (r : R) (x : M) : (M.smul r).asHom x = r • x := rfl

/-- The fixed comparison intertwines the scalar endomorphisms.
Source: Stacks Project, Tags 01E1 and 01E4.
(blueprint: lem-pc-resolution-open-scalar-core).

Proof: Multiplication by b on each term of the restricted resolution lifts G.smulHom b by naturality
of smulHom and the augmentation. Naturality of isoRightDerivedObj identifies its induced
homology map with the cohomology map. The fixed section comparison is semilinear by
resolutionSectionsHomology_scalar: its ring map equals f.app W followed by topIso.inv, by the
canonical chart cancellation. Use the same computation with a^n and the fact that this ring
map preserves powers. The exact evaluation and forgetful homology comparisons commute with
these endomorphisms. Thus every arrow in the displayed fixed comparison intertwines b^n with
a^n, yielding the equality. For n=0 the maps are identities; degree zero and empty opens use
the same comparisons. -/
theorem resolution_open_scalar_core {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (a : Γ(T, W))
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let Y := (f ⁻¹ᵁ W).toScheme
    let : CommRing (Y.ringCatSheaf.obj.obj (op ⊤)) :=
    inferInstanceAs (CommRing Γ(Y, ⊤))
  let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
    let c := resolutionOpenComparison f F I q W R
    ∀ (n : ℕ) (x : P.obj (op W)),
      (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).map
        (G.smulHom (b ^ n)) (c x) = c (a ^ n • x) := by
  dsimp only
  intro n x
  let Y := (f ⁻¹ᵁ W).toScheme
  let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
  let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
  let K := ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let A := RingedSpace.globalSectionsComplex R.resolution
  let B := ((SheafOfModules.forget T.ringCatSheaf).mapHomologicalComplex (.up ℕ)).obj K
  let E := PresheafOfModules.toPresheaf T.ringCatSheaf.obj ⋙
    (evaluation T.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) q
  let eA := (A.sc q).mapHomologyIso (forget₂ _ AddCommGrpCat.{u})
  let eB := (B.sc q).mapHomologyIso E
  let S := RingedSpace.openModuleSections Y.toRingedSpace ⊤
  let : S.Additive := RingedSpace.openModuleSections_additive Y.toRingedSpace ⊤
  let eR := R.resolution.isoRightDerivedObj S q
  let raw := H.map R.sections.hom ≫ eB.hom
  let phi : R.resolution.cocomplex ⟶ R.resolution.cocomplex :=
    { f := fun i ↦ (R.resolution.cocomplex.X i).smulHom (b ^ n)
      comm' := fun i j _ ↦ smulHom_naturality (R.resolution.cocomplex.d i j) (b ^ n) }
  have hphi : R.resolution.ι.f 0 ≫ phi.f 0 =
      G.smulHom (b ^ n) ≫ R.resolution.ι.f 0 :=
    (smulHom_naturality (R.resolution.ι.f 0) (b ^ n)).symm
  have hnat := R.resolution.isoRightDerivedObj_hom_naturality
    (G.smulHom (b ^ n)) R.resolution phi hphi S q
  have ht (y : A.homology q) :
      (eA.inv ≫ raw) ((b ^ n) • y) = a ^ n • (show (sectionCohomologyPresheaf K q).obj (op W) from
        (eA.inv ≫ raw) y) := by
    have hs := resolutionSectionsHomology_scalar f F I q W R (a ^ n) y
    let h := f.resLE W (f ⁻¹ᵁ W) le_rfl ≫ W.toSpecΓ
    have hb : (Scheme.ΓSpecIso Γ(T, W)).inv ≫ h.appTop ≫
        (f ⁻¹ᵁ W).topIso.hom = f.app W := by
      simp only [h, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
        Category.assoc, Iso.inv_hom_id_assoc, Scheme.Hom.appTop,
        Scheme.Hom.resLE_app_top, Iso.inv_hom_id,
        Category.comp_id, Scheme.Hom.appLE]
      simp only [homOfLE_refl, op_id]
      rw [X.presheaf.map_id, Category.comp_id]
    have hb' : (Scheme.ΓSpecIso Γ(T, W)).inv ≫ h.appTop =
        f.app W ≫ (f ⁻¹ᵁ W).topIso.inv := by
      rw [← hb]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    dsimp only at hs
    dsimp only [h] at hb'
    simp only [hb', map_pow] at hs
    simpa only [eA, A, raw, H, eB, B, E, K, b, ConcreteCategory.comp_apply] using hs
  have hh (y : (H.obj ((S.mapHomologicalComplex (.up ℕ)).obj
      R.resolution.cocomplex))) :
      raw ((S.mapHomologicalComplex (.up ℕ) ⋙ H).map phi y) =
        a ^ n • (show (sectionCohomologyPresheaf K q).obj (op W) from raw y) := by
    have hphiSC :
        (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (.up ℕ) q).map
          ((S.mapHomologicalComplex (.up ℕ)).map phi) =
        (A.sc q).mapNatTrans (ModuleCat.smulNatTrans _ (b ^ n)).asHom := by
      apply ShortComplex.hom_ext <;> ext z <;>
        exact smulHom_app_top_apply _ (b ^ n) z
    have hphiH : (S.mapHomologicalComplex (.up ℕ) ⋙ H).map phi =
        eA.hom ≫ ((A.homology q).smul (b ^ n)).asHom ≫ eA.inv := by
      exact (congrArg (fun g ↦ ShortComplex.homologyMap g) hphiSC).trans
        (ShortComplex.homologyMap_mapNatTrans (A.sc q)
          (ModuleCat.smulNatTrans _ (b ^ n)).asHom)
    have hy := ConcreteCategory.congr_hom hphiH y
    simp only [ConcreteCategory.comp_apply] at hy
    have hy' := hy.trans (congrArg eA.inv
      (moduleCat_smul_asHom_apply (A.homology q) (b ^ n) (eA.hom y)))
    calc
      raw ((S.mapHomologicalComplex (.up ℕ) ⋙ H).map phi y) =
          (eA.inv ≫ raw) ((b ^ n) • (show A.homology q from eA.hom y)) := by
        exact congrArg raw hy'
      _ = a ^ n • (show (sectionCohomologyPresheaf K q).obj (op W) from
          (eA.inv ≫ raw) (eA.hom y)) := ht _
      _ = a ^ n • (show (sectionCohomologyPresheaf K q).obj (op W) from raw y) := by
        simp
        rfl
  have hc (z : (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj G) :
      (eR.hom ≫ raw) ((RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).map
        (G.smulHom (b ^ n)) z) = a ^ n • (show (sectionCohomologyPresheaf K q).obj (op W) from
        (eR.hom ≫ raw) z) := by
    have hz := ConcreteCategory.congr_hom hnat z
    change eR.hom ((RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).map
      (G.smulHom (b ^ n)) z) = (S.mapHomologicalComplex (.up ℕ) ⋙ H).map phi
        (eR.hom z) at hz
    change raw (eR.hom _) = _
    erw [hz]
    exact hh _
  apply (resolutionOpenComparison f F I q W R).symm.injective
  simp only [AddEquiv.symm_apply_apply]
  change (eR.hom ≫ raw) _ = a ^ n • x
  rw [hc]
  change a ^ n • ((resolutionOpenComparison f F I q W R).symm
    ((resolutionOpenComparison f F I q W R) x)) = _
  simp only [AddEquiv.symm_apply_apply]


end AlgebraicGeometry.Scheme.Modules
