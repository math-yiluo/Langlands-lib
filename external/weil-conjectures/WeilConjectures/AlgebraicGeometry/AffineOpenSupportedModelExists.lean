/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
/-! # Affine derived preimages of restricted quasi-coherent targets

Source: Stacks Project, Tag 06Z0, with exact restriction to an affine open.
(blueprint: new-affine-open-supported-model-exists).
-/
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency true in

/-- The inverse affine derived equivalence supplies a model of the restricted target.
Source: Stacks Project, Tag 06Z0, and exact open and affine-site transport.
(blueprint: new-affine-open-supported-model-exists).

Proof: The homology shift isomorphism identifies every cohomology sheaf of E'[k]
with one of E', hence it is quasi-coherent. Exact open restriction and the over-site
module equivalence preserve quasi-coherence. Restrict further along the inverse
of the affine chart isoSpec; restriction along an isomorphism is an exact equivalence
and preserves quasi-coherent sheaves, so the result K on Spec A is quasi-coherent.
Use the inverse of the affine derived equivalence on K to obtain M. Its counit,
followed by the canonical affine-site transport, identifies the transported derived
tilde of M with the restriction of E'[k]. The comparisons on module complexes for
this composite and for F give an isomorphism after precomposition with Q. The
universal property of localization lifts that natural isomorphism to D(A).
Its component at M gives the required isomorphism. Support is not used. The same
construction works for the empty affine open and arbitrary, unbounded E'. -/
theorem affine_open_supported_model_exists
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E' : schemeDerivedQCohCategory X)
    (U : X.Opens) (hU : IsAffineOpen U) (k : ℤ)
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} (X.sheaf.obj.obj (op U)))]
    (F : DerivedCategory (ModuleCat.{u} (X.sheaf.obj.obj (op U))) ⥤
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)))
    (hF : Nonempty (DerivedCategory.Q ⋙ F ≅
      (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q)) :
    ∃ M : DerivedCategory (ModuleCat.{u} (X.sheaf.obj.obj (op U))),
      Nonempty (F.obj M ≅
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
          (E'.obj⟦k⟧)) := by
  classical
  let A := X.presheaf.obj (op U)
  let S := SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)
  let D := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let hS := HasDerivedCategory.standard S
  let a := Modules.restrictFunctor hU.isoSpec.hom
  let b := Modules.restrictFunctor hU.isoSpec.inv
  let e : S ≌ (U : Scheme.{u}).Modules := CategoryTheory.Equivalence.mk a b
    ((Modules.restrictFunctorId).symm ≪≫
      Modules.restrictFunctorCongr (by simp [A]) ≪≫
      Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
    ((Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId)
  let t : S ≌ D := e.trans (Modules.overEquiv U).symm
  have : HasBinaryBiproducts S := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasBinaryBiproducts D := HasBinaryBiproducts.of_hasBinaryProducts
  have : PreservesBinaryBiproducts t.functor :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : PreservesBinaryBiproducts t.inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : t.functor.Additive := Functor.additive_of_preservesBinaryBiproducts _
  have : t.inverse.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let td : DerivedCategory S ⥤ DerivedCategory D := t.functor.mapDerivedCategory
  let ti : DerivedCategory D ⥤ DerivedCategory S := t.inverse.mapDerivedCategory
  have : PreservesFiniteLimits (t.inverse ⋙ t.functor) :=
    comp_preservesFiniteLimits t.inverse t.functor
  have : PreservesFiniteColimits (t.inverse ⋙ t.functor) :=
    comp_preservesFiniteColimits t.inverse t.functor
  let counit : ti ⋙ td ≅ 𝟭 (DerivedCategory D) :=
    Functor.mapDerivedCategoryCompIso t.inverse t.functor ≪≫
      Functor.mapDerivedCategoryNatIso t.counitIso ≪≫ Functor.mapDerivedCategoryIdIso D
  let r := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let K₀ := E'.obj⟦k⟧
  have hK₀ : schemeDerivedQCohProperty X K₀ := by
    intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      (((DerivedCategory.homologyFunctor _ 0).shiftIso k n (k + n) rfl).app E'.obj).symm
      (E'.property (k + n))
  let H := r ⋙ t.inverse
  have : PreservesFiniteLimits H := comp_preservesFiniteLimits r t.inverse
  have : PreservesFiniteColimits H := comp_preservesFiniteColimits r t.inverse
  let c : H ≅ Modules.restrictFunctor (hU.isoSpec.inv ≫ U.ι) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Modules.overFunctorEquiv U) b ≪≫
      (Modules.restrictFunctorComp hU.isoSpec.inv U.ι).symm
  let K := H.mapDerivedCategory.obj K₀
  have hK : schemeDerivedQCohProperty (Spec A) K := by
    intro n
    let q := (H.mapDerivedCategoryHomologyFunctorIso n).app K₀
    have := hK₀ n
    have hq : (H.obj ((DerivedCategory.homologyFunctor _ n).obj K₀)).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (moduleRings (Spec A).toRingedSpace)).prop_of_iso
        (c.app _).symm (Modules.isQuasicoherent_restrictFunctor _ _)
    exact (SheafOfModules.isQuasicoherent (moduleRings (Spec A).toRingedSpace)).prop_of_iso
      q hq
  let Kq : schemeDerivedQCohCategory (Spec A) := ⟨K, hK⟩
  let hA : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    ‹HasDerivedCategory.{u + 1} (ModuleCat.{u} (X.sheaf.obj.obj (op U)))›
  obtain ⟨eq, ⟨ce⟩, _⟩ :=
    @exists_affineQCohDerivedEquivalence_core.{u, u + 1, u + 1} A inferInstance
      hA hS
  let M := eq.inverse.obj Kq
  let j := (schemeDerivedQCohProperty (Spec A)).ι
  let G : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory D :=
    (eq.functor ⋙ j) ⋙ td
  let T : ModuleCat.{u} A ⥤ S := tilde.functor A
  have : T.Additive := inferInstanceAs (tilde.functor A).Additive
  let : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let ft : T ⋙ t.functor ≅ affinePerfectSheafification X U hU := Iso.refl _
  have : (affinePerfectSheafification X U hU).Additive := Functor.additive_of_iso ft
  let cmp : DerivedCategory.Q ⋙ G ≅
      (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ce td ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (T.mapHomologicalComplex (.up ℤ))
        t.functor.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso ft (.up ℤ)) _
  obtain ⟨cf⟩ := hF
  let QA : CochainComplex (ModuleCat.{u} A) ℤ ⥤ DerivedCategory (ModuleCat.{u} A) :=
    DerivedCategory.Q
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)
  have : QA.IsLocalization W := by
    dsimp [QA, W]
    infer_instance
  let : Localization.Lifting QA W (QA ⋙ F) F := ⟨Iso.refl _⟩
  let : Localization.Lifting QA W (QA ⋙ G) G := ⟨Iso.refl _⟩
  let fg : F ≅ G := Localization.liftNatIso QA W
    (QA ⋙ F) (QA ⋙ G) F G (cf ≪≫ cmp.symm)
  refine ⟨M, ⟨?_⟩⟩
  let d : K ≅ ti.obj (r.mapDerivedCategory.obj K₀) :=
    (Functor.mapDerivedCategoryCompIso r t.inverse).symm.app K₀
  exact fg.app M ≪≫ td.mapIso (j.mapIso (eq.counitIso.app Kq) ≪≫ d) ≪≫
    counit.app (r.mapDerivedCategory.obj K₀)

end AlgebraicGeometry.Scheme
