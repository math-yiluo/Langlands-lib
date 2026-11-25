/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Field.ULift
import all WeilConjectures.Algebra.Homology.ScalarHomCancellation.ScalarHomTensorCancellation
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Field.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldLocalSections
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The field-module calculation for a principal residue quotient

## References

* Stacks Project, Modules on Sites, Tags 0GMW (tensor and sheafification) and 03EI (exact
  sheafification)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ResidueModule

private noncomputable def residuePresheaf
    (T : Scheme.{u}) (A : Type u) [CommRing A] (r : A)
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (hM : ∀ (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (proEtaleModuleScalarUnit T A).app U (ULift.up r) • x = 0) :
    PresheafOfModules.{u + 1} ((Functor.const T.ProEtᵒᵖ).obj
      (RingCat.of (ULift.{u + 1, u} (A ⧸ Ideal.span {r})))) := by
  let η := proEtaleModuleScalarUnit T A
  letI amod (U : T.ProEtᵒᵖ) : Module A (M.val.obj U) :=
    Module.compHom _ (((η.app U).hom).comp ULift.ringEquiv.symm.toRingHom)
  let hk (U : T.ProEtᵒᵖ) : Module.IsTorsionBy A (M.val.obj U) r := hM U
  letI bmod (U : T.ProEtᵒᵖ) : Module (A ⧸ Ideal.span {r}) (M.val.obj U) :=
    (hk U).module
  letI ubmod (U : T.ProEtᵒᵖ) : Module
      (ULift.{u + 1, u} (A ⧸ Ideal.span {r})) (M.val.obj U) :=
    Module.compHom _ ULift.ringEquiv.toRingHom
  refine
    { obj U := ModuleCat.of (ULift.{u + 1, u} (A ⧸ Ideal.span {r})) (M.val.obj U)
      map {U V} f := ModuleCat.ofHom
        { toFun := M.val.map f
          map_add' := map_add _
          map_smul' := ?_ }
      map_id U := ?_
      map_comp f g := ?_ }
  · intro b x
    obtain ⟨b⟩ := b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    change M.val.map f (η.app U (ULift.up a) • x) =
      η.app V (ULift.up a) • M.val.map f x
    rw [M.val.map_smul]
    congr 1
    exact ConcreteCategory.congr_hom (η.naturality f).symm (ULift.up a)
  · ext x
    exact ConcreteCategory.congr_hom (M.val.map_id U) x
  · ext x
    exact M.val.map_comp_apply f g x

private theorem factor_module
    (T : Scheme.{u}) (A : Type u) [CommRing A] (r : A)
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (hM : ∀ (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (proEtaleModuleScalarUnit T A).app U (ULift.up r) • x = 0) :
    let B := A ⧸ Ideal.span {r}
    let c := (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.mk (Ideal.span {r}))))
    let α := (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c
    ∃ MB : proEtaleRingModules T (proEtaleConstantRing T B),
      Nonempty ((SheafOfModules.restrictScalars α).obj MB ≅ M) := by
  let B := A ⧸ Ideal.span {r}
  let J := ProEt.topology T
  let η := proEtaleModuleScalarUnit T B
  have : Presheaf.IsLocallyInjective J η :=
    (proEtaleConstantRingUnit_locallyBijective T B).1
  have : Presheaf.IsLocallySurjective J η :=
    (proEtaleConstantRingUnit_locallyBijective T B).2
  let F := residuePresheaf T A r M hM
  let H := (SheafOfModules.toSheaf _).obj M
  let φ : F.presheaf ⟶ H.obj := 𝟙 H.obj
  have : IsIso φ := by
    change IsIso (𝟙 H.obj)
    infer_instance
  let MB := PresheafOfModules.sheafify η (M₀ := F) (A := H) φ
  let c := (constantSheaf J CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.mk (Ideal.span {r}))))
  let α := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c
  let N := (SheafOfModules.restrictScalars α).obj MB
  let ηA := proEtaleModuleScalarUnit T A
  have : Presheaf.IsLocallySurjective J ηA :=
    (proEtaleConstantRingUnit_locallyBijective T A).2
  have hscalar (U : T.ProEtᵒᵖ) (a : ULift.{u + 1, u} A) (x : M.val.obj U) :
      α.hom.app U (ηA.app U a) • (show MB.val.obj U from x) =
        ηA.app U a • x := by
    have hc : α.hom.app U (ηA.app U a) =
        η.app U (ULift.up (Ideal.Quotient.mk (Ideal.span {r}) a.down)) := by
      have t := toSheafify_naturality J ((Functor.const T.ProEtᵒᵖ).map
        (CommRingCat.ofHom
          (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.mk (Ideal.span {r})))))
      exact ConcreteCategory.congr_hom (NatTrans.congr_app t U).symm a
    rw [hc]
    have hl := ((PresheafOfModules.toSheafify η (M₀ := F) (A := H)
      φ).app U).hom.map_smul
        (ULift.up (Ideal.Quotient.mk (Ideal.span {r}) a.down)) x
    exact hl.symm
  let f₀ : (PresheafOfModules.restrictScalars ηA).obj N.val ⟶
      (PresheafOfModules.restrictScalars ηA).obj M.val :=
    PresheafOfModules.homMk (𝟙 H.obj) (fun U a x ↦ hscalar U a x)
  let f : N ⟶ M := ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    ηA M.isSheaf).symm f₀⟩
  have hf : IsIso f := by
    rw [← isIso_iff_of_reflects_iso f (SheafOfModules.toSheaf _)]
    change IsIso (𝟙 H)
    infer_instance
  exact ⟨MB, ⟨asIso f⟩⟩

private noncomputable def extensionFunctor
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ⟶ S) :
    SheafOfModules.{u + 1} ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤
      SheafOfModules.{u + 1} ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
  let E₀ : SheafOfModules.{u + 1} ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤
      PresheafOfModules.{u + 1} (S.obj ⋙ forget₂ CommRingCat RingCat) :=
    { obj := SheafOfModules.changeOfRingsPresheaf c
      map := fun a ↦ SheafOfModules.ScalarHomCancellation.cancellationChangeMap c a
      map_id := by
        intro M
        ext U
        simp [SheafOfModules.ScalarHomCancellation.cancellationChangeMap]
        rfl
      map_comp := by
        intro M N P a b
        ext U
        simp [SheafOfModules.ScalarHomCancellation.cancellationChangeMap]
        rfl }
  E₀ ⋙ PresheafOfModules.sheafification (𝟙 _)

private theorem extensionFunctor_additive
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ⟶ S) :
    (extensionFunctor c).Additive := by
  have : (PresheafOfModules.sheafification (J := J)
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 _)).left_adjoint_additive
  have hscalar (U : Cᵒᵖ) :
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      (c.hom.app U).hom).left_adjoint_additive
  constructor
  intro M N f g
  have h : SheafOfModules.ScalarHomCancellation.cancellationChangeMap c (f + g) =
      SheafOfModules.ScalarHomCancellation.cancellationChangeMap c f +
        SheafOfModules.ScalarHomCancellation.cancellationChangeMap c g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app U).hom).map_add
  change (PresheafOfModules.sheafification (𝟙 _)).map
    (SheafOfModules.ScalarHomCancellation.cancellationChangeMap c (f + g)) =
      (PresheafOfModules.sheafification (𝟙 _)).map
        (SheafOfModules.ScalarHomCancellation.cancellationChangeMap c f) +
      (PresheafOfModules.sheafification (𝟙 _)).map
        (SheafOfModules.ScalarHomCancellation.cancellationChangeMap c g)
  rw [h, Functor.map_add]

end ResidueModule

set_option synthInstance.maxSize 2048 in
/-- Tensor cohomology vanishing passes from the constant principal residue quotient to
any sheaf annihilated by its generator. This concerns ordinary termwise tensor of an
arbitrary, possibly unbounded, complex, in one degree. No K-flatness or nilpotence
hypothesis is needed here. -/
theorem proEtale_residue_module_tensor_homology
    (T : Scheme.{u}) (A : Type u) [CommRing A] (r : A)
    (hr : (Ideal.span {r}).IsMaximal)
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (hM : ∀ (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app U
          (ULift.up r) • x = 0)
    (i : ℤ) :
    letI := SheafOfModules.monoidalCategory (proEtaleConstantRing T A)
    let B := A ⧸ Ideal.span {r}
    let RB := proEtaleConstantRing T B
    let SB := (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RB
    let α := (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk (Ideal.span {r})))))
    let N := (SheafOfModules.restrictScalars.{u + 1} α).obj (SheafOfModules.unit SB)
    IsZero ((((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P).homology i) →
    IsZero ((((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P).homology i) := by
  classical
  let J := ProEt.topology T
  let B := A ⧸ Ideal.span {r}
  have : (Ideal.span {r}).IsMaximal := hr
  let : Field B := Ideal.Quotient.field _
  let R := proEtaleConstantRing T A
  let RB := proEtaleConstantRing T B
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory RB
  let := SheafOfModules.cochainModulesPreadditive R
  let := SheafOfModules.cochainModulesPreadditive RB
  let c : R ⟶ RB := (constantSheaf J CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.mk (Ideal.span {r}))))
  let α := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c
  let U := SheafOfModules.restrictScalars.{u + 1} α
  let N := U.obj (SheafOfModules.unit _)
  change IsZero ((((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P).homology i) → _
  intro hz
  obtain ⟨MB, ⟨eM⟩⟩ := ResidueModule.factor_module T A r M hM
  let E := ResidueModule.extensionFunctor c
  have : E.Additive := ResidueModule.extensionFunctor_additive c
  have hU := SheafOfModules.restrict_exact.{u + 1, u, u + 1, u + 1} c
  have : PreservesFiniteLimits U := hU.1
  have : PreservesFiniteColimits U := hU.2
  obtain ⟨e, he⟩ := SheafOfModules.ScalarHomCancellation.exists_changeOfRings_tensorCancellation c
  let comparison (L : proEtaleRingModules T RB) :
      E ⋙ tensorLeft L ⋙ U ≅ tensorLeft (U.obj L) :=
    NatIso.ofComponents (e L) (by
      intro X Y f
      change U.map (L ◁ E.map f) ≫ (e L Y).hom =
        (e L X).hom ≫ (U.obj L ◁ f)
      have h := he (𝟙 L) f
      change U.map ((𝟙 L) ⊗ₘ E.map f) ≫ (e L Y).hom =
        (e L X).hom ≫ (U.map (𝟙 L) ⊗ₘ f) at h
      rw [U.map_id] at h
      erw [id_tensorHom, id_tensorHom] at h
      exact h)
  let D := P.sc i
  have hDN : (D.map (tensorLeft N)).Exact := by
    apply ShortComplex.exact_of_iso
      (D.mapNatIso (BraidedCategory.tensorLeftIsoTensorRight N).symm)
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hz
  let regular := SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RB)
  let unitComparison : E ⋙ U ≅ tensorLeft N :=
    (Functor.isoWhiskerLeft E (Functor.isoWhiskerRight
      (leftUnitorNatIso (proEtaleRingModules T RB)).symm U)) ≪≫ comparison regular
  have hDEU : ((D.map E).map U).Exact :=
    ShortComplex.exact_of_iso (D.mapNatIso unitComparison.symm) hDN
  have : U.Faithful := ⟨by
    intro L K f g h
    ext V x
    exact congrArg (fun k ↦ (k.val.app V).hom x) h⟩
  have hDE : (D.map E).Exact :=
    ((D.map E).exact_map_iff_of_faithful U).1 hDEU
  have hflat := SheafOfModules.isFlat_constantFieldModule.{u + 1, u, u + 1, u + 1} J
    (ULift.{u + 1, u} B) MB
  have hright : exactFunctor _ _ (tensorRight MB) :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso RB MB) hflat
  have : PreservesFiniteLimits (tensorRight MB) := hright.1
  have : PreservesFiniteColimits (tensorRight MB) := hright.2
  have hDEM : ((D.map E).map (tensorLeft MB)).Exact :=
    ShortComplex.exact_of_iso
      ((D.map E).mapNatIso (BraidedCategory.tensorLeftIsoTensorRight MB).symm)
      (hDE.map (tensorRight MB))
  have hDUM : (D.map (tensorLeft (U.obj MB))).Exact :=
    ShortComplex.exact_of_iso (D.mapNatIso (comparison MB)) (hDEM.map U)
  have hDM : (D.map (tensorLeft M)).Exact :=
    ShortComplex.exact_of_iso
      (D.mapNatIso ((curriedTensor _).mapIso eM)) hDUM
  have hDM' : (D.map (tensorRight M)).Exact :=
    ShortComplex.exact_of_iso
      (D.mapNatIso (BraidedCategory.tensorLeftIsoTensorRight M)) hDM
  exact HomologicalComplex.ExactAt.isZero_homology hDM'

end AlgebraicGeometry.Scheme
