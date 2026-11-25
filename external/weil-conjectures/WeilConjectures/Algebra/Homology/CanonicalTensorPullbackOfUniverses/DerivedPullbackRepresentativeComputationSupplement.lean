/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorComparisonOfUniverses
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Computing derived pullback on K-flat tensor representatives -/

@[expose] public section
set_option autoImplicit false
universe s h w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.CanonicalTensorPullbackOfUniverses
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

private noncomputable abbrev moduleUnderlying
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max s h}) :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max s h})

private theorem moduleUnderlying_finiteLimits
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max s h}) : PreservesFiniteLimits (moduleUnderlying R) := by
  let V := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max s h})
  have : PreservesFiniteLimits (V ⋙ sheafToPresheaf J (Type (max s h))) :=
    show PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{max s h} ⋙
      (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{max s h})) from
        comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits V :=
    preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type (max s h)))
  exact comp_preservesFiniteLimits _ _

private theorem moduleUnderlying_epi
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max s h}) : (moduleUnderlying R).PreservesEpimorphisms := by
  let V := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max s h})
  have : V.PreservesEpimorphisms := ⟨fun {M N} f hf ↦ by
    have : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max s h} f).2 hf
    exact inferInstance⟩
  exact inferInstanceAs ((toSheaf _ ⋙ V).PreservesEpimorphisms)

private theorem algebraicInverseImage_finiteLimits
    {C D : Type s} [Category.{h} C] [Category.{h} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{max s h}} {RI : Sheaf JD CommRingCat.{max s h}}
    (L : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h))) [PreservesFiniteLimits L]
    (I : AlgebraicInverseImage L R RI) : PreservesFiniteLimits I.modules := by
  have := moduleUnderlying_finiteLimits R
  have := moduleUnderlying_finiteLimits RI
  have : PreservesFiniteLimits (moduleUnderlying R ⋙ L) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (I.modules ⋙ moduleUnderlying RI) :=
    preservesFiniteLimits_of_natIso I.moduleUnderlying.symm
  exact preservesFiniteLimits_of_reflects_of_preserves I.modules (moduleUnderlying RI)

private theorem algebraicInverseImage_epi
    {C D : Type s} [Category.{h} C] [Category.{h} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{max s h}} {RI : Sheaf JD CommRingCat.{max s h}}
    (L : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h)))
    (V : Sheaf JD (Type (max s h)) ⥤ Sheaf JC (Type (max s h))) (adj : L ⊣ V)
    (I : AlgebraicInverseImage L R RI) : I.modules.PreservesEpimorphisms := by
  have := moduleUnderlying_epi R
  have := adj.leftAdjoint_preservesColimits
  constructor
  intro M N f hf
  apply (moduleUnderlying RI).epi_of_epi_map
  have : Epi ((moduleUnderlying R ⋙ L).map f) := inferInstance
  have hn := I.moduleUnderlying.hom.naturality f
  have : Epi ((I.modules ⋙ moduleUnderlying RI).map f ≫
      I.moduleUnderlying.hom.app N) := by
    rw [hn]
    infer_instance
  exact (epi_comp_iff_of_isIso _ (I.moduleUnderlying.hom.app N)).1 this

private noncomputable def scalarExtensionPresheaf
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{max s h}} (c : R ⟶ S) :
    SheafOfModules.{max s h} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      PresheafOfModules.{max s h} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj where
  obj M := changeOfRingsPresheaf.{h, s, max s h} c M
  map {M N} f :=
    { app := fun U ↦ (ModuleCat.extendScalars (c.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality.{h, s, max s h} c M f }
  map_id M := by
    ext U : 1
    simp
    rfl
  map_comp f g := by
    ext U : 1
    exact (ModuleCat.extendScalars (c.hom.app U).hom).map_comp _ _

private theorem scalarExtensionPresheaf_additive
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{max s h}} (c : R ⟶ S) :
    (scalarExtensionPresheaf c).Additive where
  map_add {M N} f g := by
    ext U : 1
    have : (ModuleCat.extendScalars (c.hom.app U).hom).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (c.hom.app U).hom).left_adjoint_additive
    simpa only [scalarExtensionPresheaf, add_val, PresheafOfModules.add_app] using
      (ModuleCat.extendScalars (c.hom.app U).hom).map_add
        (f := f.val.app U) (g := g.val.app U)

private noncomputable def scalarExtension
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{max s h}} (c : R ⟶ S) :
    SheafOfModules.{max s h} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{max s h} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) :=
  scalarExtensionPresheaf c ⋙ PresheafOfModules.sheafification.{max s h}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)

private theorem scalarExtension_additive
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{max s h}} (c : R ⟶ S) :
    (scalarExtension c).Additive := by
  have hsheaf : (PresheafOfModules.sheafification.{max s h}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 _)).left_adjoint_additive
  have := scalarExtensionPresheaf_additive c
  dsimp only [scalarExtension]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarExtensionPresheafIdIso
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max s h})
    (M : SheafOfModules.{max s h} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    M.val ≅ (scalarExtensionPresheaf (𝟙 R)).obj M := by
  refine PresheafOfModules.isoMk
    (fun U ↦ ((ModuleCat.extendScalarsId (R.obj.obj U)).app (M.val.obj U)).symm) ?_
  intro U V i
  ext m
  change (ModuleCat.extendScalarsId (R.obj.obj V)).inv.app (M.val.obj V)
      (M.val.map i m) =
    changeOfRingsMap (𝟙 R) M i
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (M.val.obj U) m)
  rw [ModuleCat.extendScalarsId_inv_app_apply, ModuleCat.extendScalarsId_inv_app_apply]
  simpa [changeOfRingsMap] using
    (Classical.choose_spec (exists_changeOfRingsMap (𝟙 R) M i)
      (1 : R.obj.obj U) m).symm

private noncomputable def scalarExtensionIdIsoApp
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max s h})
    (M : SheafOfModules.{max s h} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (scalarExtension (𝟙 R)).obj M ≅ M :=
  (PresheafOfModules.sheafification (𝟙 _)).mapIso
      (scalarExtensionPresheafIdIso R M).symm ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app M)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarExtensionIdIso
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max s h}) : scalarExtension (𝟙 R) ≅ 𝟭 _ := by
  refine NatIso.ofComponents (scalarExtensionIdIsoApp R) ?_
  intro M N a
  let F := PresheafOfModules.sheafification.{max s h}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let ψ := (scalarExtensionPresheaf (𝟙 R)).map a
  have hp : (scalarExtensionPresheafIdIso R M).hom ≫ ψ =
      a.val ≫ (scalarExtensionPresheafIdIso R N).hom := by
    ext U m
    change (ModuleCat.extendScalars (RingHom.id (R.obj.obj U))).map (a.val.app U)
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (M.val.obj U) m) =
        (ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (N.val.obj U) (a.val.app U m)
    exact ConcreteCategory.congr_hom ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.naturality
      (a.val.app U)) m
  have hp' : (scalarExtensionPresheafIdIso R M).inv ≫ a.val =
      ψ ≫ (scalarExtensionPresheafIdIso R N).inv := by
    rw [← cancel_epi (scalarExtensionPresheafIdIso R M).hom]
    simp only [← Category.assoc, hp]
    simp
  symm
  change F.map (scalarExtensionPresheafIdIso R M).inv ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app M ≫ a =
    F.map ψ ≫ F.map (scalarExtensionPresheafIdIso R N).inv ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app N
  rw [← (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit_naturality a]
  change F.map (scalarExtensionPresheafIdIso R M).inv ≫ F.map a.val ≫ _ = _
  rw [← F.map_comp_assoc, hp', F.map_comp_assoc]

set_option synthInstance.maxSize 256 in
open MonoidalCategory in
private theorem isKFlat_of_iso
    {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max s h}}
    {P Q : CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (e : P ≅ Q) (hP : P.IsAcyclicTensorKFlat) : Q.IsAcyclicTensorKFlat := by
  let := monoidalCategory R
  intro A hA n
  let F := (MonoidalCategory.curriedTensor (SheafOfModules.{max s h}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let e' : CochainComplex.mapBifunctor A P (curriedTensor _) ≅
      CochainComplex.mapBifunctor A Q (curriedTensor _) :=
    HomologicalComplex₂.total.mapIso ((F.obj A).mapIso e) (ComplexShape.up ℤ)
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (hP A hA n)).of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso e').symm |>
      (HomologicalComplex.exactAt_iff_isZero_homology _ n).2

private theorem isKFlat_inverseImage
    {C D : Type s} [Category.{h} C] [Category.{h} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{max s h}} {RI : Sheaf JD CommRingCat.{max s h}}
    (L : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h)))
    (V : Sheaf JD (Type (max s h)) ⥤ Sheaf JC (Type (max s h))) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (I : AlgebraicInverseImage L R RI) [I.modules.Additive]
    (P : CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
    CochainComplex.IsAcyclicTensorKFlat
      ((I.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  have := algebraicInverseImage_finiteLimits L I
  have : I.modules.Additive := Functor.additive_of_preserves_binary_products I.modules
  have := scalarExtension_additive (𝟙 RI)
  let U := I.modules ⋙ scalarExtension (𝟙 RI)
  have hobj (M) : U.obj M = changeOfRings (𝟙 RI) (I.modules.obj M) := rfl
  have hmap {M N} (a : M ⟶ N) : U.map a = eqToHom (hobj M) ≫
      changeOfRingsHom (𝟙 RI) (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hk := (isKFlat_ringedToposPullback L V adj I (𝟙 RI) U hobj hmap P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP)
      hf).1
  let e : U ≅ I.modules :=
    Functor.isoWhiskerLeft I.modules (scalarExtensionIdIso RI) ≪≫ I.modules.rightUnitor
  exact isKFlat_of_iso ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app P)
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk)

set_option synthInstance.maxSize 2048 in
/-- Derived pullback computes the ordinary pullback on a K-flat flat-term complex and
on the total tensor of two such complexes.
Source: Stacks Project, Cohomology on Sites, Tags 06YY, 07A4 and 0G7E.
(blueprint: lem-weil-pbc-kflat-tensor-pullback-computation-universes).
Proof: algebraic inverse image preserves finite limits and epimorphisms, hence
homology. Its image of a K-flat flat-term complex is K-flat by applying the ringed-topos
pullback theorem with identity scalar extension and cancelling the canonical identity
extension isomorphism. The existing independent-universe derived change-of-rings theorem
then preserves quasi-isomorphisms between these images. The object and map equalities
identify their composite with the specified uStar. Resolve every homotopy object by a
K-flat complex with flat terms, and apply the resolving-class derived-functor theorem.
Its counit is invertible on these representatives. The unique isomorphism of left
derived functors transports that assertion to LF and epsilon; the canonical quotient
comparisons transport it to complexes. Finally the existing total-tensor model theorem
supplies K-flatness and flat terms for the tensor, so the same computation applies. -/
theorem derivedPullback_kflat_tensor_computation
    {C D : Type s} [Category.{h} C] [Category.{h} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{max s h}} {S RI : Sheaf JD CommRingCat.{max s h}}
    (uInv : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h)))
    (uPush : Sheaf JD (Type (max s h)) ⥤ Sheaf JC (Type (max s h)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R) ⥤
      SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))
    (hobj : ∀ M : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R), uStar.obj M =
        changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)} (a : M ⟶ N),
        uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) (ComplexShape.up
        ℤ)))
    :
    (∀ P : CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) ℤ,
      P.IsAcyclicTensorKFlat →
      (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
      IsIso (derivedPullbackComplexComparison uStar LF epsilon P)) ∧
    (∀ P Q : CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) ℤ,
      P.IsAcyclicTensorKFlat →
      (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
      Q.IsAcyclicTensorKFlat →
      (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (Q.X n)) →
      IsIso (derivedPullbackComplexComparison uStar LF epsilon
        (CochainComplex.mapBifunctor P Q
          (@curriedTensor _ _ (monoidalCategory R))))) := by
  classical
  let A := SheafOfModules.{max s h}
    ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)
  let B := SheafOfModules.{max s h}
    ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)
  let T := uStar.mapHomologicalComplex (.up ℤ)
  let H := HomotopyCategory.quotient A (.up ℤ)
  let F := uStar.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hpres : ∀ {P Q : CochainComplex A ℤ} (a : P ⟶ Q),
      P.IsAcyclicTensorKFlat →
      (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
      Q.IsAcyclicTensorKFlat →
      (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (Q.X n)) →
      QuasiIso a → QuasiIso (T.map a) := by
    have := algebraicInverseImage_finiteLimits uInv I
    have : I.modules.Additive := Functor.additive_of_preserves_binary_products I.modules
    have := algebraicInverseImage_epi uInv uPush adj I
    have : I.modules.PreservesHomology :=
      Functor.preservesHomology_of_preservesEpis_and_kernels I.modules
    let A' := SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj RI)
    let := HasDerivedCategory.standard A'
    let := HasDerivedCategory.standard B
    obtain ⟨E, heobj, hemap, headd, hepres, _⟩ :=
      derivedChangeOfRingsIndependentCoefficients c
    have := headd
    intro P Q a hp hf hq hqf ha
    have := ha
    have hkP := isKFlat_inverseImage uInv uPush adj I P hp hf
    have hkQ := isKFlat_inverseImage uInv uPush adj I Q hq hqf
    have ht := hepres ((I.modules.mapHomologicalComplex (.up ℤ)).map a) hkP hkQ
      (by infer_instance)
    let e : uStar ≅ I.modules ⋙ E := NatIso.ofComponents
      (fun M ↦ eqToIso ((hobj M).trans (heobj (I.modules.obj M)).symm)) (by
        intro M N a
        simp only [Functor.comp_map]
        rw [hmap, hemap]
        simp only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_trans_assoc])
    let e' : T ≅ I.modules.mapHomologicalComplex (.up ℤ) ⋙
        E.mapHomologicalComplex (.up ℤ) :=
      NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (I.modules ⋙ E)) (.up ℤ)).symm
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e'.app P) (e'.app Q) (e'.hom.naturality a).symm)).2 ht
  let K : Set (HomotopyCategory A (.up ℤ)) :=
    {X | ∃ P : CochainComplex A ℤ, H.obj P = X ∧
      P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)}
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (a : X' ⟶ X),
        X' ∈ K ∧ HomotopyCategory.quasiIso A (.up ℤ) a := by
    intro X
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, a, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
    have hflat : ∀ n, IsFlatOnSite (J := JC) (R := R) (P.X n) := fun n ↦
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm (hf n)
    exact ⟨H.obj P, H.map a, ⟨P, rfl, hp, hflat⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff a).2 hq⟩
  have hinv : ∀ (X X' : HomotopyCategory A (.up ℤ)) (a : X ⟶ X'),
      X ∈ K → X' ∈ K → HomotopyCategory.quasiIso A (.up ℤ) a →
        IsIso (F.map a) := by
    intro X X' a hX hX' ha
    obtain ⟨P, rfl, hp, hf⟩ := hX
    obtain ⟨P', rfl, hp', hf'⟩ := hX'
    obtain ⟨a, rfl⟩ := H.map_surjective a
    have ht := hpres a hp hf hp' hf'
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 ha)
    change IsIso (DerivedCategory.Qh.map
      ((uStar.mapHomotopyCategory (.up ℤ)).map (H.map a)))
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff (T.map a)).2 ht)
  obtain ⟨_, LF', ε', hLF', _, hε'⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F K hres hinv
  have := hLF
  have := hLF'
  let e := Functor.leftDerivedNatIso LF' LF ε' epsilon
    (HomotopyCategory.quasiIso A (.up ℤ)) (Iso.refl F)
  have he (P : CochainComplex A ℤ) (hp : P.IsAcyclicTensorKFlat)
      (hf : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
      IsIso (derivedPullbackComplexComparison uStar LF epsilon P) := by
    have : IsIso (ε'.app (H.obj P)) := hε' (H.obj P) ⟨P, rfl, hp, hf⟩
    have hfac : e.hom.app (DerivedCategory.Qh.obj (H.obj P)) ≫
        epsilon.app (H.obj P) = ε'.app (H.obj P) := by
      simp [e, Functor.leftDerivedNatIso, Functor.leftDerivedNatTrans_app]
    have heps : IsIso (epsilon.app (H.obj P)) := by
      have : IsIso (e.hom.app (DerivedCategory.Qh.obj (H.obj P)) ≫
          epsilon.app (H.obj P)) := by rw [hfac]; infer_instance
      exact IsIso.of_isIso_comp_left (e.hom.app (DerivedCategory.Qh.obj (H.obj P)))
        (epsilon.app (H.obj P))
    unfold derivedPullbackComplexComparison
    infer_instance
  refine ⟨he, ?_⟩
  intro P Q hp hf hq hqf
  have ht := KFlatTotalTensorModel.kFlat_total_tensor_model R P Q hp hq hf hqf
  exact he _ ht.1 ht.2.1

end SheafOfModules.CanonicalTensorPullbackOfUniverses
