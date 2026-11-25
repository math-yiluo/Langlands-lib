/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorShifts
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
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
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # Representative-normalized tensor comparison for pro-etale pullback

## References

* Stacks Project, Cohomology on Sites, Tag 07A4
* Stacks Project, Tag 07A4, using the total-complex construction of Tag 06YN
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
private theorem ordinary_naturality (o : Operation F R S) (mu : o.OrdinaryTensor)
    {M M' N N' : Mod R} (f : M ⟶ M') (g : N ⟶ N') :
    o.pullback.map (((tensor R).map f).app N ≫ ((tensor R).obj M').map g) ≫
      (mu.iso M' N').hom =
    (mu.iso M N).hom ≫ (((tensor S).map (o.pullback.map f)).app (o.pullback.obj N) ≫
      ((tensor S).obj (o.pullback.obj M')).map (o.pullback.map g)) := by
  apply (o.moduleAdjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [o.pushforward.map_comp, o.pushforward.map_comp]
  have hn := o.moduleAdjunction.unit.naturality
    (((tensor R).map f).app N ≫ ((tensor R).obj M').map g)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, ← hn]
  apply SheafOfModules.CochainScalarConstruction.pure_hom_ext R M N
  intro W x y
  have hp := SheafOfModules.CochainScalarConstruction.pure_map R f g W x y
  change _ = pure R M' N' W (f.val.app W x) (g.val.app W y) at hp
  have hM := congrArg (fun k ↦ k.val.app W x) (o.moduleAdjunction.unit.naturality f)
  have hN := congrArg (fun k ↦ k.val.app W y) (o.moduleAdjunction.unit.naturality g)
  change _ = _ at hM hN
  have hS := SheafOfModules.CochainScalarConstruction.pure_map S
    (o.pullback.map f) (o.pullback.map g) (F.op.obj W)
    ((o.moduleAdjunction.unit.app M).val.app W x)
    ((o.moduleAdjunction.unit.app N).val.app W y)
  change _ = pure S _ _ _ _ _ at hS
  simp only [MonoidalCategory.tensorHom_def] at hp hS
  change ((((tensor R).map f).app N ≫ ((tensor R).obj M').map g).val.app W)
    (pure R M N W x y) = pure R M' N' W (f.val.app W x) (g.val.app W y) at hp
  change ((((tensor S).map (o.pullback.map f)).app (o.pullback.obj N) ≫
    ((tensor S).obj (o.pullback.obj M')).map (o.pullback.map g)).val.app (F.op.obj W))
      (pure S _ _ (F.op.obj W)
        ((o.moduleAdjunction.unit.app M).val.app W x)
        ((o.moduleAdjunction.unit.app N).val.app W y)) = _ at hS
  change
    ((o.pushforward.map (mu.iso M' N').hom).val.app W)
      ((o.moduleAdjunction.unit.app _).val.app W
        (((((tensor R).map f).app N ≫ ((tensor R).obj M').map g)).val.app W
          (pure R M N W x y))) =
    ((o.pushforward.map
      (((tensor S).map (o.pullback.map f)).app (o.pullback.obj N) ≫
        ((tensor S).obj (o.pullback.obj M')).map (o.pullback.map g))).val.app W)
        (((o.pushforward.map (mu.iso M N).hom).val.app W)
          ((o.moduleAdjunction.unit.app _).val.app W (pure R M N W x y)))
  rw [hp, mu.pure_unit, mu.pure_unit]
  exact (hS.trans (congrArg₂ (pure S _ _ (F.op.obj W)) hM.symm hN.symm)).symm

private theorem cancel_representative
    {A B : Type*} [Category A] [Category B] (q : A ⥤ B)
    {X Y : A} {U V : B} (e : X ≅ Y) (r : q.obj X ≅ V)
    (a : U ⟶ V) (d : U ⟶ q.obj Y)
    (h : a = d ≫ q.map e.inv ≫ r.hom) :
    a ≫ r.inv ≫ q.map e.hom = d := by
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    ← q.map_comp, Iso.inv_hom_id, q.map_id, Category.comp_id]

private theorem tensor_core (o : Operation F R S) (a : TensorModel R) (b : TensorModel S)
    (mu : o.OrdinaryTensor)
    (hp : ∀ P, resolving R P → resolving S ((o.pullback.mapHomologicalComplex (.up ℤ)).obj P)) :
    Nonempty (TensorComparison o.pullback o.leftModel a b mu.iso) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := a.preadditive
  let := b.preadditive
  let L := o.pullback
  let LC := L.mapHomologicalComplex (.up ℤ)
  have hn : ∀ {M M' N N' : Mod R} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (f ⊗ₘ g) ≫ (mu.iso M' N').hom =
        (mu.iso M N).hom ≫ (L.map f ⊗ₘ L.map g) := by
    intro M M' N N' f g
    change o.pullback.map
      (((tensor R).map f).app N ≫ ((tensor R).obj M').map g) ≫
        (mu.iso M' N').hom =
      (mu.iso M N).hom ≫
        (((tensor S).map (o.pullback.map f)).app (o.pullback.obj N) ≫
          ((tensor S).obj (o.pullback.obj M')).map (o.pullback.map g))
    exact ordinary_naturality o mu f g
  let comm := tensorPullbackTotalComponent_comm L mu.iso hn
  let beta := tensorPullbackTotal L mu.iso hn
  have hi (P Q : CochainComplex (Mod R) ℤ) : IsIso (beta P Q) :=
    tensorPullbackTotal_isIso L mu.iso hn o.pushforward o.moduleAdjunction P Q
  let betaiso : (LC.prod LC) ⋙ total S ≅ total R ⋙ LC :=
    NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ (beta X.1 X.2) (hi X.1 X.2))
      (fun f ↦ by
        dsimp only [beta, total, Functor.comp_map, Functor.prod_map]
        simp only [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
          asIso_hom, SheafOfModules.CanonicalTensorPullbackOfUniverses.tensorMap_factor]
        exact SheafOfModules.CanonicalTensorPullbackOfUniverses.tensorPullbackTotal_naturality
          L mu.iso hn f.1 f.2)
  let q := (resolving R).ι ⋙ DerivedCategory.Q
  let W := (Functor.whiskeringLeft _ _ (Der S)).obj (q.prod q)
  obtain ⟨_, _, _, hd⟩ := SheafOfModules.cochain_tensor_model_rigidity J R
  have hW : W.FullyFaithful :=
    ((Functor.FullyFaithful.nonempty_iff_map_bijective W).2
      (fun U V ↦ hd (Der S) inferInstance U V)).some
  obtain ⟨alpha, halpha, _⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q LC o.left
    o.leftModel.factors.hom (resolving R) (resolving S) hp hW
    (total R) (total S) a.functor b.functor a.representative b.representative betaiso.symm
    (fun _ _ ↦ inferInstance) (fun _ _ _ _ ↦ inferInstance)
  let t : TensorComparisonCore o.pullback o.leftModel a b mu.iso := {
    preserves := hp
    comparison := alpha
    comm := comm }
  refine ⟨{ toTensorComparisonCore := t, representative := ?_ }⟩
  intro P Q hP hQ
  have h := cancel_representative DerivedCategory.Q (betaiso.app (P, Q))
    (b.representative.app (⟨LC.obj P, hp P hP⟩, ⟨LC.obj Q, hp Q hQ⟩))
    (o.left.map (a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) ≫
      alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      b.functor.map (Prod.mkHom (o.leftModel.factors.hom.app P)
        (o.leftModel.factors.hom.app Q)))
    (o.leftModel.factors.hom.app ((total R).obj (P, Q))) (halpha P Q hP hQ)
  have hbeta : (betaiso.app (P, Q)).hom =
      totalMap a b o.pullback mu.iso t.comm P Q := by
    apply HomologicalComplex.Hom.ext
    funext n
    rfl
  simpa only [Category.assoc, Iso.app_inv, hbeta] using h

private theorem preserves_resolving {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (o : Operation (proEtaleBaseChange f) R S)
    (ho : o.coefficient =
      ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f R S c).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)
    (a : TensorModel R) (b : TensorModel S)
    (P : CochainComplex (Mod R) ℤ) (hp : resolving R P) :
    resolving S ((o.pullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  have hpush : o.pushforward = proEtaleRingModuleDirectImage f R S c := by
    dsimp only [Operation.pushforward]
    rw [ho]
    rfl
  let adj := (proEtaleRingModuleAdjunction f R S c).ofNatIsoRight (eqToIso hpush).symm
  let e := o.moduleAdjunction.leftAdjointUniq adj
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  have h := (proEtaleCanonicalTensorPullback f R S c
    { tensor := a.functor, representative := a.representative }
    { tensor := b.functor, representative := b.representative }).1 P hp
  refine ⟨?_, ?_⟩
  · exact SheafOfModules.kFlat_iso_independent S ec.symm h.1
  · intro n
    let := SheafOfModules.monoidalCategory S
    let en := (HomologicalComplex.eval _ _ n).mapIso ec
    have hf := (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso S _) (h.2 n)
    have hf' := (exactFunctor _ _).prop_of_iso ((tensor S).flip.mapIso en.symm) hf
    exact (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso S _).symm hf'

/-- The canonical ordinary tensor comparison descends with the signed shift squares. -/
theorem globalTensorComparison_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (o : Operation (proEtaleBaseChange f) R S)
    (ho : o.coefficient =
      ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f R S c).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)
    (a : TensorModel R) (b : TensorModel S) (sa : TensorShifts a) (sb : TensorShifts b)
    (mu : o.OrdinaryTensor) :
    ∃ t : TensorComparison o.pullback o.leftModel a b mu.iso,
      TensorComparisonShifts t (sa := sa) (sb := sb) (sd := inferInstance) := by
  obtain ⟨t⟩ := tensor_core o a b mu (preserves_resolving f R S c o ho a b)
  exact ⟨t, tensorComparison_shifts o a b sa sb mu t⟩

end AlgebraicGeometry.Scheme.ProjectionRestriction
