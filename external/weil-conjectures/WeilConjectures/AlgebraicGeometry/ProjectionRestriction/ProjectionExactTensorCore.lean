/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
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
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import all WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! Exact tensor functors on resolving representatives.

## References

* Stacks Project, Tags 06YU, 07A4 and 0FNH
* Stacks 0735
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}

/-- The fixed exact localization model of an additive exact module functor. -/
abbrev exactTensorModel (L : Mod R ⥤ Mod S) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] : ExactModel L where
  additive := inferInstance
  functor := L.mapDerivedCategory
  factors := L.mapDerivedCategoryFactors

namespace ExactTensor
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι

private structure Data (R : Sheaf J CommRingCat.{u + 1})
    (S : Sheaf K CommRingCat.{u + 1}) where
  pullback : Mod R ⥤ Mod S
  [additive : pullback.Additive]
  [limits : PreservesFiniteLimits pullback]
  [colimits : PreservesFiniteColimits pullback]
  [coproducts : PreservesColimitsOfSize.{0, 0} pullback]

attribute [instance] Data.additive Data.limits Data.colimits Data.coproducts
private def Data.left (o : Data R S) : Der R ⥤ Der S := o.pullback.mapDerivedCategory
private instance Data.leftShift (o : Data R S) : o.left.CommShift ℤ :=
  inferInstanceAs (o.pullback.mapDerivedCategory.CommShift ℤ)
private abbrev Data.leftModel (o : Data R S) : ExactModel o.pullback where
  additive := inferInstance
  functor := o.left
  factors := o.pullback.mapDerivedCategoryFactors
private instance Data.leftModelShift (o : Data R S) : o.leftModel.functor.CommShift ℤ :=
  inferInstanceAs (o.left.CommShift ℤ)

private def Data.factors (o : Data R S) :
    DerivedCategory.Q ⋙ o.left ≅
      o.pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  o.pullback.mapDerivedCategoryFactors
private instance Data.factorsShift (o : Data R S) :
    NatTrans.CommShift o.factors.hom ℤ :=
  inferInstanceAs (NatTrans.CommShift o.pullback.mapDerivedCategoryFactors.hom ℤ)

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

private structure OrdinaryTensor (o : Data R S) where
  iso : ∀ M N : Mod R, o.pullback.obj (((tensor R).obj M).obj N) ≅
    ((tensor S).obj (o.pullback.obj M)).obj (o.pullback.obj N)
  naturality : ∀ {M M' N N' : Mod R} (f : M ⟶ M') (g : N ⟶ N'),
    o.pullback.map (((tensor R).map f).app N ≫ ((tensor R).obj M').map g) ≫
      (iso M' N').hom =
    (iso M N).hom ≫ (((tensor S).map (o.pullback.map f)).app (o.pullback.obj N) ≫
      ((tensor S).obj (o.pullback.obj M')).map (o.pullback.map g))

private def ordinaryComparison (o : Data R S) (mu : OrdinaryTensor o) :
    (Functor.postcompose₂.obj o.pullback).obj (tensor R) ≅
      (((Functor.whiskeringLeft₂ (Mod S)).obj o.pullback).obj o.pullback).obj (tensor S) :=
by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  exact NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦ mu.iso M N) (fun {N N'} g ↦ by
    change o.pullback.map (((tensor R).obj M).map g) ≫ _ =
      _ ≫ ((tensor S).obj (o.pullback.obj M)).map (o.pullback.map g)
    simpa only [tensor, curriedTensor_map_app, curriedTensor_obj_map,
      CategoryTheory.Functor.map_id, MonoidalCategory.id_whiskerRight, NatTrans.id_app,
      Category.id_comp] using mu.naturality (𝟙 M) g))
    (fun {M M'} f ↦ by
      apply NatTrans.ext
      funext N
      change o.pullback.map (((tensor R).map f).app N) ≫ _ =
        _ ≫ ((tensor S).map (o.pullback.map f)).app (o.pullback.obj N)
      have h := mu.naturality f (𝟙 N)
      erw [((tensor R).obj M').map_id, Category.comp_id,
        o.pullback.map_id, ((tensor S).obj (o.pullback.obj M')).map_id,
        Category.comp_id] at h
      exact h)

-- Totalize the ordinary comparison; left-adjoint pullback preserves the coproducts.
private def chainComparison (o : Data R S) (mu : OrdinaryTensor o) :
    (Functor.postcompose₂.obj (o.pullback.mapHomologicalComplex (.up ℤ))).obj
      ((tensor R).map₂CochainComplex) ≅
    (((Functor.whiskeringLeft₂ (CochainComplex (Mod S) ℤ)).obj
      (o.pullback.mapHomologicalComplex (.up ℤ))).obj
        (o.pullback.mapHomologicalComplex (.up ℤ))).obj ((tensor S).map₂CochainComplex) := by
  let := o.coproducts
  exact asIso (HomologicalComplex.mapBifunctorComparisonNatTrans
    (ordinaryComparison o mu).hom (.up ℤ))

private theorem chainComparison_inv (o : Data R S)
    (a : TensorModel R) (b : TensorModel S) (mu : OrdinaryTensor o)
    (comm : ∀ (P Q : CochainComplex (Mod R) ℤ) (n m : ℤ),
      totalComponent a b o.pullback mu.iso P Q n ≫
        o.pullback.map (((total R).obj (P, Q)).d n m) =
      ((total S).obj ((o.pullback.mapHomologicalComplex (.up ℤ)).obj P,
        (o.pullback.mapHomologicalComplex (.up ℤ)).obj Q)).d n m ≫
          totalComponent a b o.pullback mu.iso P Q m)
    (P Q : CochainComplex (Mod R) ℤ) :
    ((chainComparison o mu).inv.app P).app Q =
      totalMap a b o.pullback mu.iso comm P Q := by
  let := o.coproducts
  apply (cancel_epi (((chainComparison o mu).hom.app P).app Q)).1
  simp only [← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app]
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map o.pullback
  intro p q hpq
  change o.pullback.map _ ≫ 𝟙 _ =
    o.pullback.map _ ≫
      (HomologicalComplex.mapBifunctorComparison (ordinaryComparison o mu).hom
        (.up ℤ) P Q).f n ≫ totalComponent a b o.pullback mu.iso P Q n
  erw [HomologicalComplex.mapBifunctorComparison_f,
    HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  simp only [Category.comp_id, totalComponent,
    tensorPullbackTotalComponent]
  erw [HomologicalComplex.ι_mapBifunctorDesc]
  change _ = (mu.iso (P.X p) (Q.X q)).hom ≫ (mu.iso (P.X p) (Q.X q)).inv ≫ _
  erw [Iso.hom_inv_id_assoc]
  rfl

private theorem cancel_representative
    {A B : Type*} [Category A] [Category B] (q : A ⥤ B)
    {X Y : A} {U V : B} (e : X ≅ Y) (r : q.obj X ≅ V)
    (a : U ⟶ V) (d : U ⟶ q.obj Y)
    (h : a = d ≫ q.map e.inv ≫ r.hom) :
    a ≫ r.inv ≫ q.map e.hom = d := by
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    ← q.map_comp, Iso.inv_hom_id, q.map_id, Category.comp_id]

attribute [local semireducible] SheafOfModules.monoidalCategory

private theorem tensor_core (o : Data R S) (a : TensorModel R) (b : TensorModel S)
    (mu : OrdinaryTensor o)
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
    exact mu.naturality f g
  let comm := tensorPullbackTotalComponent_comm L mu.iso hn
  let beta := tensorPullbackTotal L mu.iso hn
  have he (P Q : CochainComplex (Mod R) ℤ) :
      ((chainComparison o mu).inv.app P).app Q = beta P Q :=
    chainComparison_inv o a b mu comm P Q
  have hi (P Q : CochainComplex (Mod R) ℤ) : IsIso (beta P Q) := by
    rw [← he]
    exact (show IsIso ((((chainComparison o mu).app P).app Q).inv) from inferInstance)
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

attribute [local irreducible] SheafOfModules.monoidalCategory

private theorem representative_square (o : Data R S)
    (a : TensorModel R) (b : TensorModel S) (mu : OrdinaryTensor o)
    (t : TensorComparison o.pullback o.leftModel a b mu.iso)
    (P Q : CochainComplex (Mod R) ℤ) (hp : resolving R P) (hq : resolving R Q) :
    o.left.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      t.comparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      b.functor.map (Prod.mkHom (o.leftModel.factors.hom.app P)
        (o.leftModel.factors.hom.app Q)) =
    o.leftModel.factors.hom.app ((total R).obj (P, Q)) ≫
      DerivedCategory.Q.map (((chainComparison o mu).hom.app P).app Q) ≫
      b.representative.hom.app
        (⟨(o.pullback.mapHomologicalComplex (.up ℤ)).obj P, t.preserves P hp⟩,
          ⟨(o.pullback.mapHomologicalComplex (.up ℤ)).obj Q, t.preserves Q hq⟩) := by
  have h := t.representative P Q hp hq
  rw [← chainComparison_inv o a b mu t.comm P Q] at h
  have hh := congrArg (fun z ↦ z ≫
    DerivedCategory.Q.map (((chainComparison o mu).hom.app P).app Q) ≫
      b.representative.hom.app
        (⟨(o.pullback.mapHomologicalComplex (.up ℤ)).obj P, t.preserves P hp⟩,
          ⟨(o.pullback.mapHomologicalComplex (.up ℤ)).obj Q, t.preserves Q hq⟩)) h
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app] at hh
  erw [DerivedCategory.Q.map_id] at hh
  simp only [Category.id_comp, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh

/-- The ordinary total comparison descends to the exact-derived model. -/
theorem exactTensorComparison_nonempty (L : Mod R ⥤ Mod S) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesColimitsOfSize.{0, 0} L]
    (a : TensorModel R) (b : TensorModel S)
    (mu : ∀ M N : Mod R, L.obj (((tensor R).obj M).obj N) ≅
      ((tensor S).obj (L.obj M)).obj (L.obj N))
    (hn : ∀ {M M' N N' : Mod R} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (((tensor R).map f).app N ≫ ((tensor R).obj M').map g) ≫
        (mu M' N').hom =
      (mu M N).hom ≫ (((tensor S).map (L.map f)).app (L.obj N) ≫
        ((tensor S).obj (L.obj M')).map (L.map g)))
    (hp : ∀ P, resolving R P → resolving S ((L.mapHomologicalComplex (.up ℤ)).obj P)) :
    Nonempty (TensorComparison L (exactTensorModel L) a b mu) := by
  let o : Data R S := ⟨L⟩
  let m : OrdinaryTensor o := ⟨mu, hn⟩
  exact tensor_core o a b m hp

end ExactTensor
end AlgebraicGeometry.Scheme.ProjectionRestriction
