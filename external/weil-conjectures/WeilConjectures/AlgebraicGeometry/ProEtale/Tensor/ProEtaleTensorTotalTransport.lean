/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
import all WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Transport of the total tensor comparison

## References

* Stacks Project, Cohomology on Sites, Tag 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 100] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open ProjectionRestriction
attribute [local implicit_reducible] resolving proEtaleFlatRepresentatives
  CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.presheafToSheaf SheafOfModules.monoidalCategory
  proEtaleOrdinaryTensorPullback

/-- Transport a normalized ordinary tensor comparison to its signed total complexes. -/
theorem proEtaleTensorTotalTransport
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (L : Mod R ⥤ Mod S) [L.Additive]
    (e : L ≅ proEtaleRingModulePullback f R S c)
    (a : TensorModel R) (b : TensorModel S) (d : ExactModel L)
    (mu : ∀ M N : Mod R, L.obj (((tensor R).obj M).obj N) ≅
      ((tensor S).obj (L.obj M)).obj (L.obj N))
    (tc : TensorComparison L d a b mu)
    (he : ∀ M N : Mod R,
      e.hom.app (((tensor R).obj M).obj N) ≫
        (proEtaleOrdinaryTensorPullback f R S c M N).hom =
      (mu M N).hom ≫ ((tensor S).map (e.hom.app M)).app (L.obj N) ≫
        ((tensor S).obj ((proEtaleRingModulePullback f R S c).obj M)).map (e.hom.app N))
    (P Q : CochainComplex (Mod R) ℤ) :
    let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).hom
    (total S).map (Prod.mkHom (ec.app P) (ec.app Q)) ≫
        proEtaleTensorPullbackTotal f R S c P Q =
      totalMap a b L mu tc.comm P Q ≫ ec.app ((total R).obj (P, Q)) := by
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).hom
  have hi (M N : Mod R) :
      ((tensor S).map (e.hom.app M)).app (L.obj N) ≫
        ((tensor S).obj ((proEtaleRingModulePullback f R S c).obj M)).map (e.hom.app N) ≫
          (proEtaleOrdinaryTensorPullback f R S c M N).inv =
        (mu M N).inv ≫
          e.hom.app (((tensor R).obj M).obj N) := by
    apply (cancel_epi (mu M N).hom).1
    rw [← reassoc_of% (he M N)]
    simp only [Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  dsimp only
  simp only [total, Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
    SheafOfModules.CanonicalTensorPullbackOfUniverses.tensorMap_factor]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
    proEtaleTensorPullbackTotal, tensorPullbackTotal, tensorPullbackTotalComponent,
    totalMap, totalComponent, HomologicalComplex.ι_mapBifunctorDesc_assoc,
    HomologicalComplex.ι_mapBifunctorDesc]
  change ((tensor S).map (e.hom.app (P.X i))).app (L.obj (Q.X j)) ≫
      ((tensor S).obj ((proEtaleRingModulePullback f R S c).obj (P.X i))).map
        (e.hom.app (Q.X j)) ≫
      (proEtaleOrdinaryTensorPullback f R S c (P.X i) (Q.X j)).inv ≫ _ = _
  rw [reassoc_of% (hi (P.X i) (Q.X j))]
  simp only [Category.assoc]
  exact congrArg (fun z ↦ (mu (P.X i) (Q.X j)).inv ≫ z)
    (e.hom.naturality (P.ιMapBifunctor Q (tensor R) i j n hij)).symm

end AlgebraicGeometry.Scheme
