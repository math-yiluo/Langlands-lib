/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientPullback
import WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientTensorRepresentativeSquare
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent

/-! # Compatibility of coefficient restriction with tensor pullback

(blueprint: lem-pbc-coefficient-restriction-tensor-comparison-compatibility)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

attribute [local implicit_reducible] pbcDerivedRestrict
  Functor.map₂HomologicalComplex
  SheafOfModules.restrictScalars

attribute [local irreducible] Functor.mapDerivedCategory
  proEtaleRingDerivedPullbackFactors CoefficientTensorChain.complexPullback
  pullback SheafOfModules.monoidalCategory

/-- The normalized coefficient tensor comparison, including its geometric compatibility.

Source: Stacks Tags 03EL and 07A4. Construct the coefficient tensor comparison by
representative descent of the chain tensor square. On a flat K-flat pair, the three
representative normalization equations reduce the desired square to that chain
square. Full faithfulness of restriction to resolving representatives extends the
square to all derived pairs.

(blueprint: lem-pbc-coefficient-restriction-tensor-comparison-compatibility)
-/
theorem tensorComparison_compatibility {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (aY : ProEtaleTensorModel Y R)
    (z : ProEtaleTensorModel X
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    (aX : ProEtaleTensorModel X S) :
    ∃ rho : ((pbcDerivedRestrict c.hom).prod (pbcDerivedRestrict c.hom)) ⋙ z.tensor ≅
        aX.tensor ⋙ pbcDerivedRestrict c.hom,
      ∀ F G : DerivedCategory (proEtaleRingModules Y R),
        (pullback f R S c).hom.app (aY.tensor.obj (F, G)) ≫
            (proEtaleCanonicalTensorComparison f R
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
              (Iso.refl _) aY z).hom.app (F, G) =
          (pbcDerivedRestrict c.hom).map
              ((proEtaleCanonicalTensorComparison f R S c aY aX).hom.app (F, G)) ≫
            rho.inv.app ((proEtaleRingDerivedPullback f R S c).obj F,
              (proEtaleRingDerivedPullback f R S c).obj G) ≫
            z.tensor.map (Prod.mkHom
              ((pullback f R S c).hom.app F)
              ((pullback f R S c).hom.app G)) := by
  let A := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R
  let U := (pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)
  let UD := pbcDerivedRestrict c.hom
  let CD := proEtaleRingDerivedPullback f R S c
  let ID := proEtaleRingDerivedPullback f R A (Iso.refl _)
  let b := pullback f R S c
  let ac := proEtaleCanonicalTensorComparison f R S c aY aX
  let ai := proEtaleCanonicalTensorComparison f R A (Iso.refl _) aY z
  obtain ⟨o⟩ := SheafOfModules.ringIso_tensor_transport c
  let sigma := CoefficientTensorChain.tensorIso f R S c o
  have hU (P : CochainComplex (proEtaleRingModules X S) ℤ)
      (hp : proEtaleFlatRepresentatives X S P) :
      proEtaleFlatRepresentatives X A (U.obj P) :=
    ⟨(o.kflat_iff P).2 hp.1, fun n ↦ (o.flat_iff (P.X n)).2 (hp.2 n)⟩
  obtain ⟨ffU⟩ := tensorRepresentatives_fullyFaithful S A
  obtain ⟨gamma, hgamma, _⟩ := CategoryTheory.tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q U UD (pbcRestrict c.hom).mapDerivedCategoryFactors.hom
    (proEtaleFlatRepresentatives X S) (proEtaleFlatRepresentatives X A) hU ffU
    (CoefficientTensorChain.total X S) (CoefficientTensorChain.total X A)
    aX.tensor z.tensor aX.representative z.representative sigma
    (fun _ _ ↦ inferInstance) (fun _ _ _ _ ↦ inferInstance)
  refine ⟨gamma.symm, ?_⟩
  let left : aY.tensor ⋙ CD ⋙ UD ⟶ (ID.prod ID) ⋙ z.tensor :=
    whiskerLeft aY.tensor b.hom ≫ ai.hom
  let right : aY.tensor ⋙ CD ⋙ UD ⟶ (ID.prod ID) ⋙ z.tensor :=
    whiskerRight ac.hom UD ≫ whiskerLeft (CD.prod CD) gamma.hom ≫
      whiskerRight (NatTrans.prod b.hom b.hom) z.tensor
  suffices h : left = right by
    intro F G
    exact NatTrans.congr_app h (F, G)
  obtain ⟨ff⟩ := tensorRepresentatives_fullyFaithful R A
  apply ff.map_injective
  ext Z
  obtain ⟨⟨P, hp⟩, ⟨Q, hq⟩⟩ := Z
  change left.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
    right.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
  exact representative_square f R S c aY z aX o hU gamma hgamma P Q hp hq

end AlgebraicGeometry.Scheme.CoefficientTensorTransport
