/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback

/-! # Normalization equations for tensor representatives -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] SheafOfModules.monoidalCategory
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingDerivedPullbackFactors
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

/-- The selected canonical comparison has its specified equation on representatives.
Source: Stacks Tags 07A4 and 0G7E; proEtaleCanonicalTensorPullback.
(blueprint: lem-pbc-canonical-tensor-representative-normalization)

Proof: the canonical comparison is the unique comparison chosen from the existing
existence-and-uniqueness theorem. Its specification gives the displayed equation,
with the actual signed-total functor in the source. No comparison is chosen here. -/
theorem canonical_tensor_representative {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
    (hp : proEtaleFlatRepresentatives Y R P) (hq : proEtaleFlatRepresentatives Y R Q) :
    ∃ (hp' : proEtaleFlatRepresentatives X S
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P))
      (hq' : proEtaleFlatRepresentatives X S
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q)),
      (proEtaleRingDerivedPullback f R S c).map
          (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
        (proEtaleCanonicalTensorComparison f R S c a b).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        b.tensor.map (Prod.mkHom
          ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
          ((proEtaleRingDerivedPullbackFactors f R S c).hom.app Q)) =
      (proEtaleRingDerivedPullbackFactors f R S c).hom.app
          ((CoefficientTensorChain.total Y R).obj (P, Q)) ≫
        DerivedCategory.Q.map (proEtaleTensorPullbackTotalIso f R S c P Q).inv ≫
        b.representative.hom.app (⟨_, hp'⟩, ⟨_, hq'⟩) := by
  exact (Classical.choose_spec (proEtaleCanonicalTensorPullback f R S c a b).2.exists)
    P Q hp hq

/-- Naturality of a tensor representative, expressed using actual complex maps.
Source: naturality of ProEtaleTensorModel.representative, Stacks Tag 07A4.
(blueprint: lem-pbc-canonical-tensor-representative-normalization)

Proof: regard the two chain maps as morphisms in the full subcategory of flat
K-flat complexes. Apply naturality of the representative natural isomorphism to
their product and reverse the resulting equation. No condition on the chain maps
other than their endpoints is needed, including when the complexes are zero. -/
theorem tensor_representative_naturality {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (a : ProEtaleTensorModel X R)
    {P Q P' Q' : CochainComplex (proEtaleRingModules X R) ℤ}
    (hp : proEtaleFlatRepresentatives X R P) (hq : proEtaleFlatRepresentatives X R Q)
    (hp' : proEtaleFlatRepresentatives X R P') (hq' : proEtaleFlatRepresentatives X R Q')
    (v : P ⟶ P') (w : Q ⟶ Q') :
    a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
        a.tensor.map (Prod.mkHom (DerivedCategory.Q.map v) (DerivedCategory.Q.map w)) =
      DerivedCategory.Q.map ((CoefficientTensorChain.total X R).map (Prod.mkHom v w)) ≫
        a.representative.hom.app (⟨P', hp'⟩, ⟨Q', hq'⟩) := by
  let vp : (⟨P, hp⟩ : (proEtaleFlatRepresentatives X R).FullSubcategory) ⟶ ⟨P', hp'⟩ :=
    ObjectProperty.homMk v
  let vq : (⟨Q, hq⟩ : (proEtaleFlatRepresentatives X R).FullSubcategory) ⟶ ⟨Q', hq'⟩ :=
    ObjectProperty.homMk w
  exact (a.representative.hom.naturality (Prod.mkHom vp vq)).symm

end AlgebraicGeometry.Scheme.CoefficientTensorTransport
