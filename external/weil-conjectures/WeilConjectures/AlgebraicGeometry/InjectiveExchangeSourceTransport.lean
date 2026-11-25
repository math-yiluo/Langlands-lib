/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Source transport on an injective representative

Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation.
(blueprint: lem-weil-pbc-injective-exchange-source-transport).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Expand the inverse of the fixed injective direct-image comparison.

Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation;
`sourceInjectiveDirectImageIso` in StrictLocalInjectiveSourceComparison.
(blueprint: lem-weil-pbc-injective-exchange-source-transport).

Proof: the defining isomorphism is the image of the direct-image transport by
q', followed by the inverse derived unit, then the homotopy and complex
localization comparisons. Inverting reverses these factors. The inverse of the
inverse unit is the unit itself. The homotopy functor comparison at a quotient
complex is the identity, as is quotientCompQhIso at that complex. Functoriality
and the identity laws therefore leave exactly the unit followed by transport
by q'.inv. Only source injectivity is used to define the original isomorphism;
no inverse image or target direct-image unit appears. -/
theorem injectiveExchange_source_transport {X S : Scheme.{v}} (f : X ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    let M₁ := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let M : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :=
      ⟨M₁, ((InjectiveObject.ι _).mapCochainComplexPlus.obj J).property⟩
    let H := (HomotopyCategory.Plus.quotient _).obj M
    let q' : K ≅ DerivedCategory.Plus.Qh.obj H :=
      DerivedCategory.Plus.ι.preimageIso (Y := DerivedCategory.Plus.Qh.obj H)
        (q ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app M.obj)
    let R := lowerStar AddCommGrpCat.{v + 1} f
    (sourceInjectiveDirectImageIso f K J q).inv =
      (DerivedCategory.quotientCompQhIso _).inv.app
        ((R.mapHomologicalComplex (.up ℤ)).obj M.obj) ≫
      DerivedCategory.Plus.ι.map (R.rightDerivedFunctorPlusUnith.app H) ≫
      DerivedCategory.Plus.ι.map (R.rightDerivedFunctorPlus.map q'.inv) := by
  simp only [sourceInjectiveDirectImageIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, asIso_hom]
  simp only [Functor.map_comp, Functor.mapHomotopyCategoryFactors,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift, NatIso.ofComponents.app, Iso.refl_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

end AlgebraicGeometry.Etale
