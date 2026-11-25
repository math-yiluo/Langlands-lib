/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-! # Additive functions on the small etale site

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim:
the additive section groups used in the affine linearization.
(blueprint: def-sc-etale-additive-structure-restriction)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- The underlying additive groups of the structure rings, in the coefficient universe of Gm.
This is the composite of the usual forgetful functor and the additive universe lift. 
(blueprint: def-sc-etale-additive-structure-restriction)
-/
noncomputable def etaleAdditiveCoefficients : CommRingCat.{u} ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- Forgetting multiplication and lifting the universe preserve the limits expressing
etale descent, so additive structure functions form a sheaf.
Source: the structure-sheaf descent theorem and preservation of limits by the
coefficient functor (blueprint: def-sc-etale-additive-structure-restriction). -/
theorem isSheaf_etaleAdditivePresheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf X.smallEtaleTopology
      (X.etaleStructurePresheaf ⋙ etaleAdditiveCoefficients) := by
  have : PreservesLimitsOfSize.{u, u + 1}
      (etaleAdditiveCoefficients ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) := by
    change PreservesLimitsOfSize.{u, u + 1}
      (CategoryTheory.forget CommRingCat.{u} ⋙ CategoryTheory.uliftFunctor.{u + 1, u})
    infer_instance
  have : PreservesLimitsOfSize.{u, u + 1} etaleAdditiveCoefficients :=
    preservesLimits_of_reflects_of_preserves etaleAdditiveCoefficients
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  exact Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.isSheaf_etaleStructurePresheaf

/-- The additive structure sheaf on the small etale site, lifted to the universe of Gm. 
(blueprint: def-sc-etale-additive-structure-restriction)
-/
noncomputable def etaleAdditiveSheaf (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ⟨X.etaleStructurePresheaf ⋙ etaleAdditiveCoefficients,
    isSheaf_etaleAdditivePresheaf X⟩

/-- Restriction of additive functions along a scheme morphism. On V this is pullback
along V times_Y X to V, exactly as for the restriction of units. 
(blueprint: def-sc-etale-additive-structure-restriction)
-/
noncomputable def etaleAdditiveSheafToLowerStar {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Y.etaleAdditiveSheaf ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj X.etaleAdditiveSheaf :=
  ⟨Functor.whiskerRight (etaleStructurePresheafToPullback g) etaleAdditiveCoefficients⟩

end AlgebraicGeometry.Scheme
