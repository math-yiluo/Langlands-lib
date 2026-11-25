/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenInterchangeCoherence

/-! # Bundled proper/open comparison families

## References

* Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F

## Implementation details

The families are bundled to retain their relation to the coherence proof without repeatedly
expanding dependent existential selection terms. The support inclusion determines the ordinary
comparison and the derived-unit normalization determines the derived comparison, so no
arbitrary data is selected.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory
attribute [local instance 2000] Abelian.toPreadditive

namespace AlgebraicGeometry.Etale

/-- The two comparison families together with their normalizations. -/
structure ProperOpenInterchangeData (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] where
  /-- The support-preserving ordinary comparison. -/
  underived : ProperOpenUnderivedFamily Λ
  /-- The comparison of bounded-below derived functors. -/
  derived : ProperOpenDerivedFamily Λ
  /-- Section, unit and pasting normalizations. -/
  conditions : properOpenInterchangeConditions Λ underived derived

/-- The normalized proper/open comparison families provided by
`properOpenInterchangeCoherence`. -/
@[no_expose, irreducible]
def properOpenInterchangeData (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ProperOpenInterchangeData Λ where
  underived := (properOpenInterchangeCoherence Λ).choose
  derived := (properOpenInterchangeCoherence Λ).choose_spec.choose
  conditions := (properOpenInterchangeCoherence Λ).choose_spec.choose_spec

/-- The stored derived family is the second witness of `properOpenInterchangeCoherence`. -/
theorem properOpenInterchangeData_derived (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ((properOpenInterchangeData Λ).derived : ProperOpenDerivedFamily Λ) =
      ((properOpenInterchangeCoherence Λ).choose_spec.choose : ProperOpenDerivedFamily Λ) := by
  unfold properOpenInterchangeData
  rfl

/-- The section-preserving inclusion normalization of the stored ordinary family. -/
theorem ProperOpenInterchangeData.inclusionNormalization
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (d : ProperOpenInterchangeData Λ) :
    ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (F : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (d.underived k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app
            ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F :=
  @And.left _ _ d.conditions

/-- The derived-unit normalization of the stored families. -/
theorem ProperOpenInterchangeData.unitNormalization
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (d : ProperOpenInterchangeData Λ) :
    ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i)
      (J : HomotopyCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map
          ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusUnith.app J) ≫
          (d.derived k i r p h).hom.app (DerivedCategory.Plus.Qh.obj J) =
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlusFactorsh.hom.app
            ((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomotopyCategoryPlus.obj J) ≫
          DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus (d.underived k i r p h).hom).app J) ≫
          (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusUnith.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomotopyCategoryPlus.obj J) ≫
          (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus.map
            ((Functor.mapDerivedCategoryPlusFactorsh
              (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)).inv.app J) :=
  @And.left _ _ (@And.right _ _ d.conditions)

end AlgebraicGeometry.Etale
