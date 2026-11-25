/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenCoverShriekComplexSES

/-!
# The extension-by-zero triangle of an open cover

Source: Stacks Project, More on Etale Cohomology, Tag 0GKK.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- The absolute extension-by-zero triangle of a two-open cover.

Source: Stacks Project, Tag 0GKK, `lemma-mayer-vietoris-shriek`.
(blueprint: lem-weil-pbc-etale-open-cover-shriek-triangle).

Proof: Choose any cochain representative L of the underlying derived object K.
The termwise open-cover short exact sequence gives a distinguished triangle
in the unbounded derived category. Exact restriction and extension by zero
induce functors on D⁺; their comparison isomorphisms identify the first two
vertices with the images of the objects displayed in this statement. The
localization functor and the inclusion D⁺ → D preserve binary biproducts,
which identifies the middle vertices. Fullness of that inclusion lifts all
three arrows, using its shift comparison for the last arrow. The lifted
triangle is distinguished because the fully faithful triangulated inclusion
reflects distinguished triangles. A bounded-below representative need not
be chosen: boundedness is already supplied by the identified vertices in D⁺.
-/
theorem exists_distinguished_openCover_lowerShriek
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (K : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ (α : (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (U ⊓ V).ι).mapDerivedCategoryPlus.obj
        (((upperStar (ModuleCat.{u + 1} Λ) (U ⊓ V).ι).mapDerivedCategoryPlus).obj K) ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) U.ι).mapDerivedCategoryPlus.obj
        (((upperStar (ModuleCat.{u + 1} Λ) U.ι).mapDerivedCategoryPlus).obj K) ⊞
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus.obj
        (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K))
      (β : (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) U.ι).mapDerivedCategoryPlus.obj
        (((upperStar (ModuleCat.{u + 1} Λ) U.ι).mapDerivedCategoryPlus).obj K) ⊞
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus.obj
        (((upperStar (ModuleCat.{u + 1} Λ) V.ι).mapDerivedCategoryPlus).obj K) ⟶ K)
      (δ : K ⟶
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (U ⊓ V).ι).mapDerivedCategoryPlus.obj
          (((upperStar (ModuleCat.{u + 1} Λ) (U ⊓ V).ι).mapDerivedCategoryPlus).obj K))⟦(1 : ℤ)⟧),
      Triangle.mk α β δ ∈ distTriang
        (_root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) := by
  let J := _root_.DerivedCategory.Plus.ι
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let L := _root_.DerivedCategory.Q.objPreimage K.obj
  let e : _root_.DerivedCategory.Q.obj L ≅ K.obj :=
    _root_.DerivedCategory.Q.objObjPreimageIso K.obj
  let E (T : X.Opens) :=
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (((upperStar (ModuleCat.{u + 1} Λ) T.ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)
  let A (T : X.Opens) :=
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι).mapDerivedCategoryPlus.obj
      (((upperStar (ModuleCat.{u + 1} Λ) T.ι).mapDerivedCategoryPlus).obj K)
  let p (T : X.Opens) : J.obj (A T) ≅ _root_.DerivedCategory.Q.obj (E T) :=
    (Functor.mapDerivedCategoryPlusCompatibility
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι)).app _ ≪≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι).mapDerivedCategory.mapIso
      ((upperStar (ModuleCat.{u + 1} Λ) T.ι).mapDerivedCategoryPlusCompatibility.app K ≪≫
        (upperStar (ModuleCat.{u + 1} Λ) T.ι).mapDerivedCategory.mapIso e.symm ≪≫
        (upperStar (ModuleCat.{u + 1} Λ) T.ι).mapDerivedCategoryFactors.app L) ≪≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) T.ι).mapDerivedCategoryFactors.app _
  obtain ⟨α, β, hz, hS⟩ := exists_shortExact_openCover_lowerShriek_complex Λ U V hcover L
  let T := _root_.DerivedCategory.triangleOfSES hS
  have hT := _root_.DerivedCategory.triangleOfSES_distinguished hS
  have : PreservesBinaryBiproducts J := preservesBinaryBiproducts_of_preservesBiproducts J
  have : PreservesBinaryBiproducts
      (_root_.DerivedCategory.Q
        (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let pB : J.obj (A U ⊞ A V) ≅ _root_.DerivedCategory.Q.obj (E U ⊞ E V) :=
    J.mapBiprod _ _ ≪≫ biprod.mapIso (p U) (p V) ≪≫
      (_root_.DerivedCategory.Q.mapBiprod _ _).symm
  let a : A (U ⊓ V) ⟶ A U ⊞ A V := J.preimage ((p _).hom ≫ T.mor₁ ≫ pB.inv)
  let b : A U ⊞ A V ⟶ K := J.preimage (pB.hom ≫ T.mor₂ ≫ e.hom)
  let d : K ⟶ (A (U ⊓ V))⟦(1 : ℤ)⟧ := J.preimage
    (e.inv ≫ T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map (p _).inv ≫
      (J.commShiftIso (1 : ℤ)).inv.app (A (U ⊓ V)))
  refine ⟨a, b, d, (J.map_distinguished_iff _).mp ?_⟩
  apply isomorphic_distinguished T hT
  refine Triangle.isoMk _ _ (p _) pB e.symm ?_ ?_ ?_
  · change J.map a ≫ pB.hom = (p _).hom ≫ T.mor₁
    simp [a]
  · change J.map b ≫ e.inv = pB.hom ≫ T.mor₂
    simp [b]
  · change (J.map d ≫ (J.commShiftIso (1 : ℤ)).hom.app (A (U ⊓ V))) ≫
      (shiftFunctor _ (1 : ℤ)).map (p _).hom = e.inv ≫ T.mor₃
    simp [d, ← Functor.map_comp]

end AlgebraicGeometry.Etale
