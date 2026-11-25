/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceFactors
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientSquare
public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap

/-! # Concrete formulas for raw scalar comparison
Source: Stacks Project, Tags 03FD, 03Q8 and 03D7.
(blueprint: lem-sbc-raw-scalar-hom-evaluation).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local instance] moduleSheafCategory moduleSheafPreadditive moduleSheafAbelian
  moduleSheafHasDerivedCategory

/-- Evaluation of the explicit additive scalar Hom map.
Source: Stacks Project, Tags 03FD and 03Q8, formula-expansion step of
lem-sbc-raw-module-abelian-hom-map-naturality.
(blueprint: lem-sbc-raw-scalar-hom-evaluation).

Proof: Expand the definition of rawModuleAbelianHomMap. Its additive map is the composite of
derived forgetting, right composition by the coefficient factor, and left composition by the
source factor. Evaluation of AddCommGrpCat.ofHom and of the two additive compositions therefore
gives c composed with V(z) composed with b. The two named factor definitions have exactly these
source and coefficient bodies. No naturality or coherence equation is used. This applies to zero
classes, zero sheaves, identity geometric maps and degree zero. -/
theorem rawModuleScalarHom_evaluate
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A : Over W)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op A)) :
    rawModuleAbelianHomMap Λ k G q U A z =
      scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus.map z ≫
        scalarCoefficientFactor Λ A.hom G (q : ℤ) := by
  rfl

end AlgebraicGeometry.Etale
