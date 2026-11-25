/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientScalars

/-! # Normalized diagonal coefficient diagrams

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-diagrams).

## Main definitions

- `Family`: the coefficient stages and scalar compatibilities.
- `IntegralRoots`, `FiniteRoots`: projection-normalized root comparisons.
- `quotientMap`, `quotientLine`: the actual uniformizer reduction objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable (l : ℕ) [Fact l.Prime]

/-- The complete non-torsion coefficient diagram. Its maps are the actual finite
free, localization, and finite-subextension-colimit maps. Every member contains
both integration identities as equations in its coefficient-linear derived category.
Source: blueprint clauses 1--2
(blueprint: def-sfb-diagonal-coefficient-diagrams). -/
structure Family (Y : Scheme.{u}) where
  zl : Diagram (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y (zlLine l)
  integral : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    Diagram (Profinite.padicIntegersRingObj.{u} l E.1) Y (fun X ↦ spIntegralTwist X l E)
  rational : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    Diagram (Profinite.continuousMapRingObj.{u} E.1) Y (fun X ↦ spRationalTwist X l E)
  closure : Diagram (Profinite.padicAlgClRingObj.{u} l) Y (fun X ↦ spQbarTwist X l)
  toIntegral : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    ScalarCompatibility (integralMap l E) Y (zlLine l) (fun X ↦ spIntegralTwist X l E)
      (integralLineMap l E) zl (integral E)
  toRational : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    ScalarCompatibility (padicIntegersRingObjToContinuousMapRingObj l E) Y
      (fun X ↦ spIntegralTwist X l E) (fun X ↦ spRationalTwist X l E)
      (rationalLineMap l E) (integral E) (rational E)
  toClosure : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    ScalarCompatibility (Profinite.padicSubfieldRingObjToPadicAlgCl l E) Y
      (fun X ↦ spRationalTwist X l E) (fun X ↦ spQbarTwist X l)
      (closureLineMap l E) (rational E) closure
  rationalTransitions : ∀ (E F : PadicAlgCl.FiniteIntermediateField l) (h : E ≤ F),
    ScalarCompatibility (Profinite.padicSubfieldRingObjMap l h) Y
      (fun X ↦ spRationalTwist X l E) (fun X ↦ spRationalTwist X l F)
      (fun X ↦ spRationalTwistMap X l (E := E) (F := F) h) (rational E) (rational F)

/-- The canonical integral root map, specified by every projection of the actual
root and coefficient-root limits. This is data with a determining universal
property, not an arbitrary map of Tate lines. Source: blueprint coefficient
changes, proof steps 1 and 3a
(blueprint: def-sfb-diagonal-coefficient-diagrams). -/
structure IntegralRoots (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u}) where
  hom : Scheme.purTwistZlOne X l ⟶ (spIntegralTwist X l E).X
  projections : ∀ n : ℕ,
    hom ≫ (limit.π (spIntegralTwistSystem X l E) (op n)).hom =
      limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) ≫
        (Mod.freeForgetAdjunction (condensedRingObj (spEllPointRingObj l E n) X)).unit.app
          (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)))

/-- The finite-root comparison is fixed by the actual kernel inclusions into
units. Only the finite roots comparison is an isomorphism; the map from pulled
back etale units to all pro-etale units is the specified adjunction map.
Source: blueprint proof steps 1 and 3a
(blueprint: def-sfb-diagonal-coefficient-diagrams). -/
structure FiniteRoots (X : Scheme.{u}) (N : ℕ) where
  iso : (comparisonUpperStar Ab.{u + 1} X).obj (X.rootsOfUnitySheaf N) ≅
    Scheme.proEtaleRootsOfUnitySheaf X N
  inclusion : iso.hom ≫ Scheme.proEtaleRootsOfUnityInclusion X N =
    (comparisonUpperStar Ab.{u + 1} X).map (kernel.ι (N • 𝟙 X.gmSheaf)) ≫
      cartierUnitsComparison X

/-- The canonical root-to-finite-line map, using the kernel-normalized root
comparison and the scalar-forgetting comparison of site inverse images.
Source: blueprint proof step 1, torsion Cartier normalization
(blueprint: def-sfb-diagonal-coefficient-diagrams). -/
def FiniteRoots.toLine {X : Scheme.{u}} {N : ℕ} (r : FiniteRoots X N)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    Scheme.proEtaleRootsOfUnitySheaf X N ⟶
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).obj (geoCartierLine A N hA X) :=
  r.iso.inv ≫ (comparisonUpperStar Ab.{u + 1} X).map
    (Etale.ordinaryFiniteRootMap A N hA X) ≫
      (forgetComparisonIso A X).hom.app (Scheme.finiteEtaleTateLine X N A hA)

/-- The actual uniformizer quotient map on condensed rings. Level n is exponent
n+1. Source: blueprint clause 1, every uniformizer quotient
(blueprint: def-sfb-diagonal-coefficient-diagrams). -/
def quotientMap (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) :
    Profinite.padicIntegersRingObj.{u} l E.1 ⟶
      Profinite.continuousMapRingObj.{u} (completedResidue l E π n) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (completedReduction l E π n)

/-- Quotient is a map of ring objects. Source: blueprint clause 1
(blueprint: def-sfb-diagonal-coefficient-diagrams). -/
instance quotientMap_isMonHom (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) : IsMonHom (quotientMap.{u} l E π n) := by
  dsimp only [quotientMap]
  infer_instance

/-- The ordinary quotient line; derived reduction agrees with it through the
adjoint-normalized endpoint of ScalarCompatibility. Source: blueprint clause 1
(blueprint: def-sfb-diagonal-coefficient-diagrams). -/
def quotientLine (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) (X : Scheme.{u}) :
    Modules (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) X :=
  (Mod.extendScalars (coefficientMap (quotientMap l E π n) X)).obj (spIntegralTwist X l E)

/-- The integral-to-quotient line map is the actual extension unit. Source:
blueprint clause 1 (blueprint: def-sfb-diagonal-coefficient-diagrams). -/
def quotientLineMap (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) (X : Scheme.{u}) :
    (spIntegralTwist X l E).X ⟶ (quotientLine l E π n X).X :=
  Mod.extendUnitHom (coefficientMap (quotientMap l E π n) X) (spIntegralTwist X l E)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
