/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement

import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownCanonicalScalarCube
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownInverseRepresentative

/-! # Open scalar transport decomposition

Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16;
Stacks 03CY, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- Scalar extension respects a normalized inverse-image realization.
Source: Zheng Construction 4.1 and Lemma 5.16; Stacks 03CY, 06YY and 07A4.
(blueprint: lem-pur-etale-brown-scalar-inverse-realization-cube).

Proof: first take scalar mates of both sides. The realization scalar comparisons
become the recorded restriction comparisons; the coefficient-system tensor comparison
becomes the ordinary restriction/inverse-image comparison by tensor_unit and the
derived Hom transpose formulas. On ordinary modules the resulting cube commutes:
apply the faithful underlying set-sheaf functor, use restrictInverseUnderlying, and
use the section identity for ordinaryRestriction. Both paths are the pullback of
the same section. Prolong to complexes. The supplied inverse representative equations
and restriction representative equations identify its localized faces. For the
nonexact scalar faces choose flat-term K-flat resolutions, apply derivedTensor_rep
and the scalar computation counits, and cancel their invertible components.
Naturality transports the equality from these resolutions to every derived input.
Taking inverse scalar mates gives exactly the displayed cube. No finiteness,
flatness of the quotient map, boundedness, or open-immersion hypothesis is used. -/
theorem etaleBrownScalarInverseRealization_cube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (r : ∀ n, StrictEtaleBrownImageRealization O t g n A (B.level n) RV RW)
    (e : ∀ n, (A.lift n).modules ⋙ strictEtaleBrownConstant O t V n ≅
        strictEtaleBrownConstant O t W n ⋙
          Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
    (_he : letI := RV.val.ordinaryAdditive
      letI := RW.val.ordinaryAdditive
      ∀ n (K : CochainComplex (strictEtaleLevel W O t n) ℤ),
        (r n).inverse.inv.app (DerivedCategory.Q.obj K) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            g).mapDerivedCategory.map ((RW.factors n).hom.app K) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            g).mapDerivedCategoryFactors.hom.app
            (((strictEtaleBrownConstant O t W n).mapHomologicalComplex (.up ℤ)).obj K) =
        (RV.derived n).map ((B.level n).inverseFactors.hom.app K) ≫
          (RV.factors n).hom.app (((A.lift n).modules.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (e n) (.up ℤ)).hom.app K))
    {m n : ℕ} (h : m ≤ n) (K : DerivedCategory (strictEtaleLevel W O t n)) :
    (RV.derived m).map ((B.derivedTensor h).inv.app K) ≫
      (r m).inverse.inv.app ((PW.scalar h).derived.obj K) ≫
      (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m))
        g).mapDerivedCategory.map ((RW.scalar h).hom.app K) =
    (RV.scalar h).hom.app ((B.level n).inverse.obj K) ≫
      (Etale.scalarExtension (strictEtaleBrownRingMap O t h) V).map ((r n).inverse.inv.app K) ≫
      (Etale.properOpenCoefficientPullbackIso (strictEtaleBrownRingMap O t h) g).inv.app
        ((RW.derived n).obj K) := by
  have hc := strictEtaleBrownCanonicalScalarCube O t g A PW PV B RV RW r
    (fun k K ↦ strictEtaleBrownInverse_representative O t g k A (B.level k) RV RW (r k) K) h K
  simp only [strictEtaleBrownCanonicalRestriction_mate, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, isoWhiskerLeft_inv, whiskerLeft_app, Functor.map_comp,
    Category.assoc] at hc
  rw [← cancel_epi ((RV.scalar h).inv.app _), ← cancel_epi
    ((Etale.scalarExtension (strictEtaleBrownRingMap O t h) V).map ((r n).inverse.hom.app K)),
    ← cancel_epi ((Etale.scalarExtension (strictEtaleBrownRingMap O t h) V).map
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).hom.app ((RW.derived n).obj K)))]
  rw [reassoc_of% hc]
  simp [Etale.properOpenCoefficientPullbackIso]

end AlgebraicGeometry
