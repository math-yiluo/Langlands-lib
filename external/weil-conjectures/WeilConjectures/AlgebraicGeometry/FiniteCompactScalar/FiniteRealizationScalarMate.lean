/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactScalarCoordinates
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteRealizationRestrictionCube
import all WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage

/-! # Scalar direct-image mates under intrinsic realization -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
attribute [local implicit_reducible] CategoryTheory.Equivalence.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence
namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- Intrinsic realization respects the direct-image scalar mate on the entire
unbounded fixed-scalar pro-etale category. This assertion involves no change of site.

Source: Stacks Tags 0D6E, 0D6J and 07A6; the realization/restriction cube in
`lem-finite-proper-scalar-transport`, proof Steps 1 and 2.
(blueprint: lem-finite-realization-scalar-mate).

Proof: evaluate the restriction/direct-image square on a K-injective B-complex
and a K-injective resolution of its restriction. The normalizations of
sfDerivedImageRestriction, fixedScalarRestrictionDirectImage and
sfIntrinsicDerivedDirectImageComparison identify both paths after realization
with direct image of the resolution arrow. The underived realization square is
the sectionwise coefficient square. Cancel the common quasi-isomorphisms and
use naturality and K-injective representatives to obtain the derived square.
Transpose that square under the coefficient adjunctions. The comparison of
left adjoints is realizationScalarIso, since it is defined by the same inverse
realization/restriction square. The iterated-mates identity identifies the
fixed-scalar transpose with the geometric mate of scalarPullbackProEtaleIso.
This gives the displayed equality on every object, without properness,
boundedness or coefficient flatness. Universal properties and the triangle
identities include the zero ring, zero complex and empty scheme. -/
theorem realizationScalar_directImage_mate
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (K : DerivedCategory
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    ((pbcDerivedScalarAdjunction (scalarRingMap φ Y)).homEquiv _ _).symm
        ((proEtaleConstantDerivedDirectImage g A).map
            ((pbcDerivedScalarAdjunction (scalarRingMap φ Z)).unit.app
              ((sfIntrinsicDerivedEquivalence Z A).functor.obj K)) ≫
          (sfDerivedImageRestriction g φ).hom.app
            ((pbcDerivedExtend (scalarRingMap φ Z)).obj
              ((sfIntrinsicDerivedEquivalence Z A).functor.obj K))) ≫
      (proEtaleConstantDerivedDirectImage g B).map
        ((realizationScalarIso φ Z).hom.app K) ≫
      (sfIntrinsicDerivedDirectImageComparison g B).hom.app
        ((ProEtale.pbcFixedScalarExtension (ProEt.topology Z)
          (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj K) =
    (pbcDerivedExtend (scalarRingMap φ Y)).map
        ((sfIntrinsicDerivedDirectImageComparison g A).hom.app K) ≫
      (realizationScalarIso φ Y).hom.app
        ((ProEtale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).rightDerivedFunctor.obj K) ≫
      (sfIntrinsicDerivedEquivalence Y B).functor.map
        ((mateEquiv
          (ProEtale.derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
          (ProEtale.derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g)
          (TwoSquare.mk _ _ _ _ (ProEtale.scalarPullbackProEtaleIso
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) g).hom)).app K) := by
  let a := RingHom.ulift.{u + 1, u + 1, u, u} φ
  let b (T : Scheme.{u}) := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (ProEt.topology T) a)
  have hn (T : Scheme.{u}) (M : DerivedCategory
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
      (pbcDerivedScalarAdjunction (scalarRingMap φ T)).unit.app
          ((sfIntrinsicDerivedEquivalence T A).functor.obj M) ≫
        (pbcDerivedRestrict (scalarRingMap φ T)).map
          ((realizationScalarIso φ T).hom.app M) ≫
        (realizationRestrictionIso φ T).hom.app
          ((ProEtale.pbcFixedScalarExtension (ProEt.topology T) a).obj M) =
      (sfIntrinsicDerivedEquivalence T A).functor.map ((b T).unit.app M) := by
    -- Normalize the equality cast in the chosen inverse restriction square explicitly.
    simpa only [realizationScalarIso, realizationRestrictionIso, realizationRestrictionRightIso,
      ProEtale.pbcFixedScalarExtension, pbcDerivedRestrict, pbcRestrict, scalarRingMap,
      proEtaleConstantRingMap, proEtaleCoefficientRestrictScalars, sfFixedRestriction,
      Sheaf.restrictScalars, Sheaf.derivedRestrictScalars, Functor.id_obj, Functor.comp_obj,
      eq_mpr_eq_cast, cast_eq, id_eq, a, b] using
      realizationScalar_unit (sfIntrinsicDerivedEquivalence T A)
        (sfIntrinsicDerivedEquivalence T B)
        (pbcDerivedScalarAdjunction (scalarRingMap φ T)) (b T)
        (realizationRestrictionRightIso φ T) M
  have hs : (mateEquiv (b Y) (b Z)
      (ProEtale.scalarPullbackProEtaleIso a g).inv) =
      (ProEtale.leftDerivedUpperStarRestrictScalarsIso a g).hom := by
    change (mateEquiv (b Y) (b Z))
      ((mateEquiv (b Y) (b Z)).symm
        (TwoSquare.mk _ _ _ _
          (ProEtale.leftDerivedUpperStarRestrictScalarsIso a g).hom)) = _
    exact Equiv.apply_symm_apply _ _
  have hm := scalarTranspose_inverse_mate
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g)
    (b Y) (b Z) (ProEtale.leftDerivedUpperStarRestrictScalarsIso a g)
    (ProEtale.scalarPullbackProEtaleIso a g).symm
    (ProEtale.fixedScalarRestrictionDirectImage a g) hs (by rfl) K
  have h := scalarTranspose_realization_cube
    (pbcDerivedScalarAdjunction (scalarRingMap φ Z))
    (pbcDerivedScalarAdjunction (scalarRingMap φ Y)) (b Z) (b Y)
    (realizationScalarIso φ Z) (realizationScalarIso φ Y)
    (realizationRestrictionIso φ Z) (realizationRestrictionIso φ Y)
    (sfIntrinsicDerivedDirectImageComparison g A)
    (sfIntrinsicDerivedDirectImageComparison g B)
    (sfDerivedImageRestriction g φ) (ProEtale.fixedScalarRestrictionDirectImage a g)
    (hn Z) (hn Y) (realizationRestriction_directImage_cube φ g) K
  simp only [Functor.id_obj] at hm h
  rw [hm] at h
  simpa only [ProEtale.pbcFixedScalarExtension, Functor.id_obj, TwoSquare.mk,
    Iso.symm_inv, a] using h

end AlgebraicGeometry.Scheme.FiniteCompactScalar
