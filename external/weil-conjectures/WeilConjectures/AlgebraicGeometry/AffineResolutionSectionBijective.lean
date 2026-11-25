/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

import WeilConjectures.AlgebraicGeometry.SectionCohomologyThetaAcyclic
import WeilConjectures.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-! # Bijectivity of the normalized affine section class map

Source: Stacks Project, Tags 01F4, 01XJ and 01E4.
(blueprint: lem-pc-affine-resolution-section-bijective)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- The canonical restricted-resolution class map is bijective over an affine base open.
There is no Ext comparison or choice of cohomology coordinates in this assertion.
Source: Stacks Project, Tags 01F4 (2), 01XJ (1), 01E4 and 01E5.
(blueprint: lem-pc-affine-resolution-section-bijective)

Proof: Set U = f inverse V, g = f restricted to U -> V, and M = F restricted to U.
Restriction preserves quasi-coherence, and g is qcqs by base change. Its ordinary higher
images are quasi-coherent by 01XJ. Their positive cohomology vanishes because V is affine.
Thus the cocycle-defined Leray edge in 01F4 is invertible. Open restriction identifies its
target with sections over V of R^p f_* F. To identify the particular map, represent a
cohomology class by a cocycle in the global section complex of R.resolution. The equation
R.components sends this cocycle to its restriction in the original resolution I on U.
R.augmentation makes the induced comparison the identity on the resolved module, so the
resolution comparisons induce the same derived class. The cocycle formula for the edge
sends that representative to its class in the homology sheaf of f_* I. Exact evaluation
and the sheafification unit give precisely sectionCohomologyTheta by 01E4. Composing with
the inverse of I.isoRightDerivedObj gives the displayed map. Since all other maps are
isomorphisms, this class map is bijective. At p = 0 the argument is the augmentation
comparison; for empty V or zero F it is the unique map between zero groups. -/
theorem affine_resolutionSectionClass_bijective
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (I : InjectiveResolution F)
    (p : ℕ) (V : S.Opens) (hV : IsAffineOpen V)
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ V)) :
    Function.Bijective
      (resolutionSectionClass R.resolution
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
      V R.sections p ≫ Hom.app (I.isoRightDerivedObj (pushforward f) p).inv V) := by
  let K := (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  have hterms (n r : ℕ) (hr : 0 < r) :
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj (K.X n))) :=
    (module_pushforward_injective_acyclic f (I.cocomplex.X n)).1 V r hr
  have hhomology (n r : ℕ) (hr : 0 < r) :
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace r).obj
        ((restrictFunctor V.ι).obj (K.homology n))) := by
    have hqc := ordinaryHigherImage_isQuasicoherent f F inferInstance n
    have : (K.homology n).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
        (I.isoRightDerivedObj (pushforward f) n) hqc
    have : IsAffine V.toScheme := hV
    obtain ⟨b, _⟩ := exists_moduleCohomology_source_comparison V.toScheme r
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    have : Subsingleton (((restrictFunctor V.ι).obj (K.homology n)).H (k + 1)) :=
      subsingleton_H_succ_of_isAffine _ k
    have : Subsingleton ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace
        (k + 1)).obj ((restrictFunctor V.ι).obj (K.homology n))) :=
      (b ((restrictFunctor V.ι).obj (K.homology n))).toEquiv.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  have := sectionCohomologyTheta_isIso_of_acyclic K V hterms hhomology p
  have hc : IsIso (resolutionSectionClass R.resolution K V R.sections p) := by
    dsimp only [resolutionSectionClass]
    infer_instance
  have hd : IsIso (Hom.app (I.isoRightDerivedObj (pushforward f) p).inv V) := by
    change IsIso ((RingedSpace.openModuleSections S.toRingedSpace V).map
      (I.isoRightDerivedObj (pushforward f) p).inv)
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

end AlgebraicGeometry.Scheme.Modules
