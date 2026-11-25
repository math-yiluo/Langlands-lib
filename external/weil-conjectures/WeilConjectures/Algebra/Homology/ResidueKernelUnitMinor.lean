/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

import WeilConjectures.Algebra.Homology.ResidueKernelUnitMinorKernel
import WeilConjectures.Algebra.Homology.ResidueKernelUnitMinorQuotient
import WeilConjectures.Algebra.Homology.ResidueKernelLocalizedCokernel

/-! # Unit-minor reduction for a residue rank-one kernel

Source: Stacks Project, Tags 00O0 and 00NX, local matrix argument.
(blueprint: new-residue-kernel-unit-minor)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace ModuleCat

/-- The unit-minor step reduces the localized cokernel to the cokernel of a
map with rank-one source, retaining the entire localized kernel.

Source: Stacks Project, Tags 00O0 and 00NX, the unit-minor calculation.
Proof:
1. Localize the finite projective source and target at p. They are finite free
   over A = R_p (Tag 00NX). Scalar extension agrees with localization, and
   tensor associativity identifies the residue map with f tensor kappa(p).
2. Choose finite bases. By hres and rank-nullity the residue matrix has rank
   n-1, where n is the source rank. In particular n is positive. Select n-1
   independent columns and n-1 rows giving a nonzero square residue minor;
   its lifted determinant is a unit in the local ring A (Tag 00O0 argument).
3. Permute these columns and rows to the front and write f in block form
   [[B,b],[D,d]], with B invertible. The source operation
   (u,a) -> (u - B inverse b a,a) and target operation
   (y,z) -> (B inverse y,z - D B inverse y) change it to diag(id,g),
   where g(a) = (d - D B inverse b)a. Both operations have explicit inverses
   obtained by reversing the elementary operations. Set C to the free module
   on the remaining target coordinates. For n=1 the B block is empty.
4. In this normal form, (u,a) lies in the kernel exactly when u=0 and g(a)=0.
   Including a as (0,a), then undoing the source operation, gives the kernel
   equivalence; its inverse extracts the last source coordinate.
5. Project the normal-form target onto C / range(g). This map is surjective
   and its kernel is precisely the image of diag(id,g), since that image
   consists of pairs (u,g(a)). The first isomorphism theorem gives the
   quotient equivalence. Localization is exact: localizedQuotientEquiv and
   the localized-range identity identify the global localized quotient with
   this cokernel. A prime localization is nonzero; n=0 is excluded by hres.
The conclusion retains a potentially nonzero g; its vanishing requires the
separate local-ring kernel test in the parent theorem.
(blueprint: new-residue-kernel-unit-minor) -/
theorem residue_kernel_unit_minor
    (R : Type v) [CommRing R] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (hfX : Module.Finite R X) (hfY : Module.Finite R Y)
    (hpX : Module.Projective R X) (hpY : Module.Projective R Y)
    (𝔭 : Ideal R) [𝔭.IsPrime]
    (hres : Nonempty (LinearMap.ker ((ModuleCat.extendScalars
      ((IsLocalRing.residue (Localization.AtPrime 𝔭)).comp
        (algebraMap R (Localization.AtPrime 𝔭)))).map f).hom
      ≃ₗ[IsLocalRing.ResidueField (Localization.AtPrime 𝔭)]
        IsLocalRing.ResidueField (Localization.AtPrime 𝔭))) :
    ∃ (C : ModuleCat.{v} (Localization.AtPrime 𝔭))
      (g : Localization.AtPrime 𝔭 →ₗ[Localization.AtPrime 𝔭] C),
      Module.Free (Localization.AtPrime 𝔭) C ∧
      Nonempty (LinearMap.ker g ≃ₗ[Localization.AtPrime 𝔭]
        LinearMap.ker ((ModuleCat.extendScalars
          (algebraMap R (Localization.AtPrime 𝔭))).map f).hom) ∧
      Nonempty (LocalizedModule 𝔭.primeCompl (Y ⧸ LinearMap.range f.hom)
        ≃ₗ[Localization.AtPrime 𝔭] (C ⧸ LinearMap.range g)) := by
  obtain ⟨U, C, g, hfree, eX, eY, hdiag⟩ :=
    residue_kernel_unit_minor_normal_form R X Y f hfX hfY hpX hpY 𝔭 hres
  obtain ⟨hker, hcoker⟩ := residue_kernel_unit_minor_quotient
    (Localization.AtPrime 𝔭) _ _ U C
    ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime 𝔭))).map f).hom
    g eX eY hdiag
  obtain ⟨eLoc⟩ := residue_kernel_localized_cokernel R X Y f 𝔭
  obtain ⟨eCoker⟩ := hcoker
  exact ⟨C, g, hfree, hker, ⟨eLoc.trans eCoker⟩⟩

end ModuleCat
