/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.Algebra.Homology.ResidueKernelUnitMinor

/-! # Local freeness of the first cokernel under universal rank-one H0

Source: Stacks Project, Tags 00O0 and 00NX, local matrix argument.
(blueprint: new-universal-h0-cokernel-local-free)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex

-- The freeness of C permits cancellation of c in every basis coordinate.
private theorem kernel_equiv_ring_forces_zero
    {A : Type v} [CommRing A] {C : Type v} [AddCommGroup C] [Module A C]
    [Module.Free A C] (g : A →ₗ[A] C) (e : LinearMap.ker g ≃ₗ[A] A) : g = 0 := by
  let k : A →ₗ[A] A := (LinearMap.ker g).subtype.comp e.symm.toLinearMap
  have hk : Function.Injective k :=
    (LinearMap.ker g).injective_subtype.comp e.symm.injective
  have hk_apply (x : A) : k x = x * k 1 := by
    simpa using k.map_smul x (1 : A)
  have hgc : g (k 1) = 0 := (e.symm 1).property
  have hgc' : k 1 • g 1 = 0 := by
    have hm : g (k 1) = k 1 • g 1 := by simpa using g.map_smul (k 1) (1 : A)
    exact hm.symm.trans hgc
  let b := Module.Free.chooseBasis A C
  have hg1 : g 1 = 0 := by
    apply b.repr.injective
    ext i
    have hcoord : k 1 * b.repr (g 1) i = 0 := by
      simpa using congrArg (fun z : C ↦ b.repr z i) hgc'
    have hki : k (b.repr (g 1) i) = k 0 := by
      rw [hk_apply, mul_comm, hcoord, map_zero]
    simpa using hk hki
  apply LinearMap.ext
  intro x
  simpa [hg1] using g.map_smul x (1 : A)

-- With no incoming differential, the homology projection identifies cycles with H0.
private theorem h0_kernel_test
    (R B : Type v) [CommRing R] [CommRing B] (φ : R →+* B)
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (hneg : IsZero (P.X (-1)))
    (hH : Nonempty
      ((((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P).homology 0
        ≅ ModuleCat.of B B)) :
    Nonempty (LinearMap.ker ((ModuleCat.extendScalars φ).map (P.d 0 1)).hom ≃ₗ[B] B) := by
  let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
  have hnegB : IsZero (PB.X (-1)) := (ModuleCat.extendScalars φ).map_isZero hneg
  let S := PB.sc' (-1) 0 1
  have hf : S.f = 0 := hnegB.eq_of_src _ _
  let e : ModuleCat.of B (LinearMap.ker S.g.hom) ≅ S.homology :=
    S.moduleCatCyclesIso.symm ≪≫ S.asIsoHomologyπ hf
  let j : PB.sc 0 ≅ S := PB.isoSc' (-1) 0 1
    ((ComplexShape.up ℤ).prev_eq' (by decide))
    ((ComplexShape.up ℤ).next_eq' (by decide))
  obtain ⟨h⟩ := hH
  exact ⟨(e ≪≫ (ShortComplex.homologyMapIso j).symm ≪≫ h).toLinearEquiv⟩

/-- The cokernel of the first differential is free at every prime.

Source: Stacks Project, Tags 00O0 (unit-minor calculation) and 00NX
(finite projective modules are free at primes).

Proof: Since the degree-minus-one term is zero, after any scalar extension
H0 is the kernel of the degree-zero differential. At a prime of R the finite
projective source and target become finite free over the local ring A. Test the
hypothesis with its residue field: the matrix has kernel dimension one, hence
an invertible minor of size n-1, where n is the source rank. Row and column
operations reduce it to an identity block and a map A to a finite free module.
Test the hypothesis with A itself: the remaining kernel is isomorphic to A.
Its injection into A is multiplication by some c. This multiplication is
injective. Every entry of the remaining map annihilates c, so every entry is
zero. The localized cokernel is consequently free. Localization is exact, so it
is the localization of the quotient by the global image.
For n=1 the identity block is empty. Rank zero cannot occur over a nonzero
local ring, by the residue-field test. Over the zero ring all modules are zero.
(blueprint: new-universal-h0-cokernel-local-free) -/
theorem universalH0_cokernel_local_free
    (R : Type v) [CommRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hf0 : Module.Finite R (P.X 0))
    (hf1 : Module.Finite R (P.X 1))
    (hp0 : Module.Projective R (P.X 0))
    (hp1 : Module.Projective R (P.X 1))
    (hneg : IsZero (P.X (-1)))
    (hzero : ∀ (B : Type v) [CommRing B] (φ : R →+* B),
      let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
      Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) :
    ∀ (𝔭 : Ideal R) [𝔭.IsPrime], Module.Free (Localization.AtPrime 𝔭)
      (LocalizedModule 𝔭.primeCompl (P.X 1 ⧸ LinearMap.range (P.d 0 1).hom)) := by
  intro 𝔭 h𝔭
  let A := Localization.AtPrime 𝔭
  let κ := IsLocalRing.ResidueField A
  let φ : R →+* κ := (IsLocalRing.residue A).comp (algebraMap R A)
  have hres := h0_kernel_test R κ φ P hneg (hzero κ φ)
  obtain ⟨C, g, hfree, ⟨e⟩, ⟨q⟩⟩ :=
    ModuleCat.residue_kernel_unit_minor R (P.X 0) (P.X 1) (P.d 0 1)
      hf0 hf1 hp0 hp1 𝔭 hres
  obtain ⟨eA⟩ := h0_kernel_test R A (algebraMap R A) P hneg (hzero A (algebraMap R A))
  let : Module.Free A C := hfree
  have hg : g = 0 := kernel_equiv_ring_forces_zero g (e.trans eA)
  have hquot : Module.Free (Localization.AtPrime 𝔭) (C ⧸ LinearMap.range g) := by
    rw [hg, LinearMap.range_zero]
    exact Module.Free.of_equiv
      ((⊥ : Submodule (Localization.AtPrime 𝔭) C).quotEquivOfEqBot rfl).symm
  let : Module.Free (Localization.AtPrime 𝔭) (C ⧸ LinearMap.range g) := hquot
  exact Module.Free.of_equiv q.symm

end CochainComplex
