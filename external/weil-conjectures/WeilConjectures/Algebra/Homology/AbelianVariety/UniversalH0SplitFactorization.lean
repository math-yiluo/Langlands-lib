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

import Mathlib.RingTheory.LocalProperties.Projective
import WeilConjectures.Algebra.Homology.UniversalH0CokernelLocalFree

/-! Factorization data for a generalized inverse.

This is the algebraic splitting output of the universal rank-one kernel argument.
The existence of the factorization is the local matrix and projectivity argument
from Stacks Project, Tags 00O0 and 00NX.
(blueprint: new-universal-h0-split-factorization)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex

/-- The local algebra argument supplies a split factorization of the first
 differential through an intermediate projective direct summand.

The proof is the local matrix and projective-cokernel argument of Stacks
Project, Tags 00O0 and 00NX: localize at primes, reduce the finite projective
map to an identity block and a zero block using the rank-one residue-kernel
hypothesis, then use finite presentation and local freeness to obtain a
projective cokernel. Splitting the quotient and the induced surjection onto
the image yields the displayed maps and identities.
(blueprint: new-universal-h0-split-factorization) -/
-- The former identity e ≫ r = 𝟙 (P.X 0) incorrectly made d injective.
theorem universalH0_split_factorization
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
    ∃ (I : ModuleCat.{v} R) (e : P.X 0 ⟶ I) (p : I ⟶ P.X 1)
      (r : I ⟶ P.X 0) (q : P.X 1 ⟶ I),
      P.d 0 1 = e ≫ p ∧ r ≫ e = 𝟙 I ∧ p ≫ q = 𝟙 I := by
  let f := (P.d 0 1).hom
  let K := LinearMap.range f
  let : Module.Finite R (P.X 0) := hf0
  let : Module.Finite R (P.X 1) := hf1
  let : Module.Projective R (P.X 1) := hp1
  let : Module.FinitePresentation R (P.X 1) := Module.finitePresentation_of_projective R _
  let : Module.FinitePresentation R (P.X 1 ⧸ K) :=
    Module.finitePresentation_of_surjective K.mkQ
      (LinearMap.range_eq_top.mp K.range_mkQ) (by
        rw [Submodule.ker_mkQ]
        exact Submodule.fg_range f)
  have hproj : Module.Projective R (P.X 1 ⧸ K) := by
    apply Module.projective_of_localization_maximal
    intro 𝔪 h𝔪
    let : 𝔪.IsMaximal := h𝔪
    let : Module.Free (Localization.AtPrime 𝔪)
        (LocalizedModule 𝔪.primeCompl (P.X 1 ⧸ K)) :=
      universalH0_cokernel_local_free R P hf0 hf1 hp0 hp1 hneg hzero 𝔪
    infer_instance
  obtain ⟨t, ht⟩ := Module.projective_lifting_property K.mkQ
    (LinearMap.id : (P.X 1 ⧸ K) →ₗ[R] (P.X 1 ⧸ K))
    (LinearMap.range_eq_top.mp K.range_mkQ)
  let a : P.X 1 →ₗ[R] P.X 1 := LinearMap.id - t.comp K.mkQ
  have ha (x : P.X 1) : a x ∈ K := by
    rw [← K.ker_mkQ, LinearMap.mem_ker]
    change K.mkQ (x - t (K.mkQ x)) = 0
    simpa only [map_sub, LinearMap.comp_apply, LinearMap.id_apply] using
      sub_eq_zero.mpr (DFunLike.congr_fun ht (K.mkQ x)).symm
  let q : P.X 1 →ₗ[R] K := a.codRestrict K ha
  have hq : q.comp K.subtype = LinearMap.id := by
    ext x
    change (x : P.X 1) - t (K.mkQ x) = x
    have hx : K.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero K).mpr x.property
    rw [hx, map_zero, sub_zero]
  let : Module.Projective R K := Module.Projective.of_split K.subtype q hq
  obtain ⟨r, hr⟩ := Module.projective_lifting_property f.rangeRestrict
    (LinearMap.id : K →ₗ[R] K) f.surjective_rangeRestrict
  refine ⟨ModuleCat.of R K, ModuleCat.ofHom f.rangeRestrict,
    ModuleCat.ofHom K.subtype, ModuleCat.ofHom r, ModuleCat.ofHom q, ?_, ?_, ?_⟩
  · ext x
    rfl
  · exact ModuleCat.hom_ext hr
  · exact ModuleCat.hom_ext hq

end CochainComplex
