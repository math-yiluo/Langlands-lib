/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.CoherentGenericFilteredSource
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.Algebra.Homology.ModuleStalkExact

/-! # Generic inclusions with filtered source

Source: Stacks Project, Tags 01YE and 01YF, generic-point ideal inclusion and cokernel reduction.
(blueprint: lem-pc-s3-coherent-generic-filtered-extension)
-/

@[expose] public section

universe u

open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A generic ideal-sum inclusion with filtered source and smaller-support cokernel.

Source: Stacks Project, Tag 01YE and Tag 01YF, final generic-point paragraph
(https://stacks.math.columbia.edu/tag/01YE).
(blueprint: lem-pc-s3-coherent-generic-filtered-extension)

Proof: give T its reduced induced closed subscheme structure i : Z -> X.
Generic-point uniqueness identifies i(genericPoint Z) with ξ, and Z is integral.
Tag 01YE applied to the generic-annihilation hypothesis constructs a coherent
ideal I on Z, a finite rank r and a mono alpha : i_*(I^r) -> F which is an
isomorphism near ξ. Since ξ belongs to Supp F, its stalk is nonzero; consequently
r is positive and I is nonzero. Closed pushforward preserves coherence and
finite sums. The partial-sum chain of copies of i_*I therefore gives a coherent
integral filtration of A = i_*(I^r), each quotient being i_*I. Set Q to the actual
cokernel of alpha and g to its cokernel projection. Coherent cokernel closure
gives coherence of Q, and the mono alpha makes its cokernel sequence short
exact. Stalk exactness gives Supp Q contained in Supp F = T, while invertibility
near ξ gives Q_xi = 0. Since ξ belongs to T, containment is strict. This proves
the assertions without support induction and without claiming a filtration of F.
There is no zero-support case because a generic point belongs to its closed set. -/
theorem coherent_generic_filtered_extension
    (X : Scheme.{u}) [IsNoetherian X]
    (T : TopologicalSpace.Closeds X) (ξ : X)
    (hξ : IsGenericPoint ξ (T : Set X))
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = (T : Set X))
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ),
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj F, a • m = 0) :
    ∃ (A Q : X.Modules) (f : A ⟶ F) (g : F ⟶ Q) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧
      RingedSpace.IsCoherent X.toRingedSpace A ∧
      RingedSpace.IsCoherent X.toRingedSpace Q ∧ HasCoherentIntegralFiltration A ∧
      {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} ⊂ (T : Set X) := by
  classical
  let J := Scheme.IdealSheafData.vanishingIdeal T
  let Z := J.subscheme
  let i : Z ⟶ X := J.subschemeι
  have hred := Scheme.IdealSheafData.reduced_induced_closed_subscheme X T
  have : IsReduced Z := hred.2.2.2.1
  have hrange : Set.range i.base = (T : Set X) := hred.2.2.2.2.2.1
  let e : Z ≃ₜ (T : Set X) :=
    i.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have : IrreducibleSpace (T : Set X) := Subtype.irreducibleSpace hξ.isIrreducible
  have : IrreducibleSpace Z := e.irreducibleSpace_iff.mpr inferInstance
  have : IsIntegral Z := isIntegral_of_irreducibleSpace_of_isReduced Z
  have hpoint : i (genericPoint Z) = ξ := by
    have h := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, hrange, T.isClosed.closure_eq] at h
    exact h.eq hξ
  have hkill' : ∀ a ∈ IsLocalRing.maximalIdeal
      (X.presheaf.stalk (i.base (genericPoint Z))),
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint Z))).obj F, a • m = 0 := by
    rw [hpoint]
    exact hkill
  have hx : ¬ Subsingleton (F.presheaf.stalk (i.base (genericPoint Z))) := by
    have hx' : ξ ∈ {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := by
      rw [hSupp]
      exact hξ.mem
    rw [hpoint]
    exact hx'
  obtain ⟨A, α, hα, hA, hfil, hsurj⟩ :=
    coherent_generic_filtered_source i F hF hx hkill'
  have : Mono α := hα
  have hQ := (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).1
    A F α hA hF |>.2
  have qsurj (y : X) : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace y).map (cokernel.π α)) := by
    have : Epi ((RingedSpace.moduleStalkFunctor X.toRingedSpace y).map
        (cokernel.π α)) :=
      ((RingedSpace.module_stalk_exact X.toRingedSpace α).2.2.1 y).1
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hQx : Subsingleton ((cokernel α).presheaf.stalk (i.base (genericPoint Z))) := by
    refine ⟨fun a b ↦ ?_⟩
    have hz (a : (cokernel α).presheaf.stalk (i.base (genericPoint Z))) : a = 0 := by
      obtain ⟨a', rfl⟩ := qsurj (i.base (genericPoint Z)) a
      obtain ⟨a'', rfl⟩ := hsurj a'
      have hcomp := congrArg (fun f ↦ f a'')
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint Z))).map_comp α (cokernel.π α))
      rw [cokernel.condition, Functor.map_zero] at hcomp
      exact hcomp.symm
    exact (hz a).trans (hz b).symm
  have hsub : {y : X | ¬ Subsingleton ((cokernel α).presheaf.stalk y)} ⊆
      {y : X | ¬ Subsingleton (F.presheaf.stalk y)} := by
    intro y hy hFy
    have : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace y).obj F) := hFy
    exact hy ((qsurj y).subsingleton)
  have hstrict : {y : X | ¬ Subsingleton ((cokernel α).presheaf.stalk y)} ⊂
      {y : X | ¬ Subsingleton (F.presheaf.stalk y)} := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    have hxQ : i.base (genericPoint Z) ∈
        {y : X | ¬ Subsingleton ((cokernel α).presheaf.stalk y)} := by
      rw [heq]
      exact hx
    exact hxQ hQx
  have hS : (ShortComplex.mk α (cokernel.π α) (cokernel.condition α)).ShortExact :=
    { exact := ShortComplex.exact_cokernel α }
  refine ⟨A, cokernel α, α, cokernel.π α, cokernel.condition α, hS, hA, hQ, hfil, ?_⟩
  simpa only [hSupp] using hstrict

end AlgebraicGeometry.Scheme.Modules
