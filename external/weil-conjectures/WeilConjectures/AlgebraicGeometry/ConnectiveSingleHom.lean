/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Degree-zero chain maps into connective complexes

Source: Stacks Project, Derived Categories, Section 13.11 (Tag 05RR), truncation
calculus of fractions. (blueprint: lem-sc-connective-single-hom)
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Localization does not change maps from a degree-zero object into a complex
which is zero in negative degrees. No projectivity or acyclicity of global sections
is assumed.
Source: Stacks Project, Derived Categories, Section 13.11 (Tag 05RR).
(blueprint: lem-sc-connective-single-hom)

Proof: Truncate a right fraction to degrees both at least and at most zero on its
source. The denominator is then a quasi-isomorphism between complexes concentrated
in degree zero, hence an isomorphism. This proves surjectivity. For injectivity apply
zeroth homology. In the source both adjacent differentials vanish, so its zeroth
homology is its zeroth term. In the target the incoming differential vanishes, so
zeroth homology embeds into the zeroth term. Naturality recovers the degree-zero
component, which determines a chain map from a single complex. -/
theorem connective_single_hom_bijective
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (M : C) (K : CochainComplex C ℤ)
    (hneg : ∀ i : ℤ, i < 0 → IsZero (K.X i)) :
    Function.Bijective (fun f : (CochainComplex.singleFunctor C 0).obj M ⟶ K ↦ Q.map f) := by
  have : K.IsStrictlyGE 0 := (CochainComplex.isStrictlyGE_iff K 0).2 hneg
  constructor
  · intro f g hfg
    have hh : HomologicalComplex.homologyMap f 0 =
        HomologicalComplex.homologyMap g 0 := by
      have h := congrArg ((homologyFunctor C 0).map) hfg
      have hf := (homologyFunctorFactors C 0).hom.naturality f
      have hg := (homologyFunctorFactors C 0).hom.naturality g
      dsimp at hf hg
      rw [h] at hf
      exact (cancel_epi ((homologyFunctorFactors C 0).hom.app _)).1 (hf.symm.trans hg)
    apply HomologicalComplex.from_single_hom_ext
    have hp : IsIso (K.pOpcycles 0) :=
      K.isIso_pOpcycles (-1) 0 (by simp) ((hneg (-1) (by omega)).eq_of_src _ _)
    apply (cancel_mono (K.pOpcycles 0)).1
    rw [← HomologicalComplex.p_opcyclesMap, ← HomologicalComplex.p_opcyclesMap]
    have hi := HomologicalComplex.homologyι_naturality f 0
    have hj := HomologicalComplex.homologyι_naturality g 0
    rw [hh] at hi
    rw [hj] at hi
    have : IsIso (((CochainComplex.singleFunctor C 0).obj M).homologyι 0) := by
      exact HomologicalComplex.isIso_homologyι _ 0 1 (by simp) (by simp)
    exact congrArg (fun z ↦
      ((CochainComplex.singleFunctor C 0).obj M).pOpcycles 0 ≫ z)
        ((cancel_epi (((CochainComplex.singleFunctor C 0).obj M).homologyι 0)).1 hi.symm)
  · intro f
    obtain ⟨X, _, _, s, _, g, rfl⟩ := right_fac_of_isStrictlyLE_of_isStrictlyGE 0 0 f
    obtain ⟨A, ⟨e⟩⟩ := X.exists_iso_single 0
    obtain ⟨φ, hφ⟩ := (CochainComplex.singleFunctor C 0).map_surjective (e.inv ≫ s)
    have : IsIso ((singleFunctor C 0).map φ) := by
      change IsIso (Q.map ((CochainComplex.singleFunctor C 0).map φ))
      rw [hφ, Functor.map_comp]
      infer_instance
    have : IsIso φ :=
      (NatIso.isIso_map_iff (singleFunctorCompHomologyFunctorIso C 0) φ).1
        (by dsimp; infer_instance)
    have : IsIso (e.inv ≫ s) := by rw [← hφ]; infer_instance
    have : IsIso s := IsIso.of_isIso_comp_left e.inv s
    exact ⟨inv s ≫ g, by simp⟩

end DerivedCategory
