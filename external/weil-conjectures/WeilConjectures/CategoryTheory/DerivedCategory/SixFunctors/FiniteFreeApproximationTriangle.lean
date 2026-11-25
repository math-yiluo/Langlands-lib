/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Finite free approximations of a finite module -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- A finitely presented module over a Noetherian ring has bounded finite free
approximations with arbitrarily low error cone. Source: Stacks Project, Tag 0944,
finite free resolution and brutal truncation in the projection formula proof.
(blueprint: lem-sf-finite-free-approximation-triangle).

Proof: the module in degree zero is pseudo-coherent by the Noetherian cohomology
criterion. Its m-pseudo-coherent approximation is bounded finite free and induces
isomorphisms in all degrees above m. Complete its map to a distinguished triangle.
For i above m, exactness and the two adjacent isomorphisms force degree i cohomology
of its cone to vanish. Choosing m equal to the prescribed cone bound suffices.
Identify each finite free term with a finite power of the ring using a finite basis. -/
theorem exists_finiteFree_approximation_triangle
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M] (c : ℤ) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
      (T : Triangle (DerivedCategory (ModuleCat.{u} R))),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, ∃ n : ℕ, Nonempty (P.X i ≅ ModuleCat.of R (Fin n → R))) ∧
      T ∈ distTriang _ ∧ T.obj₁ = Q.obj P ∧
      T.obj₂ = (singleFunctor _ 0).obj M ∧ T.obj₃.IsLE c := by
  classical
  have hMfin : Module.Finite R M := inferInstance
  let D := (singleFunctor (ModuleCat.{u} R) 0).obj M
  have hpc : IsPseudoCoherent D := by
    apply (isPseudoCoherent_iff_boundedAbove_finite_homology R D).2
    refine ⟨⟨0, fun i hi ↦ D.isZero_of_isLE 0 i hi⟩, ?_⟩
    intro i
    by_cases hi : i = 0
    · subst i
      exact Module.Finite.equiv (M := M)
        (((singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app M).symm.toLinearEquiv)
    · have hz : IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj D) := by
        by_cases h : 0 < i
        · exact D.isZero_of_isLE 0 i h
        · exact D.isZero_of_isGE 0 i (by omega)
      have : Subsingleton ((homologyFunctor (ModuleCat.{u} R) i).obj D) :=
        ModuleCat.subsingleton_of_isZero hz
      infer_instance
  let E := Q.objPreimage D
  let e := Q.objObjPreimageIso D
  have hpcE : IsPseudoCoherent (Q.obj E) := by
    obtain ⟨P, b, hb, hfree, ⟨p⟩⟩ := hpc
    exact ⟨P, b, hb, hfree, ⟨p ≪≫ e.symm⟩⟩
  obtain ⟨P, a, b, ha, hb, hfree, f, hf, hepi⟩ :=
    (isPseudoCoherent_iff_forall_isMPseudoCoherent R E).1 hpcE c
  let g : Q.obj P ⟶ D := f ≫ e.hom
  have hg (i : ℤ) (hi : c < i) : IsIso ((homologyFunctor (ModuleCat.{u} R) i).map g) := by
    have := hf i hi
    dsimp [g]
    rw [Functor.map_comp]
    infer_instance
  obtain ⟨Z, v, w, hT⟩ := distinguished_cocone_triangle g
  let T := Triangle.mk g v w
  refine ⟨P, a, b, T, ha, hb, ?_, hT, rfl, rfl, ?_⟩
  · intro i
    have := (hfree i).1
    have := (hfree i).2
    by_cases hR : Nontrivial R
    · have := hR
      exact ⟨Module.finrank R (P.X i),
        ⟨(Module.finBasis R (P.X i)).equivFun.toModuleIso⟩⟩
    · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
      have : Subsingleton (P.X i) := Module.subsingleton R (P.X i)
      exact ⟨0, ⟨(LinearEquiv.ofSubsingleton (R := R) (P.X i) (Fin 0 → R)).toModuleIso⟩⟩
  · apply (isLE_iff _ c).2
    intro i hi
    have hgi := hg i hi
    have hgi' := hg (i + 1) (by omega)
    have hgiT : IsIso ((homologyFunctor (ModuleCat.{u} R) i).map T.mor₁) := hgi
    have hgiT' : IsIso ((homologyFunctor (ModuleCat.{u} R) (i + 1)).map T.mor₁) := hgi'
    apply (HomologySequence.exact₃ T hT i (i + 1)).isZero_X₂
    · exact (HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 inferInstance
    · exact (HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1)).1 inferInstance

end DerivedCategory
