/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

private theorem mem_product {S : Scheme.{u}} {J : Type (max u w)} {U : S.Opens}
    {V : J → S.Opens} {hom : ∀ j, V j ⟶ U} (C : SiteCechComplex V hom)
    (p : ℕ) (t : Fin (p + 1) → J) (x : S) (hx : ∀ k, x ∈ V (t k)) :
    x ∈ C.W p t := by
  let B : S.Opens := ⟨⋂ k, (V (t k) : Set S), isOpen_iInter_of_finite fun k ↦ (V (t k)).isOpen⟩
  have hb (k) : B ≤ V (t k) := by
    intro y hy
    exact Set.mem_iInter.mp hy k
  obtain ⟨b, _, _⟩ := C.universal p t B (fun k ↦ homOfLE (hb k))
    (fun _ ↦ Subsingleton.elim _ _)
  exact b.le (Set.mem_iInter.mpr hx)

private def inverseImageCech {X S : Scheme.{u}} (h : X ⟶ S)
    {J : Type (max u w)} {U : S.Opens} {V : J → S.Opens}
    {hom : ∀ j, V j ⟶ U} (C : SiteCechComplex V hom) :
    SiteCechComplex (fun j ↦ h ⁻¹ᵁ V j)
      (fun j ↦ homOfLE ((TopologicalSpace.Opens.map h.base).map (hom j)).le) where
  W p t := h ⁻¹ᵁ C.W p t
  pr p t k := (TopologicalSpace.Opens.map h.base).map (C.pr p t k)
  comm _ _ _ := Subsingleton.elim _ _
  universal p t Z a _ := by
    have hz : Z ≤ h ⁻¹ᵁ C.W p t := by
      intro x hx
      exact mem_product C p t (h.base x) (fun k ↦ (a k).le hx)
    exact ⟨homOfLE hz, fun _ ↦ Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩
  W_zero t := congrArg (fun W ↦ h ⁻¹ᵁ W) (C.W_zero t)
  pr_zero _ := Subsingleton.elim _ _
  indexMap t α := (TopologicalSpace.Opens.map h.base).map (C.indexMap t α)
  indexMap_pr _ _ _ := Subsingleton.elim _ _

/-- Positive Čech cohomology of a direct image of an injective module vanishes.

Source: Stacks Project, Cohomology of Sheaves, Tag 01EX (1), using Tag 01EP.
(blueprint: lem-weil-pbc-module-pushforward-injective-cech-vanishing).

Proof: Fix an open U, a covering (V_i), and a choice C of its iterated fibre products.
Pull back the opens along h. Inverse image preserves their union, so they cover h⁻¹U.
In the poset of opens, the universal property identifies C.W p t with the intersection
of the V_(t k); inverse image preserves these finite intersections. Choose the Čech
products on X to be these inverse images, with their induced projection and index maps.
The underlying additive groups of h_*I on C.W p t are exactly those of I on h⁻¹(C.W p t).
The change of scalar rings in module direct image does not change these additive groups.
Their restriction maps also agree. Taking products and alternating sums therefore
identifies the two additive Čech complexes degree by degree, including differentials.
Apply module_injective_open_cover_cech_acyclic to I and the pulled-back covering.
Transport its positive-degree IsZero statements across the resulting cohomology
isomorphisms. Uniqueness of products makes this work for every choice C. -/
theorem module_pushforward_injective_cech_vanishing {X S : Scheme.{u}} (h : X ⟶ S)
    (I : X.Modules) [Injective I] :
    ∀ (U : S.Opens) (J : Type (max u w)) (V : J → S.Opens)
      (hom : ∀ j, V j ⟶ U), (⨆ j, V j) = U →
      ∀ (C : SiteCechComplex V hom) (p : ℕ), 0 < p →
        IsZero ((C.cohomologyFunctor p).obj
          ((toPresheaf S).obj ((pushforward h).obj I))) := by
  intro U J V hom hcover C p hp
  have hcover' : (⨆ j, h ⁻¹ᵁ V j) = h ⁻¹ᵁ U := by
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_iSup]
    change (⋃ j, h.base ⁻¹' (V j : Set S)) = h.base ⁻¹' (U : Set S)
    rw [← Set.preimage_iUnion]
    simpa only [TopologicalSpace.Opens.coe_iSup] using
      congrArg (fun W : S.Opens ↦ h.base ⁻¹' (W : Set S)) hcover
  have hz := module_injective_open_cover_cech_acyclic I (h ⁻¹ᵁ U) J
    (fun j ↦ h ⁻¹ᵁ V j)
    (fun j ↦ ((TopologicalSpace.Opens.map h.base).map (hom j)).le) hcover'
    (inverseImageCech h C) p hp
  -- Both complexes have definitionally the same groups and alternating restriction maps.
  exact hz

end AlgebraicGeometry.Scheme.Modules
