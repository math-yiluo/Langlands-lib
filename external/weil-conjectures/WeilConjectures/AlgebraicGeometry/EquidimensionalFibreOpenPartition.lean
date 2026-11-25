/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.RestrictedFibreLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CohenMacaulayFibreDimensionNeighbourhood
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents

/-! # Equidimensional fibre pieces

Source: Stacks Project, Tags 02NM and 02NJ.
(blueprint: lem-sbc-cohen-macaulay-equidimensional-fibre-pieces)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A fibre Cohen-Macaulay open decomposes into pieces with pure-dimensional fibres.

Source: Stacks Project, Tags 02NM and 02NJ.
Proof: Restrict the base to U and the source to W; hW makes the latter restriction
possible. Open immersions and composition preserve flatness and local finite
presentation. Fibres are locally of finite type over residue fields, hence locally
Noetherian. The open restriction pullback squares identify their stalks with those
of the original fibres, including the canonical residue-field isomorphisms.
Depth and ring Krull dimension are invariant under these ring isomorphisms, so hW
says the restricted fibres are Cohen-Macaulay. Apply Tag 02NM to W → U. Its clopen
pieces W_n partition W and, by the definition in Tag 02NJ, all irreducible components
of every nonempty fibre of W_n have dimension n. Map W_n into X to get V_n.
The fibre of W_n identifies, as a topological space, with the inverse image of V_n
under the original fibre inclusion. A homeomorphism identifies irreducible
components and preserves their Krull dimensions, giving the last assertion.
The pieces cover W and are disjoint because W_n form a coproduct. Empty fibres
have no irreducible components, and empty W uses empty pieces.
(blueprint: lem-sbc-cohen-macaulay-equidimensional-fibre-pieces) -/
theorem exists_equidimensional_fibre_open_partition_of_depth_eq_ringKrullDim
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)] (W : X.Opens)
    (hW : ∀ y ∈ W, f y ∈ U ∧
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))) :
    ∃ V : ℕ → X.Opens, (⨆ n, V n) = W ∧
      Pairwise (fun m n => Disjoint (V m) (V n)) ∧
      ∀ n t, ∀ C ∈ irreducibleComponents
        ↥((f.fiberι t) ⁻¹ᵁ V n), topologicalKrullDim C = (n : WithBot ℕ∞) := by
  let V : ℕ → X.Opens := fun n ↦
    ⟨interior {y : X | y ∈ W ∧
      topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞)}, isOpen_interior⟩
  have hVW : ∀ n, V n ≤ W := fun n y hy ↦ (interior_subset hy).1
  have hVdim : ∀ n y, y ∈ V n →
      topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞) :=
    fun n y hy ↦ (interior_subset hy).2
  refine ⟨V, le_antisymm (iSup_le hVW) ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, O, hyO, hOW, hOdim⟩ :=
      exists_constant_fibre_dimension_neighbourhood_of_depth_eq_ringKrullDim
        f U W y hy (hW y hy).1 (hW y hy).2
    have hOV : O ≤ V n := by
      apply O.isOpen.subset_interior_iff.mpr
      intro z hz
      exact ⟨hOW hz, hOdim z hz⟩
    exact (le_iSup V n) (hOV hyO)
  · intro m n hmn
    apply disjoint_iff.mpr
    apply bot_unique
    intro y hy
    have heq : (m : WithBot ℕ∞) = (n : WithBot ℕ∞) :=
      (hVdim m y hy.1).symm.trans (hVdim n y hy.2)
    exact (hmn (by exact_mod_cast heq)).elim
  · intro n t C hC
    by_cases ht : t ∈ U
    · have := isLocallyNoetherian_fibre_of_finite_presentation_restrict f U t ht
      apply topologicalKrullDim_component_eq_of_constant_local_dimension
        ((f.fiberι t) ⁻¹ᵁ V n) n ?_ C hC
      intro z hz
      change f.fiberι t z ∈ V n at hz
      have hzt : f (f.fiberι t z) = t := by
        simpa using (f.fiberHomeo t z).property
      generalize hy : f.fiberι t z = y at hzt hz ⊢
      subst t
      have hzy : f.asFiber y = z := by
        apply (f.fiberι _).isEmbedding.injective
        simpa using hy.symm
      rw [← hzy]
      exact hVdim n y hz
    · obtain ⟨z, _⟩ := hC.1.nonempty
      have hzV : f.fiberι t z.1 ∈ V n := z.property
      have hzt : f (f.fiberι t z.1) = t := by
        simpa using (f.fiberHomeo t z.1).property
      exact (ht (hzt ▸ (hW _ (hVW n hzV)).1)).elim

end AlgebraicGeometry
