/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Auxiliary reductions for rational point local dimension base change. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem localDim_openEmbedding {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Topology.IsOpenEmbedding f) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x) := by
  apply le_antisymm
  · refine le_iInf₂ fun U hx ↦ ?_
    let V : TopologicalSpace.Opens X := ⟨f ⁻¹' U, U.isOpen.preimage hf.continuous⟩
    refine (iInf₂_le V hx).trans ?_
    refine Topology.IsInducing.topologicalKrullDim_le
      (f := fun p : V ↦ (⟨f p.1, p.2⟩ : U))
      (.of_comp (g := Subtype.val) (by fun_prop) ?_ ?_)
    · exact continuous_subtype_val
    · exact hf.toIsInducing.comp Topology.IsInducing.subtypeVal
  · refine le_iInf₂ fun U hx ↦ ?_
    let V : TopologicalSpace.Opens Y := ⟨f '' U, hf.isOpenMap _ U.isOpen⟩
    let g : U → Y := fun p ↦ f p.1
    have hg : Topology.IsEmbedding g := hf.toIsEmbedding.comp
      Topology.IsEmbedding.subtypeVal
    have hr : Set.range g = (V : Set Y) := by
      ext y
      simp [g, V, Set.mem_image]
    refine (iInf₂_le V ⟨x, hx, rfl⟩).trans_eq ?_
    rw [hg.topologicalKrullDim_eq_range, hr]
    rfl

/-- At a rational closed point of a locally finite type scheme over a field, the Krull
dimension of the scheme stalk equals its topological local dimension.

Source: Stacks Project, Lemma 10.114.6, Tag 00OU, applied on an affine open chart.
Proof: A section over the one-point scheme Spec k is a closed immersion, so its image
x is closed. Choose an affine open immersion a : Spec R -> X whose image contains x,
and write x = a(z). Since a is injective and continuous, z is closed and its prime
ideal is maximal. The composite a followed by f is locally of finite type; its ring
map k -> R therefore makes R a finite type k-algebra. Apply
topologicalKrullDimAt_eq_ringKrullDim_localizationAtMaximal at z. The open immersion
stalk isomorphism and Spec.stalkIso identify the stalk at x with R localized at z.
Ring equivalences preserve ring Krull dimension. The open immersion a also preserves
local topological dimension by cofinality of open neighbourhoods. Combining these
identifications proves the equality.
(blueprint: lem-ag-rational-point-stalk-topological-local-dimension)
-/
theorem ringKrullDim_stalk_rationalPoint_eq_topologicalKrullDimAt
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    ringKrullDim (X.presheaf.stalk (p (IsLocalRing.closedPoint k))) =
      topologicalKrullDimAt (p (IsLocalRing.closedPoint k)) := by
  let : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id f p hp
  have hc : IsClosed ({p (IsLocalRing.closedPoint k)} : Set X) := by
    simpa using p.isClosedEmbedding.isClosedMap _
      (isClosed_discrete _ : IsClosed ({IsLocalRing.closedPoint k} : Set (Spec (.of k))))
  obtain ⟨R, a, ha, ⟨z, hz⟩, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (show p (IsLocalRing.closedPoint k) ∈ (⊤ : X.Opens) from trivial)
  let : IsOpenImmersion a := ha
  have hcz : IsClosed ({z} : Set (Spec R)) := by
    have := hc.preimage a.continuous
    rw [← hz] at this
    have he : a ⁻¹' ({a z} : Set X) = {z} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, a.isOpenEmbedding.injective.eq_iff]
    exact he ▸ this
  let : z.asIdeal.IsMaximal := z.isClosed_singleton_iff_isMaximal.mp hcz
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ f)
  have hft : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
  have hft' : RingHom.FiniteType φ.hom := HasRingHomProperty.Spec_iff.mp hft
  let : Algebra k R := φ.hom.toAlgebra
  let : Algebra.FiniteType k R := hft'
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k R)
  have hd := topologicalKrullDimAt_eq_ringKrullDim_localizationAtMaximal
    (k := k) ⟨n, g, hg⟩ z.asIdeal
  rw [← hz]
  calc
    ringKrullDim (X.presheaf.stalk (a z)) =
        ringKrullDim ((Spec R).presheaf.stalk z) :=
      ringKrullDim_eq_of_ringEquiv (asIso (a.stalkMap z)).commRingCatIsoToRingEquiv
    _ = ringKrullDim (Localization.AtPrime z.asIdeal) :=
      ringKrullDim_eq_of_ringEquiv (Spec.stalkIso R z).commRingCatIsoToRingEquiv
    _ = topologicalKrullDimAt z := hd.symm
    _ = topologicalKrullDimAt (a z) := localDim_openEmbedding a.isOpenEmbedding z

end AlgebraicGeometry
