import Langlands.Geometry.Analytic.AtlasTopology.Homeomorph
import Langlands.Geometry.Analytic.AtlasTopology.QuasinetProperties

/-! # Disjoint sums of actual atlas nets -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AtlasTopology

open Set Filter Topology
open scoped Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Restricted quasinet transport along an embedding uses the actual subspace
homeomorphism. The larger ambient family can contain additional members. -/
theorem IsQuasinet.restrictedFamily_image {τ : Set (Set X)} {S : Set X}
    (hτ : IsQuasinet (restrictedFamily τ S)) {f : X → Y} (hf : IsEmbedding f) :
    IsQuasinet (restrictedFamily ((fun U => f '' U) '' τ) (f '' S)) := by
  apply (hτ.imageFamily (hf.homeomorphImage S)).mono
  rintro _ ⟨_, ⟨U, hU, hUS, rfl⟩, rfl⟩
  refine ⟨f '' U, ⟨U, hU, rfl⟩, Set.image_mono hUS, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hUS hx⟩, hx, Subtype.ext hxy⟩

variable {I : Type w} {Z : I → Type u} [∀ i, TopologicalSpace (Z i)]

/-- Exactly the images of the component families in the actual topological
sigma space. No disjointness among charts within a component is assumed. -/
def sigmaFamily (τ : ∀ i, Set (Set (Z i))) : Set (Set (Sigma Z)) :=
  {W | ∃ i, ∃ U ∈ τ i, W = Sigma.mk i '' U}

theorem IsQuasinet.sigmaFamily {τ : ∀ i, Set (Set (Z i))}
    (hτ : ∀ i, IsQuasinet (τ i)) : IsQuasinet (sigmaFamily τ) := by
  rintro ⟨i, x⟩
  obtain ⟨σ, hfin, hsub, hmem, hnhds⟩ := hτ i x
  refine ⟨(fun U => Sigma.mk i '' U) '' σ, hfin.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact ⟨i, U, hsub hU, rfl⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact ⟨x, hmem U hU, rfl⟩
  · apply Filter.mem_of_superset (isOpenMap_sigmaMk.image_mem_nhds hnhds)
    rintro _ ⟨y, ⟨U, hU, hy⟩, rfl⟩
    exact ⟨Sigma.mk i '' U, ⟨U, hU, rfl⟩, ⟨y, hy, rfl⟩⟩

theorem IsNet.sigmaFamily {τ : ∀ i, Set (Set (Z i))}
    (hτ : ∀ i, IsNet (τ i)) : IsNet (sigmaFamily τ) := by
  refine ⟨IsQuasinet.sigmaFamily (fun i => (hτ i).1), ?_⟩
  rintro _ ⟨i, U, hU, rfl⟩ _ ⟨j, V, hV, rfl⟩
  by_cases hij : i = j
  · subst j
    rw [← Set.image_inter sigma_mk_injective]
    apply ((hτ i).2 U hU V hV).restrictedFamily_image IsEmbedding.sigmaMk |>.mono
    rintro W ⟨T, ⟨R, hR, rfl⟩, hT, rfl⟩
    exact ⟨Sigma.mk i '' R, ⟨i, R, hR, rfl⟩, hT, rfl⟩
  · intro z
    obtain ⟨x, _, hx⟩ := z.property.1
    obtain ⟨y, _, hy⟩ := z.property.2
    exact (hij (congrArg Sigma.fst (hx.trans hy.symm))).elim

theorem IsCompactFamily.sigmaFamily {τ : ∀ i, Set (Set (Z i))}
    (hτ : ∀ i, IsCompactFamily (τ i)) : IsCompactFamily (sigmaFamily τ) := by
  rintro _ ⟨i, U, hU, rfl⟩
  let : T2Space U := (hτ i U hU).2
  exact ⟨(hτ i U hU).1.image continuous_sigmaMk,
    (IsEmbedding.sigmaMk.homeomorphImage U).t2Space⟩

end Langlands.Analytic.AtlasTopology
