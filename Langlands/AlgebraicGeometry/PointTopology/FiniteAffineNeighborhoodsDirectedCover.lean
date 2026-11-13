import Langlands.AlgebraicGeometry.PointTopology.FiniteAffineNeighborhoodsDisjointCover
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteAffineOpen
import Mathlib.Data.Set.Finite.Lattice

/-! # Finite affine neighbourhoods in increasing unions of ample pieces -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The finite-affine-neighbourhood property passes from a directed open cover
to the whole scheme. -/
def DirectedOpenCoverFiniteAffineNeighborhoodsStatement : Prop :=
  ∀ (X : Scheme.{u}) (ι : Type v) (U : ι → X.Opens),
    iSup U = ⊤ →
    Directed (· ≤ ·) U →
    (∀ i, HasFiniteAffineNeighborhoods (U i).toScheme) →
    HasFiniteAffineNeighborhoods X

/-- A finite set in a directed open union lies in one member, where it has an
affine neighbourhood. The index type may be empty. -/
theorem hasFiniteAffineNeighborhoods_of_directed_openCover
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)
    (hcover : iSup U = ⊤) (hdirected : Directed (· ≤ ·) U)
    (hAF : ∀ i, HasFiniteAffineNeighborhoods (U i).toScheme) :
    HasFiniteAffineNeighborhoods X := by
  classical
  intro E hE
  by_cases hι : Nonempty ι
  · have := hι
    have hd : Directed (· ⊆ ·) (fun i ↦ (U i : Set X)) := by
      intro i j
      obtain ⟨k, hik, hjk⟩ := hdirected i j
      exact ⟨k, hik, hjk⟩
    have hEU : (hE.toFinset : Set X) ⊆ ⋃ i, (U i : Set X) := by
      intro x _
      have hx : x ∈ iSup U := by rw [hcover]; trivial
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hd.exists_mem_subset_of_finset_subset_biUnion hEU
    have hEi : E ⊆ U i := by simpa only [hE.coe_toFinset] using hi
    obtain ⟨V, hEV⟩ := hAF i ((U i).ι ⁻¹' E)
      (hE.preimage (U i).ι.isOpenEmbedding.injective.injOn)
    refine ⟨⟨(U i).ι ''ᵁ V.val, V.property.image_of_isOpenImmersion (U i).ι⟩, ?_⟩
    intro x hx
    exact ⟨⟨x, hEi hx⟩, hEV hx, rfl⟩
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    have hbot : (⊤ : X.Opens) = ⊥ := by simpa using hcover.symm
    refine ⟨⟨⊥, isAffineOpen_bot X⟩, ?_⟩
    intro x _
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rwa [hbot] at hx

/-- The directed-cover assembly proposition holds in arbitrary universes. -/
theorem directedOpenCoverFiniteAffineNeighborhoods :
    DirectedOpenCoverFiniteAffineNeighborhoodsStatement.{u, v} := by
  intro X ι U hcover hdirected hAF
  exact hasFiniteAffineNeighborhoods_of_directed_openCover U hcover hdirected hAF

/-- A scheme carrying an ample line bundle has finite affine neighbourhoods,
by the published ample finite-set theorem. -/
theorem hasFiniteAffineNeighborhoods_of_ample
    {X : Scheme.{u}} (L : Picard.LineBundle X) (hL : L.IsAmple) :
    HasFiniteAffineNeighborhoods X := by
  intro E hE
  obtain ⟨V, hV, hEV, _⟩ := Picard.exists_isAffineOpen_of_finite_of_ample
    X L hL E ⊤ hE (Set.subset_univ _)
  exact ⟨⟨V, hV⟩, hEV⟩

/-- An increasing union of open subschemes carrying ample line bundles has
finite affine neighbourhoods. No global quasi-compactness is required. -/
theorem hasFiniteAffineNeighborhoods_of_directed_ample_openCover
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)
    (hcover : iSup U = ⊤) (hdirected : Directed (· ≤ ·) U)
    (hample : ∀ i, ∃ L : Picard.LineBundle (U i).toScheme, L.IsAmple) :
    HasFiniteAffineNeighborhoods X := by
  apply hasFiniteAffineNeighborhoods_of_directed_openCover U hcover hdirected
  intro i
  obtain ⟨L, hL⟩ := hample i
  exact hasFiniteAffineNeighborhoods_of_ample L hL

/-- Disjoint open pieces that are each an increasing union of open subschemes
carrying ample line bundles have finite affine neighbourhoods. -/
theorem hasFiniteAffineNeighborhoods_of_disjoint_directed_ample_openCover
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)
    (hcover : iSup U = ⊤)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    {κ : ι → Type w} (V : ∀ i, κ i → (U i).toScheme.Opens)
    (hVcover : ∀ i, iSup (V i) = ⊤)
    (hVdirected : ∀ i, Directed (· ≤ ·) (V i))
    (hVample : ∀ i j, ∃ L : Picard.LineBundle ((V i j).toScheme), L.IsAmple) :
    HasFiniteAffineNeighborhoods X := by
  apply hasFiniteAffineNeighborhoods_of_disjoint_openCover U hcover hdisjoint
  intro i
  exact hasFiniteAffineNeighborhoods_of_directed_ample_openCover
    (V i) (hVcover i) (hVdirected i) (hVample i)

end Langlands.AlgebraicGeometry.PointTopology
