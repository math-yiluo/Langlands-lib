import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionRepresentability
import Mathlib.AlgebraicGeometry.Limits

/-! # Finite affine neighbourhoods from disjoint open pieces -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The finite-affine-neighbourhood property can be assembled along an arbitrary
pairwise disjoint open cover. -/
def DisjointOpenCoverFiniteAffineNeighborhoodsStatement : Prop :=
  ∀ (X : Scheme.{u}) (ι : Type v) (U : ι → X.Opens),
    iSup U = ⊤ →
    Pairwise (fun i j ↦ Disjoint (U i) (U j)) →
    (∀ i, HasFiniteAffineNeighborhoods (U i).toScheme) →
    HasFiniteAffineNeighborhoods X

/-- Every finite set meets finitely many disjoint pieces, so its affine
neighbourhoods in those pieces have an affine union. -/
theorem hasFiniteAffineNeighborhoods_of_disjoint_openCover
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)
    (hcover : iSup U = ⊤)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (hAF : ∀ i, HasFiniteAffineNeighborhoods (U i).toScheme) :
    HasFiniteAffineNeighborhoods X := by
  classical
  intro E hE
  have hmem (x : X) : ∃ i, x ∈ U i := by
    apply Opens.mem_iSup.mp
    rw [hcover]
    trivial
  choose idx hidx using hmem
  have hpre (i : ι) : ((U i).ι ⁻¹' E).Finite :=
    hE.preimage (U i).ι.isOpenEmbedding.injective.injOn
  choose V hV using fun i ↦ hAF i _ (hpre i)
  let W (i : ι) : X.Opens := (U i).ι ''ᵁ (V i).val
  have hWaff (i : ι) : IsAffineOpen (W i) :=
    (V i).property.image_of_isOpenImmersion (U i).ι
  have hWU (i : ι) : W i ≤ U i := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hWdisjoint : Pairwise (fun i j ↦ Disjoint (W i) (W j)) :=
    fun i j hij ↦ (hdisjoint hij).mono (hWU i) (hWU j)
  let I : Set ι := idx '' E
  have hI : I.Finite := hE.image idx
  refine ⟨⟨⨆ i ∈ I, W i,
    IsAffineOpen.biSup_of_disjoint hI (fun i _ ↦ hWaff i)
      (fun i _ j _ hij ↦ hWdisjoint hij)⟩, ?_⟩
  intro x hx
  apply Opens.mem_iSup.mpr
  refine ⟨idx x, Opens.mem_iSup.mpr ⟨⟨x, hx, rfl⟩, ?_⟩⟩
  exact ⟨⟨x, hidx x⟩, hV (idx x) hx, rfl⟩

/-- The disjoint-cover assembly proposition holds in arbitrary universes. -/
theorem disjointOpenCoverFiniteAffineNeighborhoods :
    DisjointOpenCoverFiniteAffineNeighborhoodsStatement.{u, v} := by
  intro X ι U hcover hdisjoint hAF
  exact hasFiniteAffineNeighborhoods_of_disjoint_openCover U hcover hdisjoint hAF

end Langlands.AlgebraicGeometry.PointTopology
