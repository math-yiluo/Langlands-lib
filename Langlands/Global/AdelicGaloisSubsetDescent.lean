import Langlands.Global.AdelicGaloisBoundedRootCompact

/-! # Compact representatives descend along Galois scalar extension, for subsets -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global

namespace LeftCosetSpace

/-- A compact subset of the left coset space of a locally compact group has a compact set of
representatives. No normality assumption on the subgroup is needed. -/
theorem exists_isCompact_representatives_of_isCompact
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] (Γ : Subgroup H) {Z : Set (LeftCosetSpace Γ)} (hZ : IsCompact Z) :
    ∃ K : Set H, IsCompact K ∧ ∀ x : H, mk Γ x ∈ Z → ∃ c : Γ, (c : H) * x ∈ K := by
  classical
  choose K hKc hKn using fun x : H => exists_compact_mem_nhds x
  have hcover : Z ⊆ ⋃ x : H, mk Γ '' interior (K x) := by
    intro c _
    obtain ⟨x, rfl⟩ := mk_surjective Γ c
    exact Set.mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hKn x), rfl⟩
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover
    (fun x : H => mk Γ '' interior (K x))
    (fun _ => (isOpenQuotientMap_mk Γ).isOpenMap _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ t, K x, t.finite_toSet.isCompact_biUnion (fun x _ => hKc x), ?_⟩
  intro x hx
  obtain ⟨y, hyt, z, hz, hzx⟩ := Set.mem_iUnion₂.mp (ht hx)
  have hγ : z * x⁻¹ ∈ Γ := (mk_eq_mk_iff Γ x z).mp hzx.symm
  refine ⟨⟨z * x⁻¹, hγ⟩, Set.mem_iUnion₂.mpr ⟨y, hyt, ?_⟩⟩
  simpa only [Subtype.coe_mk, inv_mul_cancel_right] using interior_subset hz

end LeftCosetSpace

namespace AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsGalois F L]

/-- **Subset descent, left form.** For a compact set `K` of upper-field norm-one points there
is a compact set `Ω` of source norm-one points such that every source point whose scalar
extension has a principal left translate in `K` has a principal left translate in `Ω`. -/
theorem exists_isCompact_rational_mul_mem_of_scalarExtension
    (K : Set (normOneSubgroup L (AffineWeil.unitBaseChange F L G))) (hK : IsCompact K) :
    ∃ Ω : Set (normOneSubgroup F G), IsCompact Ω ∧
      ∀ g : normOneSubgroup F G,
        (∃ q : RationalGroupPoints L (AffineWeil.unitBaseChange F L G),
          rationalNormOne L _ q * scalarExtensionNormOneMap F L G g ∈ K) →
        ∃ q : RationalGroupPoints F G, rationalNormOne F G q * g ∈ Ω := by
  let πL := LeftCosetSpace.mk
    (rationalNormOneSubgroup L (AffineWeil.unitBaseChange F L G))
  let Z := scalarExtensionQuotientMap F L G ⁻¹' (πL '' K)
  have hZ : IsCompact Z :=
    (isClosedEmbedding_scalarExtensionQuotientMap F L G).isCompact_preimage
      (hK.image (LeftCosetSpace.continuous_mk _))
  obtain ⟨Ω, hΩ, hrep⟩ :=
    LeftCosetSpace.exists_isCompact_representatives_of_isCompact
      (rationalNormOneSubgroup F G) hZ
  refine ⟨Ω, hΩ, fun g ⟨q, hq⟩ => ?_⟩
  have hgZ : LeftCosetSpace.mk (rationalNormOneSubgroup F G) g ∈ Z := by
    change scalarExtensionQuotientMap F L G _ ∈ πL '' K
    rw [scalarExtensionQuotientMap_mk_normOne]
    refine ⟨_, hq, ?_⟩
    exact LeftCosetSpace.mk_subgroup_mul
      (rationalNormOneSubgroup L (AffineWeil.unitBaseChange F L G))
      ⟨rationalNormOne L _ q, ⟨q, rfl⟩⟩ _
  obtain ⟨⟨_, r, rfl⟩, hr⟩ := hrep g hgZ
  exact ⟨r, hr⟩

/-- **Subset descent, right form.** The same statement with principal factors on the right,
the convention of `HasUniformNormOneRationalOrbitHeightBound`. -/
theorem exists_isCompact_mul_rational_mem_of_scalarExtension
    (K : Set (normOneSubgroup L (AffineWeil.unitBaseChange F L G))) (hK : IsCompact K) :
    ∃ Ω : Set (normOneSubgroup F G), IsCompact Ω ∧
      ∀ g : normOneSubgroup F G,
        (∃ q : RationalGroupPoints L (AffineWeil.unitBaseChange F L G),
          scalarExtensionNormOneMap F L G g * rationalNormOne L _ q ∈ K) →
        ∃ q : RationalGroupPoints F G, g * rationalNormOne F G q ∈ Ω := by
  obtain ⟨Ω, hΩ, hdesc⟩ :=
    exists_isCompact_rational_mul_mem_of_scalarExtension F L G K⁻¹ hK.inv
  refine ⟨Ω⁻¹, hΩ.inv, fun g ⟨q, hq⟩ => ?_⟩
  obtain ⟨r, hr⟩ := hdesc g⁻¹ ⟨q⁻¹, by
    simpa only [Set.mem_inv, mul_inv_rev, map_inv, inv_inv] using hq⟩
  refine ⟨r⁻¹, ?_⟩
  simpa only [Set.mem_inv, mul_inv_rev, map_inv, inv_inv] using hr

end AdelicGaloisUnit

end Langlands.Global
