import Langlands.Global.AdelicNormOneCompactCover

/-! # Closed subgroup embeddings of norm-one rational quotients -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global

namespace LeftCosetSpace

/-- A compact quotient of a locally compact group has a compact set of representatives.
No normality assumption on the subgroup is needed. -/
theorem exists_isCompact_representatives
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] (Γ : Subgroup H) [CompactSpace (LeftCosetSpace Γ)] :
    ∃ K : Set H, IsCompact K ∧ ∀ x : H, ∃ γ : Γ, (γ : H) * x ∈ K := by
  classical
  choose K hKc hKn using fun x : H => exists_compact_mem_nhds x
  have hcover : (Set.univ : Set (LeftCosetSpace Γ)) ⊆
      ⋃ x : H, mk Γ '' interior (K x) := by
    intro c _
    obtain ⟨x, rfl⟩ := mk_surjective Γ c
    exact Set.mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hKn x), rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : H => mk Γ '' interior (K x))
    (fun _ => (isOpenQuotientMap_mk Γ).isOpenMap _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ t, K x, t.finite_toSet.isCompact_biUnion (fun x _ => hKc x), ?_⟩
  intro x
  obtain ⟨y, hyt, z, hz, hzx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (mk Γ x)))
  have hγ : z * x⁻¹ ∈ Γ := (mk_eq_mk_iff Γ x z).mp hzx.symm
  refine ⟨⟨z * x⁻¹, hγ⟩, Set.mem_iUnion₂.mpr ⟨y, hyt, ?_⟩⟩
  simpa only [Subtype.coe_mk, inv_mul_cancel_right] using interior_subset hz

end LeftCosetSpace

namespace AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G H : GroupScheme (Spec (CommRingCat.of F)))

/-- The map on actual norm-one rational quotients induced by a group-scheme morphism. -/
def normOneRationalQuotientMap (f : G ⟶ H) :
    NormOneRationalQuotient F G → NormOneRationalQuotient F H :=
  LeftCosetSpace.lift (rationalNormOneSubgroup F G)
    (fun x => LeftCosetSpace.mk (rationalNormOneSubgroup F H) (mapNormOne F G H f x))
    (by
      rintro ⟨_, q, rfl⟩ x
      rw [map_mul, mapNormOne_rationalNormOne]
      exact LeftCosetSpace.mk_subgroup_mul (rationalNormOneSubgroup F H)
        ⟨rationalNormOne F H (G.affinePointsTarget f (CommAlgCat.of F F) q), ⟨_, rfl⟩⟩ _)

@[simp] theorem normOneRationalQuotientMap_mk (f : G ⟶ H) (g : normOneSubgroup F G) :
    normOneRationalQuotientMap F G H f
        (LeftCosetSpace.mk (rationalNormOneSubgroup F G) g) =
      LeftCosetSpace.mk (rationalNormOneSubgroup F H) (mapNormOne F G H f g) := rfl

/-- The induced quotient map is continuous for the existing quotient topologies. -/
theorem continuous_normOneRationalQuotientMap (f : G ⟶ H) :
    Continuous (normOneRationalQuotientMap F G H f) := by
  apply (LeftCosetSpace.continuous_iff (rationalNormOneSubgroup F G)).mpr
  exact (LeftCosetSpace.continuous_mk (rationalNormOneSubgroup F H)).comp
    (mapNormOne F G H f).continuous

variable {F G H}

/-- For actual finite-type affine groups, quotient compactness is equivalent to compact
principal representatives in the norm-one group. -/
theorem hasCompactNormOneRationalCover_iff_compactSpace
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    HasCompactNormOneRationalCover G ↔ CompactSpace (NormOneRationalQuotient F G) := by
  refine ⟨fun h => h.compactSpace, fun h => ?_⟩
  let : CompactSpace (NormOneRationalQuotient F G) := h
  obtain ⟨K, hK, hcover⟩ :=
    LeftCosetSpace.exists_isCompact_representatives (rationalNormOneSubgroup F G)
  refine ⟨K, hK, fun x => ?_⟩
  obtain ⟨⟨_, q, rfl⟩, hq⟩ := hcover x
  exact ⟨q, hq⟩

/-- Relative compactness of the image under a closed embedding of actual quotients
constructs compact principal representatives in the source. -/
theorem hasCompactNormOneRationalCover_of_isClosedEmbedding
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    {Y : Type v} [TopologicalSpace Y] (f : NormOneRationalQuotient F G → Y)
    (hf : IsClosedEmbedding f) (hcompact : IsCompact (closure (Set.range f))) :
    HasCompactNormOneRationalCover G := by
  apply hasCompactNormOneRationalCover_iff_compactSpace.mpr
  refine isCompact_univ_iff.mp ?_
  have h := hf.isCompact_preimage hcompact
  have heq : f ⁻¹' closure (Set.range f) = Set.univ :=
    Set.eq_univ_of_forall fun x => subset_closure (Set.mem_range_self x)
  rwa [heq] at h

/-- Springer's Lemma 1.3: a closed algebraic subgroup induces a closed topological
embedding of the actual norm-one rational quotients. -/
def NormOneRationalQuotientClosedImmersionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G H : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (f : G ⟶ H), IsClosedImmersion f.hom.hom.left →
      IsClosedEmbedding (normOneRationalQuotientMap F G H f)

end AdelicGroupPoints
end Langlands.Global
