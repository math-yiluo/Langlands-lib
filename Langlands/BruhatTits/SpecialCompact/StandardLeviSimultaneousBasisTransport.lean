import Langlands.BruhatTits.SpecialCompact.StandardLeviBasisInheritance
import Langlands.BruhatTits.SpecialCompact.InheritedNormalBasis
import Langlands.BruhatTits.SpecialCompact.StandardLeviWeakChamberTransport

/-! # The simultaneous standard basis on a representing Levi scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.HarishChandraSchwartz

namespace Langlands.BruhatTits.SpecialCompact

/-- A closed group embedding pulls a normal compact-open identity basis back
to the preimage of its common normalizing subgroup. -/
theorem CompactOpenNormalBasis.comap_of_isClosedEmbedding
    {H L : Type*} [Group H] [TopologicalSpace H] [Group L] [TopologicalSpace L]
    {K0 : Subgroup H} {B : Set (Subgroup H)} (hB : CompactOpenNormalBasis K0 B)
    (f : L →* H) (hf : IsClosedEmbedding f) :
    CompactOpenNormalBasis (K0.comap f) ((fun K => K.comap f) '' B) := by
  constructor
  · rintro _ ⟨K, hK, rfl⟩
    obtain ⟨hKK0, hnormal, hopen, hcompact⟩ := hB.1 K hK
    refine ⟨Subgroup.comap_mono hKK0, ?_, hopen.preimage hf.continuous,
      hf.isCompact_preimage hcompact⟩
    constructor
    intro n hn g
    have h := hnormal.conj_mem ⟨f n, hKK0 hn⟩ hn ⟨f g, g.property⟩
    change f (g : L) * f (n : L) * (f (g : L))⁻¹ ∈ K at h
    change f ((g : L) * n * (g : L)⁻¹) ∈ K
    simpa only [map_mul, map_inv] using h
  · have h := hf.isInducing.basis_nhds (x := (1 : L)) (by simpa only [map_one] using hB.2)
    refine h.to_hasBasis
      (fun K hK => ⟨K.comap f, ⟨K, hK, rfl⟩, subset_rfl⟩)
      ?_
    rintro _ ⟨K, hK, rfl⟩
    exact ⟨K, hK, subset_rfl⟩

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology rationalWeightsT2Field

local instance : IsAffineHom (Standard.leviScheme i ν J).X.hom := leviScheme_isAffineHom i ν J

/-- The family on the representing Levi scheme consists of the preimages of
all members of the same ambient subgroup family. -/
def leviSchemeBasisFamily (B : Set (Subgroup (rationalPoints G))) :
    Set (Subgroup (rationalPoints (Standard.leviScheme i ν J))) :=
  (fun K => leviSchemeCompact K i ν J) '' B

end Langlands.BruhatTits.SpecialCompact
