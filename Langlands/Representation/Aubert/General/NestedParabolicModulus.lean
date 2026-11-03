import Langlands.Representation.Aubert.General.SubgroupOfModulus
import Langlands.Representation.Aubert.General.SemidirectHaarModulus
import Langlands.Representation.Aubert.General.Conjugation

noncomputable section

universe u
open Topology MeasureTheory
open scoped Pointwise

namespace Langlands.Aubert.General.NestedParabolic

section Algebra

variable {G : Type u} [Group G] {Q L U N : Subgroup G}
    (hQ : IsSemidirectDecomposition Q L U) (hNQ : N ≤ Q)
    (hprod : (N : Set G) = (L ⊓ N : Subgroup G) * (U : Set G))

include hQ hNQ hprod

omit hQ hNQ in
/-- The coarse radical lies in the fine radical, by the supplied actual product. -/
theorem unipotent_le : U ≤ N := by
  intro u hu
  change u ∈ (N : Set G)
  rw [hprod]
  exact Set.mem_mul.mpr ⟨1, ⟨L.one_mem, N.one_mem⟩, u, hu, one_mul u⟩

/-- The outer projection preserves the fine radical. -/
theorem projection_mem (n : N) : (hQ.projection (Subgroup.inclusion hNQ n) : G) ∈ N := by
  have hn : (n : G) ∈ (L ⊓ N : Subgroup G) * (U : Set G) := hprod ▸ n.property
  obtain ⟨w, hw, u, hu, heq⟩ := Set.mem_mul.mp hn
  have hp : hQ.projection (Subgroup.inclusion hNQ n) = ⟨w, hw.1⟩ := by
    apply (hQ.projection_eq_iff _ _).mpr
    change w⁻¹ * (n : G) ∈ U
    rw [← heq]
    simpa using hu
  rw [hp]
  exact hw.2

/-- The actual fine radical splits as its intersection with the outer Levi,
followed by the coarse radical. -/
theorem radicalDecomposition : IsSemidirectDecomposition N (L ⊓ N) U := by
  refine ⟨inf_le_right, unipotent_le hprod, hNQ.trans hQ.le_normalizer, ?_⟩
  rw [Subgroup.isComplement'_def, Subgroup.isComplement_iff_existsUnique_inv_mul_mem]
  intro n
  let w : (L ⊓ N : Subgroup G) := ⟨hQ.projection (Subgroup.inclusion hNQ n),
    (hQ.projection (Subgroup.inclusion hNQ n)).property, projection_mem hQ hNQ hprod n⟩
  refine ⟨⟨⟨w, w.property.2⟩, w.property⟩, hQ.projection_inv_mul_mem
    (Subgroup.inclusion hNQ n), ?_⟩
  intro w' hw'
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : L => (x : G))
    ((hQ.projection_eq_iff (Subgroup.inclusion hNQ n)
      ⟨w'.val.val, w'.property.1⟩).mpr hw').symm

/-- Its canonical projection is the restriction of the outer projection. -/
theorem radical_projection (n : N) :
    ((radicalDecomposition hQ hNQ hprod).projection n : G) =
      (hQ.projection (Subgroup.inclusion hNQ n) : G) := by
  let w : (L ⊓ N : Subgroup G) := ⟨hQ.projection (Subgroup.inclusion hNQ n),
    (hQ.projection (Subgroup.inclusion hNQ n)).property, projection_mem hQ hNQ hprod n⟩
  exact congrArg (fun x : (L ⊓ N : Subgroup G) => (x : G))
    (((radicalDecomposition hQ hNQ hprod).projection_eq_iff n w).mpr
      (hQ.projection_inv_mul_mem (Subgroup.inclusion hNQ n)))

end Algebra

section Topology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Q L U N : Subgroup G}
    (hQ : IsSemidirectDecomposition Q L U) (hNQ : N ≤ Q)
    (hprod : (N : Set G) = (L ⊓ N : Subgroup G) * (U : Set G))

include hQ hNQ hprod

omit [IsTopologicalGroup G] in
/-- The restricted radical projection is continuous in the original subspace topologies. -/
theorem continuous_radical_projection (hp : Continuous hQ.projection) :
    Continuous (radicalDecomposition hQ hNQ hprod).projection := by
  have heq : (fun n : N => ((radicalDecomposition hQ hNQ hprod).projection n : G)) =
      fun n : N => (hQ.projection (Subgroup.inclusion hNQ n) : G) :=
    funext (radical_projection hQ hNQ hprod)
  apply continuous_induced_rng.mpr
  change Continuous (fun n : N => ((radicalDecomposition hQ hNQ hprod).projection n : G))
  rw [heq]
  exact continuous_subtype_val.comp (hp.comp (continuous_subtype_val.subtype_mk _))

omit hQ hNQ hprod [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The final normalizing subgroup preserves the actual inner radical. -/
theorem normalizes_inter {S : Subgroup G} (hSL : S ≤ L)
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) :
    S ≤ Subgroup.normalizer ((L ⊓ N : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro s hs w hw
  exact ⟨L.mul_mem (L.mul_mem (hSL hs) hw.1) (L.inv_mem (hSL hs)),
    (Subgroup.le_normalizer_iff.mp hSN) s hs w hw.2⟩

end Topology

section Modulus

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    {Q L U N : Subgroup G}
    (hQ : IsSemidirectDecomposition Q L U) (hNQ : N ≤ Q)
    (hprod : (N : Set G) = (L ⊓ N : Subgroup G) * (U : Set G))
    (hp : Continuous hQ.projection)
    (hN : IsClosed (N : Set G)) (hU : IsClosed (U : Set G))
    (hL : IsClosed (L : Set G))

include hQ hNQ hprod hp

/-- Haar scaling on the fine radical is the product of the two factor scalings. -/
theorem ambient_modulus_product {S : Subgroup G} (hSL : S ≤ L)
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) (s : S) :
    HaarModulus.closedRestrictCharacter N hN S hSN s =
      HaarModulus.closedRestrictCharacter (L ⊓ N) (hL.inter hN) S
        (normalizes_inter hSL hSN) s *
      HaarModulus.closedRestrictCharacter U hU S
        (hSL.trans hQ.levi_le_normalizer) s := by
  let : LocallyCompactSpace N := hN.locallyCompactSpace
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : LocallyCompactSpace (L ⊓ N : Subgroup G) := (hL.inter hN).locallyCompactSpace
  let : MeasurableSpace N := borel _
  have : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace U := borel _
  have : BorelSpace U := ⟨rfl⟩
  let : MeasurableSpace (L ⊓ N : Subgroup G) := borel _
  have : BorelSpace (L ⊓ N : Subgroup G) := ⟨rfl⟩
  let d := radicalDecomposition hQ hNQ hprod
  have hd := continuous_radical_projection hQ hNQ hprod hp
  apply Units.ext
  change mulEquivHaarChar (HaarModulus.normalizerConj N ⟨s, hSN s.property⟩) =
    mulEquivHaarChar (HaarModulus.normalizerConj (L ⊓ N)
      ⟨s, normalizes_inter hSL hSN s.property⟩) *
    mulEquivHaarChar (HaarModulus.normalizerConj U
      ⟨s, hQ.levi_le_normalizer (hSL s.property)⟩)
  apply d.haarChar_eq_mul hd
  intro w u
  apply Subtype.ext
  change (s : G) * ((w : G) * (u : G)) * (s : G)⁻¹ =
    ((s : G) * (w : G) * (s : G)⁻¹) * ((s : G) * (u : G) * (s : G)⁻¹)
  group

end Modulus

section Copies

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual ambient intersection and the literal radical copy inside the Levi. -/
def interSubgroupOfEquiv (L N : Subgroup G) :
    (L ⊓ N : Subgroup G) ≃ₜ* N.subgroupOf L where
  toFun n := ⟨⟨n.val, n.property.1⟩, n.property.2⟩
  invFun n := ⟨n.val.val, n.val.property, n.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

variable [LocallyCompactSpace G] {N L S : Subgroup G}
    (hN : IsClosed (N : Set G)) (hL : IsClosed (L : Set G))
    (hSL : S ≤ L) (hSN : S ≤ Subgroup.normalizer (N : Set G))

/-- Haar scaling agrees under the actual intersection-to-subgroup-copy isomorphism. -/
theorem inner_modulus_eq (s : S) :
    let : LocallyCompactSpace L := hL.locallyCompactSpace
    HaarModulus.closedRestrictCharacter (N.subgroupOf L)
      (hN.preimage continuous_subtype_val) (S.subgroupOf L)
      (normalizes_subgroupOf hSN) ((subgroupOfContinuousEquiv hSL).symm s) =
    HaarModulus.closedRestrictCharacter (L ⊓ N) (hL.inter hN) S
      (normalizes_inter hSL hSN) s := by
  let : LocallyCompactSpace L := hL.locallyCompactSpace
  let : LocallyCompactSpace (N.subgroupOf L) :=
    (hN.preimage continuous_subtype_val).locallyCompactSpace
  let : LocallyCompactSpace (L ⊓ N : Subgroup G) := (hL.inter hN).locallyCompactSpace
  let : MeasurableSpace (N.subgroupOf L) := borel _
  have : BorelSpace (N.subgroupOf L) := ⟨rfl⟩
  let : MeasurableSpace (L ⊓ N : Subgroup G) := borel _
  have : BorelSpace (L ⊓ N : Subgroup G) := ⟨rfl⟩
  let e := interSubgroupOfEquiv L N
  let a := HaarModulus.normalizerConj (N.subgroupOf L)
    ⟨(subgroupOfContinuousEquiv hSL).symm s, normalizes_subgroupOf hSN
      ((subgroupOfContinuousEquiv hSL).symm s).property⟩
  let b := HaarModulus.normalizerConj (L ⊓ N)
    ⟨s, normalizes_inter hSL hSN s.property⟩
  have hab : (e.trans a).trans e.symm = b := by
    ext n
    rfl
  apply Units.ext
  change mulEquivHaarChar a = mulEquivHaarChar b
  rw [← hab, mulEquivHaarChar_trans_symm]

end Copies

end Langlands.Aubert.General.NestedParabolic
