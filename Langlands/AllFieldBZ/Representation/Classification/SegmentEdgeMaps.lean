import Langlands.Representation.Classification.SegmentEdgeMaps
import Langlands.AllFieldBZ.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.AllFieldBZ.Representation.Induction.Equivalences
import Langlands.AllFieldBZ.Group.GL.CompactOpen

/-! Actual maps arising from replacing one adjacent induction slot. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

namespace Langlands.AllFieldBZ.Classification.SegmentEdge

open Langlands.GeneralLinear Langlands.Geometric CategoryTheory
open Langlands.Classification.SegmentEdge (updateHom updateHomTo updateHom_surjective
  updateHomTo_injective hom_iso_bijective hom_iso_inv_bijective comp_injective)

universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

section Exactness

variable {n : ℕ} (B : BlockShape n)

/-- Blockwise injective intertwiners induce an injective intertwiner. -/
theorem normalizedProductInducedMap_injective
    {A A' : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    (f : letI := T.topology
      ∀ i, (A i).representation.IntertwiningMap (A' i).representation)
    (hf : ∀ i, Function.Injective (f i)) :
    letI := T.topology
    Function.Injective (T.normalizedProductInducedMap B f) :=
  T.normalizedParabolicInducedMap_injective B (FiniteTensor.externalMap f)
    (FiniteTensor.externalMap_injective f hf)

/-- The functor `i_B` preserves blockwise injective morphisms. -/
theorem productInduction_map_injective
    {A A' : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    (φ : letI := T.topology; A ⟶ A')
    (hφ : letI := T.topology; ∀ i, Function.Injective (SmoothRep.hom (φ i))) :
    letI := T.topology
    Function.Injective (SmoothRep.hom ((T.normalizedProductInductionFunctor B).map φ)) := by
  let := T.topology
  exact normalizedProductInducedMap_injective T B (fun i => SmoothRep.hom (φ i)) hφ

/-- The functor `i_B` preserves blockwise surjective morphisms. -/
theorem productInduction_map_surjective
    {A A' : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    (φ : letI := T.topology; A ⟶ A')
    (hφ : letI := T.topology; ∀ i, Function.Surjective (SmoothRep.hom (φ i))) :
    letI := T.topology
    Function.Surjective (SmoothRep.hom ((T.normalizedProductInductionFunctor B).map φ)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearT2Space n
  let X := FiniteTensor.externalSmoothObject A
  let Y := FiniteTensor.externalSmoothObject A'
  let f := FiniteTensor.externalMap (fun i => SmoothRep.hom (φ i))
  have hf : Function.Surjective f :=
    FiniteTensor.externalMapSurjectivity ℂ _ _ _ _ _ _ (fun i => SmoothRep.hom (φ i)) hφ
  change Function.Surjective (T.normalizedParabolicInducedMap B f)
  let χ := B.inflateCharacter (T.leviHalfCharacter B)
  apply Induction.smoothInductionSurjectivity (GeneralLinear n F.Carrier)
  · intro K
    let L := T.generalLinearCompactOpen n K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L.1, L.2.1, L.2.2⟩
  · exact B.isClosed_parabolic F.Carrier
  · exact (isSmooth_twist_iff χ.toMonoidHom _ χ.isOpen_ker).mpr
      (isSmooth_comp (B.leviProjection F.Carrier)
        (B.leviProjectionContinuous F.Carrier).continuous X.isSmooth)
  · exact (isSmooth_twist_iff χ.toMonoidHom _ χ.isOpen_ker).mpr
      (isSmooth_comp (B.leviProjection F.Carrier)
        (B.leviProjectionContinuous F.Carrier).continuous Y.isSmooth)
  · exact hf

end Exactness

section Edge

variable {n : ℕ} (B : BlockShape n) (k : ℕ) (hk : k + 1 < B.length)

/-- The slot products of the merge of blocks `k`, `k + 1`: slot `j` of
`γ = B.adjacentMerge k` carries `i_{S_j}(σ_{e(j,0)}, …)` for
`S = B.adjacentRefinement k` and `e = B.adjacentBlockEquiv k`. -/
abbrev slotFamily
    (σ : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (j : Fin (B.adjacentMerge k hk).length) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((B.adjacentMerge k hk).size j) F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor (B.adjacentRefinement k hk j)).obj
    (fun t => σ (B.adjacentBlockEquiv k hk ⟨j, t⟩))

/-- The size casts in the ordered regrouping of an adjacent merge are trivial. -/
theorem adjacent_inner_eq
    (σ : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (fun i j => (B.adjacentBlock_size k hk ⟨i,j⟩).symm ▸ σ (B.adjacentBlockEquiv k hk ⟨i,j⟩)) =
      (fun i j => σ (B.adjacentBlockEquiv k hk ⟨i,j⟩)) := by
  funext i j
  rfl

/-- Induction in stages along an exact ordered refinement, with the inner factors
and the inner products given up to equalities of families (the pattern of the
Library's `composeProductRegroupingIso`). -/
def stagesIso {m : ℕ} (C D : BlockShape m)
    (S : Geometric.BlockRefinement D)
    (e : ((j : Fin D.length) × Fin (S j).length) ≃ Fin C.length)
    (hs : ∀ a, (S a.1).size a.2 = C.size (e a))
    (hc : ∀ j k (x : Fin ((S j).size k)),
      D.index j ((S j).index k x) = C.index (e ⟨j,k⟩) (Fin.cast (hs ⟨j,k⟩) x))
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (C.size i) F.Carrier))
    (inner : letI := T.topology
      ∀ i j, SmoothRep.{0,uF,uV} ℂ (GeneralLinear ((S i).size j) F.Carrier))
    (hinner : letI := T.topology
      (fun i j => (hs ⟨i,j⟩).symm ▸ σ (e ⟨i,j⟩)) = inner)
    (products : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (D.size i) F.Carrier))
    (hproducts : letI := T.topology
      (fun i => (T.normalizedProductInductionFunctor (S i)).obj (inner i)) = products) :
    letI := T.topology
    (T.normalizedProductInductionFunctor C).obj σ ≅
      (T.normalizedProductInductionFunctor D).obj products := by
  letI := T.topology
  let hfamily := congrArg
    (fun υ => fun i => (T.normalizedProductInductionFunctor (S i)).obj (υ i)) hinner
  let g := eqToIso (hfamily.trans hproducts)
  exact Classical.choice (AllFieldBZ.Parabolic.orderedProductRegrouping F T m C D S e hs hc σ) ≪≫
    (T.normalizedProductInductionFunctor D).mapIso g

/-- The inner products of the regrouping are the slot family. -/
theorem slotFamily_eq
    (σ : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (fun i => (T.normalizedProductInductionFunctor (B.adjacentRefinement k hk i)).obj
      (fun j => σ (B.adjacentBlockEquiv k hk ⟨i,j⟩))) = slotFamily T B k hk σ :=
  rfl

/-- Induction in stages along the merge of blocks `k`, `k + 1`:
`i_B(σ) ≅ i_γ(slotFamily σ)`, chosen from the ordered regrouping theorem. -/
def regroupIso
    (σ : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor B).obj σ ≅
      (T.normalizedProductInductionFunctor (B.adjacentMerge k hk)).obj
        (slotFamily T B k hk σ) := by
  letI := T.topology
  exact stagesIso T B (B.adjacentMerge k hk) (B.adjacentRefinement k hk)
    (B.adjacentBlockEquiv k hk) (B.adjacentBlock_size k hk) (B.adjacent_index k hk) σ
    (fun i j => σ (B.adjacentBlockEquiv k hk ⟨i,j⟩)) (adjacent_inner_eq T B k hk σ)
    (slotFamily T B k hk σ) (slotFamily_eq T B k hk σ)

/-- The map `i_B(σ) → i_γ(…, Q, …)` induced by `f : slotFamily σ j → Q` at slot `j`. -/
def slotQuotientMap
    (σ : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (j : Fin (B.adjacentMerge k hk).length)
    {Q : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((B.adjacentMerge k hk).size j) F.Carrier)}
    (f : letI := T.topology; slotFamily T B k hk σ j ⟶ Q) :
    letI := T.topology
    (T.normalizedProductInductionFunctor B).obj σ ⟶
      (T.normalizedProductInductionFunctor (B.adjacentMerge k hk)).obj
        (Function.update (slotFamily T B k hk σ) j Q) :=
  letI := T.topology
  (regroupIso T B k hk σ).hom ≫
    (T.normalizedProductInductionFunctor (B.adjacentMerge k hk)).map
      (updateHom (slotFamily T B k hk σ) j f)

/-- The map `i_γ(…, Q, …) → i_B(σ)` induced by `g : Q → slotFamily σ j` at slot `j`. -/
def slotSubMap
    (σ : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (j : Fin (B.adjacentMerge k hk).length)
    {Q : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((B.adjacentMerge k hk).size j) F.Carrier)}
    (g : letI := T.topology; Q ⟶ slotFamily T B k hk σ j) :
    letI := T.topology
    (T.normalizedProductInductionFunctor (B.adjacentMerge k hk)).obj
        (Function.update (slotFamily T B k hk σ) j Q) ⟶
      (T.normalizedProductInductionFunctor B).obj σ :=
  letI := T.topology
  (T.normalizedProductInductionFunctor (B.adjacentMerge k hk)).map
      (updateHomTo (slotFamily T B k hk σ) j g) ≫
    (regroupIso T B k hk σ).inv

theorem slotQuotientMap_surjective
    (σ : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (j : Fin (B.adjacentMerge k hk).length)
    {Q : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((B.adjacentMerge k hk).size j) F.Carrier)}
    (f : letI := T.topology; slotFamily T B k hk σ j ⟶ Q)
    (hf : letI := T.topology; Function.Surjective (SmoothRep.hom f)) :
    letI := T.topology
    Function.Surjective (SmoothRep.hom (slotQuotientMap T B k hk σ j f)) := by
  let := T.topology
  exact (productInduction_map_surjective T (B.adjacentMerge k hk) _
    (updateHom_surjective _ j f hf)).comp (hom_iso_bijective (regroupIso T B k hk σ)).2

theorem slotSubMap_injective
    (σ : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (j : Fin (B.adjacentMerge k hk).length)
    {Q : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((B.adjacentMerge k hk).size j) F.Carrier)}
    (g : letI := T.topology; Q ⟶ slotFamily T B k hk σ j)
    (hg : letI := T.topology; Function.Injective (SmoothRep.hom g)) :
    letI := T.topology
    Function.Injective (SmoothRep.hom (slotSubMap T B k hk σ j g)) := by
  let := T.topology
  have h1 := productInduction_map_injective T (B.adjacentMerge k hk)
    (updateHomTo (slotFamily T B k hk σ) j g)
    (updateHomTo_injective (slotFamily T B k hk σ) j g hg)
  have h2 := (hom_iso_inv_bijective (regroupIso T B k hk σ)).1
  exact comp_injective _ _ h1 h2

/-- The surjection `i_B(σ) → i_γ(…, slotFamily σ j / W, …)`. -/
def edgeQuotientMap
    (σ : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (j : Fin (B.adjacentMerge k hk).length)
    (W : letI := T.topology; Subrepresentation (slotFamily T B k hk σ j).representation) :
    letI := T.topology
    (T.normalizedProductInductionFunctor B).obj σ ⟶
      (T.normalizedProductInductionFunctor (B.adjacentMerge k hk)).obj
        (Function.update (slotFamily T B k hk σ) j
          (SmoothRep.quotient (slotFamily T B k hk σ j) W)) :=
  letI := T.topology
  slotQuotientMap T B k hk σ j (SmoothRep.mkQ _ W)

theorem edgeQuotientMap_surjective
    (σ : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (j : Fin (B.adjacentMerge k hk).length)
    (W : letI := T.topology; Subrepresentation (slotFamily T B k hk σ j).representation) :
    letI := T.topology
    Function.Surjective (SmoothRep.hom (edgeQuotientMap T B k hk σ j W)) := by
  let := T.topology
  exact slotQuotientMap_surjective T B k hk σ j _ (SmoothRep.mkQ_surjective _ W)

/-- The injection `i_γ(…, W, …) → i_B(σ)` for a subrepresentation `W` of
`slotFamily σ j`. -/
def edgeSubMap
    (σ : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (j : Fin (B.adjacentMerge k hk).length)
    (W : letI := T.topology; Subrepresentation (slotFamily T B k hk σ j).representation) :
    letI := T.topology
    (T.normalizedProductInductionFunctor (B.adjacentMerge k hk)).obj
        (Function.update (slotFamily T B k hk σ) j
          (SmoothRep.subrepresentation (slotFamily T B k hk σ j) W)) ⟶
      (T.normalizedProductInductionFunctor B).obj σ :=
  letI := T.topology
  slotSubMap T B k hk σ j (SmoothRep.subtype _ W)

theorem edgeSubMap_injective
    (σ : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (j : Fin (B.adjacentMerge k hk).length)
    (W : letI := T.topology; Subrepresentation (slotFamily T B k hk σ j).representation) :
    letI := T.topology
    Function.Injective (SmoothRep.hom (edgeSubMap T B k hk σ j W)) := by
  let := T.topology
  exact slotSubMap_injective T B k hk σ j _ (SmoothRep.subtype_injective _ W)

end Edge

end Langlands.AllFieldBZ.Classification.SegmentEdge
