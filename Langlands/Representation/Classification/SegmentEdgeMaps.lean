import Langlands.Representation.Parabolic.InducedMapSurjectivity
import Langlands.Representation.Classification.Segments
import Langlands.Representation.Classification.IrreducibleProductEmbedding
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Tensor.ExternalMapSurjectivityProof
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Category.Subquotients
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.AdjacentMergeShape

/-!
# One-slot exactness of product induction and the edge maps of a merged slot

Normalized product induction `i_B` takes blockwise injective (resp. surjective)
intertwiners to injective (resp. surjective) intertwiners. Regrouping
`i_β(σ) ≅ i_γ(Y)` along the merge `γ` of the adjacent blocks `k, k + 1` of `β`,
where `Y_j = i_{S_j}(σ_{e(j,0)}, …)`, this gives, for a subrepresentation `W` of
the slot `Y_kk`, a surjection `i_β(σ) → i_γ(…, Y_kk / W, …)` and an injection
`i_γ(…, W, …) → i_β(σ)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification.SegmentEdge

open GeneralLinear Geometric CategoryTheory

universe uF uV

section Update

variable {ι : Type*} [DecidableEq ι] {C : ι → Type*} [∀ i, Category (C i)]

/-- The family morphism that is `f` at slot `j` and the identity elsewhere. -/
def updateHom (X : ∀ i, C i) (j : ι) {Y : C j} (f : X j ⟶ Y) :
    X ⟶ Function.update X j Y := fun i =>
  if h : i = j then by
    subst h
    exact f ≫ eqToHom (Function.update_self i Y X).symm
  else eqToHom (Function.update_of_ne h Y X).symm

/-- The family morphism into `X` that is `f` at slot `j` and the identity elsewhere. -/
def updateHomTo (X : ∀ i, C i) (j : ι) {Y : C j} (f : Y ⟶ X j) :
    Function.update X j Y ⟶ X := fun i =>
  if h : i = j then by
    subst h
    exact eqToHom (Function.update_self i Y X) ≫ f
  else eqToHom (Function.update_of_ne h Y X)

end Update

section SmoothFamilies

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G]

theorem hom_eqToHom_bijective {A B : SmoothRep R G} (h : A = B) :
    Function.Bijective (SmoothRep.hom (eqToHom h)) := by
  subst h
  exact Function.bijective_id

theorem hom_iso_bijective {A B : SmoothRep R G} (e : A ≅ B) :
    Function.Bijective (SmoothRep.hom e.hom) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨SmoothRep.hom e.inv, fun x => ?_, fun y => ?_⟩
  · exact congrArg (fun f => SmoothRep.hom f x) e.hom_inv_id
  · exact congrArg (fun f => SmoothRep.hom f y) e.inv_hom_id

theorem comp_injective {A B C : SmoothRep R G} (f : A ⟶ B) (g : B ⟶ C)
    (hf : Function.Injective (SmoothRep.hom f)) (hg : Function.Injective (SmoothRep.hom g)) :
    Function.Injective (SmoothRep.hom (f ≫ g)) :=
  fun _ _ h => hf (hg h)

theorem hom_iso_inv_bijective {A B : SmoothRep R G} (e : A ≅ B) :
    Function.Bijective (SmoothRep.hom e.inv) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨SmoothRep.hom e.hom, fun x => ?_, fun y => ?_⟩
  · exact congrArg (fun f => SmoothRep.hom f x) e.inv_hom_id
  · exact congrArg (fun f => SmoothRep.hom f y) e.hom_inv_id

variable {ι : Type*} [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
  [∀ i, TopologicalSpace (H i)]

theorem updateHom_injective (X : ∀ i, SmoothRep R (H i)) (j : ι) {Y : SmoothRep R (H j)}
    (f : X j ⟶ Y) (hf : Function.Injective (SmoothRep.hom f)) (i : ι) :
    Function.Injective (SmoothRep.hom (updateHom X j f i)) := by
  unfold updateHom
  split_ifs with h
  · subst h
    exact (hom_eqToHom_bijective _).1.comp hf
  · exact (hom_eqToHom_bijective _).1

theorem updateHom_surjective (X : ∀ i, SmoothRep R (H i)) (j : ι) {Y : SmoothRep R (H j)}
    (f : X j ⟶ Y) (hf : Function.Surjective (SmoothRep.hom f)) (i : ι) :
    Function.Surjective (SmoothRep.hom (updateHom X j f i)) := by
  unfold updateHom
  split_ifs with h
  · subst h
    exact (hom_eqToHom_bijective _).2.comp hf
  · exact (hom_eqToHom_bijective _).2

theorem updateHomTo_injective (X : ∀ i, SmoothRep R (H i)) (j : ι) {Y : SmoothRep R (H j)}
    (f : Y ⟶ X j) (hf : Function.Injective (SmoothRep.hom f)) (i : ι) :
    Function.Injective (SmoothRep.hom (updateHomTo X j f i)) := by
  unfold updateHomTo
  split_ifs with h
  · subst h
    exact hf.comp (hom_eqToHom_bijective _).1
  · exact (hom_eqToHom_bijective _).1

theorem updateHomTo_surjective (X : ∀ i, SmoothRep R (H i)) (j : ι) {Y : SmoothRep R (H j)}
    (f : Y ⟶ X j) (hf : Function.Surjective (SmoothRep.hom f)) (i : ι) :
    Function.Surjective (SmoothRep.hom (updateHomTo X j f i)) := by
  unfold updateHomTo
  split_ifs with h
  · subst h
    exact hf.comp (hom_eqToHom_bijective _).2
  · exact (hom_eqToHom_bijective _).2

end SmoothFamilies

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

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
  exact normalizedProductMap_surjective F T B _ _ (fun i => SmoothRep.hom (φ i)) hφ

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
  exact Classical.choice (Parabolic.orderedProductRegrouping F T m C D S e hs hc σ) ≪≫
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

section Segment

variable {r : ℕ} (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
  (m : ℕ) (hr : 0 < r) (k : ℕ) (hk : k + 1 < (BlockShape.uniform m r hr).length)

/-- For a subrepresentation `W` of the merged slot product
`i_{(r,r)}(ν^k A, ν^(k+1) A)`, the surjection of the segment induction onto
`i_γ(…, slot / W, …)`. -/
def segmentEdgeQuotientMap
    (W : letI := T.topology
      Subrepresentation (slotFamily T (BlockShape.uniform m r hr) k hk (T.segmentFactors A m hr)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation) :
    letI := T.topology
    T.segmentInduced A m hr ⟶
      (T.normalizedProductInductionFunctor ((BlockShape.uniform m r hr).adjacentMerge k hk)).obj
        (Function.update (slotFamily T (BlockShape.uniform m r hr) k hk (T.segmentFactors A m hr))
          ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)
          (SmoothRep.quotient (slotFamily T (BlockShape.uniform m r hr) k hk
            (T.segmentFactors A m hr) ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)) W)) :=
  edgeQuotientMap T (BlockShape.uniform m r hr) k hk (T.segmentFactors A m hr) _ W

theorem segmentEdgeQuotientMap_surjective
    (W : letI := T.topology
      Subrepresentation (slotFamily T (BlockShape.uniform m r hr) k hk (T.segmentFactors A m hr)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation) :
    letI := T.topology
    Function.Surjective (SmoothRep.hom (segmentEdgeQuotientMap T A m hr k hk W)) :=
  edgeQuotientMap_surjective T (BlockShape.uniform m r hr) k hk (T.segmentFactors A m hr) _ W

/-- For a subrepresentation `W` of the merged slot product, the injection of
`i_γ(…, W, …)` into the segment induction. -/
def segmentEdgeSubMap
    (W : letI := T.topology
      Subrepresentation (slotFamily T (BlockShape.uniform m r hr) k hk (T.segmentFactors A m hr)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation) :
    letI := T.topology
    (T.normalizedProductInductionFunctor ((BlockShape.uniform m r hr).adjacentMerge k hk)).obj
        (Function.update (slotFamily T (BlockShape.uniform m r hr) k hk (T.segmentFactors A m hr))
          ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)
          (SmoothRep.subrepresentation (slotFamily T (BlockShape.uniform m r hr) k hk
            (T.segmentFactors A m hr) ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)) W)) ⟶
      T.segmentInduced A m hr :=
  edgeSubMap T (BlockShape.uniform m r hr) k hk (T.segmentFactors A m hr) _ W

theorem segmentEdgeSubMap_injective
    (W : letI := T.topology
      Subrepresentation (slotFamily T (BlockShape.uniform m r hr) k hk (T.segmentFactors A m hr)
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).representation) :
    letI := T.topology
    Function.Injective (SmoothRep.hom (segmentEdgeSubMap T A m hr k hk W)) :=
  edgeSubMap_injective T (BlockShape.uniform m r hr) k hk (T.segmentFactors A m hr) _ W

end Segment

end Langlands.Classification.SegmentEdge
