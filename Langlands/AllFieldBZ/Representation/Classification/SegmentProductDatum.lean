import Langlands.AllFieldBZ.Representation.Classification.OrderedSegmentProducts

/-! Ordered products of segment socles over a nonarchimedean local field. -/

noncomputable section

namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData

universe uV uF

variable {F : LocalFieldPackage.{uF}} {T : F.TopologicalData}

namespace Segment

/-- The finite set of cuspidal classes belonging to a segment. -/
def support (Δ : Segment.{uV,uF} T) : Set (CuspidalDatum.{uV,uF} T) :=
  {ρ | ∃ i < Δ.length, Δ.member i = ρ}

/-- Linked segments have a segment as their union and neither contains the other. -/
def IsLinked (Δ Γ : Segment.{uV,uF} T) : Prop :=
  ¬ Δ.support ⊆ Γ.support ∧ ¬ Γ.support ⊆ Δ.support ∧
    ∃ Ξ : Segment.{uV,uF} T, Ξ.support = Δ.support ∪ Γ.support

/-- The second segment starts at a strictly positive twist of the first,
and the two segments are linked. -/
def Precedes (Δ Γ : Segment.{uV,uF} T) : Prop :=
  Δ.IsLinked Γ ∧ ∃ k : ℕ, 0 < k ∧ Γ.base = Δ.base.twist (k : ℝ)

end Segment

/-- A finite multiset of segments, with repetitions and the empty multiset allowed. -/
abbrev Multisegment (T : F.TopologicalData) := Multiset (Segment.{uV,uF} T)

/-- Block degrees add with their multiplicities. -/
def Multisegment.degree (a : Multisegment.{uV,uF} T) : ℕ :=
  (a.map Segment.degree).sum

/-- No earlier segment precedes a later segment. -/
def IsPrecedenceOrdered {k : ℕ} (Δ : Fin k → Segment.{uV,uF} T) : Prop :=
  ∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)

/-- The ordered block shape of a finite family of segments. -/
def segmentShape {k n : ℕ} (Δ : Fin k → Segment.{uV,uF} T)
    (h : ∑ i, (Δ i).degree = n) : GeneralLinear.BlockShape n where
  length := k
  size i := (Δ i).degree
  positive i := (Δ i).degree_pos
  sum_eq := h

/-- An ordering of segments and actual smooth blocks of their prescribed degrees. -/
structure SegmentProductDatum (T : F.TopologicalData) (n : ℕ) where
  length : ℕ
  segments : Fin length → Segment.{uV,uF} T
  degree_sum : ∑ i, (segments i).degree = n
  blocks : letI := T.topology
    ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (segments i).degree F.Carrier)

namespace SegmentProductDatum

variable {n : ℕ} (d : SegmentProductDatum.{uV,uF} T n)

/-- The ordered composition of the total degree. -/
def shape : GeneralLinear.BlockShape n := segmentShape d.segments d.degree_sum

/-- The multisegment enumerated by the datum. -/
def multisegment : Multisegment.{uV,uF} T := List.ofFn d.segments

@[simp]
theorem multisegment_degree : d.multisegment.degree = n := by
  rw [Multisegment.degree, multisegment, Multiset.map_coe, Multiset.sum_coe,
    List.map_ofFn, List.sum_ofFn]
  exact d.degree_sum

/-- The actual normalized upper-parabolic induction of the block family. -/
def induced :
    letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor d.shape).obj d.blocks

/-- Every block is an actual socle of its segment induction. -/
def HasSegmentSocles : Prop :=
  ∀ i, T.IsSegmentSocle (d.segments i) (d.blocks i)

/-- The ordering condition of Zelevinsky's socle classification. -/
def IsPrecedenceOrdered : Prop :=
  TopologicalData.IsPrecedenceOrdered d.segments

/-- An irreducible subrepresentation of this product of segment socles. -/
def HasSocleEmbedding
    (π : letI := T.topology;
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  d.HasSegmentSocles ∧
    Langlands.Classification.IsIrreducibleSubrepresentation d.induced.representation π.representation

/-- The unique irreducible subobject of a precedence-ordered product of segment socles. -/
def IsZelevinskySocle
    (π : letI := T.topology;
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  d.IsPrecedenceOrdered ∧ d.HasSegmentSocles ∧
    Langlands.Classification.IsIrreducibleSocle d.induced.representation π.representation

end SegmentProductDatum

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
