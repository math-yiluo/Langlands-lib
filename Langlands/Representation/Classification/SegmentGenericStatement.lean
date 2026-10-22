import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.SegmentConstituentStatement
import Langlands.Representation.Whittaker.GeneralLinear

/-!
# Segment products and generic multisegments

Proposition definitions for Zelevinsky 1980, Theorems 4.2 and 9.7 and §9.10.
The special constituent is the head of the increasing segment product; it is
distinct from the segment socle used to construct `Z(a)`.
Nondegeneracy of a possibly reducible special product asserts only existence of
a nonzero Whittaker functional. No classification or uniqueness is assumed.
-/

namespace Langlands.Classification

open CategoryTheory GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Ze80 Theorem 4.2: the product of segment socles is irreducible exactly when
no two of the segments are linked. The ordering is unrestricted. -/
def SegmentSocleProductIrreducibility : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{uV, uF} (n + 1)),
    d.HasSegmentSocles →
      (Representation.IsIrreducible d.induced.representation ↔
        d.multisegment.IsUnlinked)

/-- Ze80 Theorem 9.7(a), nondegeneracy clause: every product of special segment
heads has a nonzero standard Whittaker functional, including reducible products. -/
def SegmentHeadProductNondegeneracy : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (d : T.SegmentProductDatum.{uV, uF} (n + 1)),
    d.HasSegmentHeads →
      Whittaker.HasFunctional
        (N := upperUnipotent (n + 1) F.Carrier)
        (θ := Whittaker.standardCharacter ψ n) d.induced.representation

/-- Ze80 Theorem 9.7(a), irreducibility clause: a product of special segment
heads is irreducible exactly when its segments are pairwise nonlinked. -/
def SegmentHeadProductIrreducibility : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{uV, uF} (n + 1)),
    d.HasSegmentHeads →
      (Representation.IsIrreducible d.induced.representation ↔
        d.multisegment.IsUnlinked)

/-- The generic reformulation of Ze80 Theorem 9.7(a), using admissibility of
irreducible smooth representations (BZ77 Theorem 2.5).
Unlike nondegeneracy alone, `IsGeneric` includes irreducibility. -/
def SegmentHeadProductGenericity : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (d : T.SegmentProductDatum.{uV, uF} (n + 1)),
    d.HasSegmentHeads →
      (Whittaker.IsGeneric ψ n d.induced.representation ↔
        d.multisegment.IsUnlinked)

/-- Ze80 Theorem 9.7(b), with (a) for the reverse implication: a smooth
representation is generic exactly when it is isomorphic to a product of special
heads for pairwise nonlinked segments. Segment bases live in the same universe
as the representation being classified; no carrier resizing is assumed. -/
def GenericSegmentProductExhaustion : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)),
    Whittaker.IsGeneric ψ n π.representation ↔
      ∃ d : T.SegmentProductDatum.{max uF uV, uF} (n + 1),
        d.HasSegmentHeads ∧ d.multisegment.IsUnlinked ∧ Nonempty (π ≅ d.induced)

/-- Ze80 Theorem 9.7(b) and §9.10: two irreducible products of special heads
are isomorphic exactly when their unordered segment multisets agree.
Repeated segments retain their multiplicities. -/
def GenericSegmentProductUniqueness : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d e : T.SegmentProductDatum.{max uF uV, uF} (n + 1)),
    d.HasSegmentHeads → e.HasSegmentHeads →
    d.multisegment.IsUnlinked → e.multisegment.IsUnlinked →
      (Nonempty (d.induced ≅ e.induced) ↔ d.multisegment = e.multisegment)

/-- Ze80 §9.10, from Theorem 8.1: `Z(a)` is generic exactly when every segment
of `a` has length one. This concerns the socle classification, not the special
head product, and imposes no pairwise nonlinkage condition. -/
def ZelevinskySocleGenericity : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (a : T.Multisegment.{uV, uF})
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)),
    a.IsZelevinskySocle π →
      (Whittaker.IsGeneric ψ n π.representation ↔
        ∀ Δ ∈ a, Δ.length = 1)

/-- The segment-product and generic-multisegment statement family over one
actual p-adic field and compatible topological realization. -/
def SegmentGenericTheorems : Prop :=
  SegmentSocleProductIrreducibility.{uF, uV} F T ∧
    SegmentHeadProductNondegeneracy.{uF, uV} F T ∧
    SegmentHeadProductIrreducibility.{uF, uV} F T ∧
    SegmentHeadProductGenericity.{uF, uV} F T ∧
    GenericSegmentProductExhaustion.{uF, uV} F T ∧
    GenericSegmentProductUniqueness.{uF, uV} F T ∧
    ZelevinskySocleGenericity.{uF, uV} F T

/-- The entire statement family over every prime, every actual finite
p-adic extension and every compatible topological realization. -/
def PadicSegmentGenericTheorems : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    SegmentGenericTheorems.{uF, uV} F T

end Langlands.Classification
