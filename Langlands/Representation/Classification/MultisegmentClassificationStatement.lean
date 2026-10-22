import Langlands.Representation.Classification.LanglandsData

/-!
# Multisegment and special-block Langlands classification statements

Zelevinsky's socle classification and the special-head quotient classification
are stated on actual normalized upper-parabolic products. Both use the condition
that no earlier segment precedes a later one. Existence, uniqueness, independence
and exhaustion are assertions, not fields of classification data.
-/

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Ze80 §6.5: every multisegment has an enumeration with no earlier segment
preceding a later one, with the expected total degree. Includes the empty case. -/
def MultisegmentNonprecedenceEnumeration : Prop :=
  ∀ a : T.Multisegment.{max uF uV, uF},
    ∃ (r : ℕ) (Δ : Fin r → T.Segment.{max uF uV, uF}),
      a.IsOrdering Δ ∧ T.IsPrecedenceOrdered Δ ∧ ∑ i, (Δ i).degree = a.degree

/-- Ze80 §§3.1, 6.5 and 9.1: every multisegment has genuine ordered product data
using segment socles, and genuine ordered product data using segment heads.
Neither datum includes a head or socle of the full product. -/
def MultisegmentConstituentDataExistence : Prop :=
  ∀ a : T.Multisegment.{max uF uV, uF},
    (∃ d : T.SegmentProductDatum.{max uF uV, uF} a.degree,
      d.multisegment = a ∧ d.IsPrecedenceOrdered ∧ d.HasSegmentSocles) ∧
    (∃ d : T.SegmentProductDatum.{max uF uV, uF} a.degree,
      d.multisegment = a ∧ d.IsPrecedenceOrdered ∧ d.HasSegmentHeads)

/-- Ze80 Theorem 6.1(a): for every permitted ordering and every actual family of
segment socles, the product has an irreducible socle, unique as a subobject. -/
def OrderedMultisegmentSocleExistence : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{max uF uV, uF} n),
    d.IsPrecedenceOrdered → d.HasSegmentSocles →
      ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        d.IsZelevinskySocle π

/-- Ze80 Proposition 6.4: ordered products of segment socles for the same
multisegment are isomorphic, regardless of ordering or actual representatives. -/
def OrderedMultisegmentSocleProductIndependence : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d d' : T.SegmentProductDatum.{max uF uV, uF} n),
    d.IsPrecedenceOrdered → d'.IsPrecedenceOrdered →
      d.HasSegmentSocles → d'.HasSegmentSocles →
        d.multisegment = d'.multisegment → Nonempty (d.induced ≅ d'.induced)

/-- Ze80 Theorem 6.1(b): any irreducible subrepresentations of two permitted
products are isomorphic exactly when their multisegments agree. -/
def OrderedMultisegmentSocleClassification : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d d' : T.SegmentProductDatum.{max uF uV, uF} n)
    (π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    d.IsZelevinskySubrepresentation π → d'.IsZelevinskySubrepresentation π' →
      (d.multisegment = d'.multisegment ↔ Nonempty (π ≅ π'))

/-- Ze80 §6.5: a socle exists for every multisegment, with its prescribed degree. -/
def MultisegmentSocleExistence : Prop :=
  letI := T.topology
  ∀ a : T.Multisegment.{max uF uV, uF},
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a.degree F.Carrier),
      a.IsZelevinskySocle π

/-- Ze80 Theorem 6.1(c), §6.5: every irreducible smooth representation occurs.
The equality of degrees is asserted, not supplied as a hypothesis. -/
def MultisegmentSocleExhaustion : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    Representation.IsIrreducible π.representation →
      ∃ a : T.Multisegment.{max uF uV, uF}, a.degree = n ∧ a.IsZelevinskySocle π

/-- Ze80 §6.5: equality of multisegments is equivalent to isomorphism of their
socles. Together with existence and exhaustion this is the classification. -/
def MultisegmentSocleClassification : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (a b : T.Multisegment.{max uF uV, uF})
    (π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    a.IsZelevinskySocle π → b.IsZelevinskySocle π' →
      (a = b ↔ Nonempty (π ≅ π'))

/-- Rodier82 §4.3 Theorem 3(a): a nonprecedence-ordered product of special
segment heads has a unique irreducible quotient object. -/
def OrderedMultisegmentHeadExistence : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{max uF uV, uF} n),
    d.IsPrecedenceOrdered → d.HasSegmentHeads →
      ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        d.IsLanglandsHead π

/-- Rodier82 §4.3 Theorem 3(b): any irreducible quotients of permitted products
are isomorphic exactly when their multisegments agree. This includes independence
of ordering and all actual block representatives. -/
def OrderedMultisegmentHeadClassification : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d d' : T.SegmentProductDatum.{max uF uV, uF} n)
    (π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    d.IsLanglandsQuotient π → d'.IsLanglandsQuotient π' →
      (d.multisegment = d'.multisegment ↔ Nonempty (π ≅ π'))

/-- Rodier82 Theorem 3 with Ze80 §6.5's enumeration and §9.1's segment heads:
every multisegment has a Langlands head of the prescribed degree. -/
def MultisegmentHeadExistence : Prop :=
  letI := T.topology
  ∀ a : T.Multisegment.{max uF uV, uF},
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a.degree F.Carrier),
      a.IsLanglandsHead π

/-- Rodier82 §4.3 Theorem 3(c): every irreducible smooth representation is a
Langlands head for a multisegment of the same total degree. -/
def MultisegmentHeadExhaustion : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    Representation.IsIrreducible π.representation →
      ∃ a : T.Multisegment.{max uF uV, uF}, a.degree = n ∧ a.IsLanglandsHead π

/-- Rodier82 §4.3 Theorem 3(b), in multiset form: Langlands heads are isomorphic
exactly when their multisegments agree. -/
def MultisegmentHeadClassification : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (a b : T.Multisegment.{max uF uV, uF})
    (π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    a.IsLanglandsHead π → b.IsLanglandsHead π' →
      (a = b ↔ Nonempty (π ≅ π'))

/-- The two multisegment relations are invariant under an actual isomorphism
of the output representation. This is an intrinsic consequence of transporting
constituent intertwiners; it asserts no classification theorem. -/
def MultisegmentConstituentRepresentativeInvariance : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (a : T.Multisegment.{max uF uV, uF})
    (π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    Nonempty (π ≅ π') →
      (a.IsZelevinskySocle π ↔ a.IsZelevinskySocle π') ∧
        (a.IsLanglandsHead π ↔ a.IsLanglandsHead π')

/-- Henniart02 §2.8: for genuine essentially square-integrable block data with
weakly decreasing unitary exponents, an irreducible head exists. -/
def SquareIntegrableLanglandsHeadExistence : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ d : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n,
      ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        d.IsLanglandsHead π

/-- Henniart02 §2.8: any two irreducible quotients of a permitted special-block
product are isomorphic. -/
def SquareIntegrableLanglandsQuotientUniqueness : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ (d : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n)
      (π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      d.IsLanglandsQuotient π → d.IsLanglandsQuotient π' → Nonempty (π ≅ π')

/-- Henniart02 §2.8: every positive-rank irreducible smooth representation is
the Langlands head of genuine decreasing-exponent square-integrable block data. -/
def SquareIntegrableLanglandsExhaustion : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      Representation.IsIrreducible π.representation →
        ∃ d : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n,
          d.IsLanglandsHead π

/-- Henniart02 §2.8: two permitted special-block products have isomorphic
irreducible quotients iff the blocks match up to permutation and genuine
isomorphism. The rank equality transports a block to the same general linear
group; chosen forms and exponent witnesses are not part of the comparison. -/
def SquareIntegrableLanglandsClassification : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ (d d' : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n)
      (π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      d.IsLanglandsQuotient π → d'.IsLanglandsQuotient π' →
        (Nonempty (π ≅ π') ↔
          ∃ e : Fin d.shape.length ≃ Fin d'.shape.length,
            ∀ i, ∃ h : d.shape.size i = d'.shape.size (e i),
              Nonempty ((h ▸ d.blocks i) ≅ d'.blocks (e i)))

/-- The core socle, special-head and special-block quotient classifications.
Twist/dual/central-character compatibility and product irreducibility are
separate statement units. -/
def MultisegmentClassificationTheorems : Prop :=
  MultisegmentNonprecedenceEnumeration.{uF, uV} F T ∧
    MultisegmentConstituentDataExistence.{uF, uV} F T ∧
    OrderedMultisegmentSocleExistence.{uF, uV} F T ∧
    OrderedMultisegmentSocleProductIndependence.{uF, uV} F T ∧
    OrderedMultisegmentSocleClassification.{uF, uV} F T ∧
    MultisegmentSocleExistence.{uF, uV} F T ∧
    MultisegmentSocleExhaustion.{uF, uV} F T ∧
    MultisegmentSocleClassification.{uF, uV} F T ∧
    OrderedMultisegmentHeadExistence.{uF, uV} F T ∧
    OrderedMultisegmentHeadClassification.{uF, uV} F T ∧
    MultisegmentHeadExistence.{uF, uV} F T ∧
    MultisegmentHeadExhaustion.{uF, uV} F T ∧
    MultisegmentHeadClassification.{uF, uV} F T ∧
    MultisegmentConstituentRepresentativeInvariance.{uF, uV} F T ∧
    SquareIntegrableLanglandsHeadExistence.{uF, uV} F T ∧
    SquareIntegrableLanglandsQuotientUniqueness.{uF, uV} F T ∧
    SquareIntegrableLanglandsExhaustion.{uF, uV} F T ∧
    SquareIntegrableLanglandsClassification.{uF, uV} F T

/-- The core classification statements for every prime, finite p-adic extension
and compatible topological realization. -/
def PadicMultisegmentClassificationTheorems : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    MultisegmentClassificationTheorems.{uF, uV} F T

end Langlands.Classification
