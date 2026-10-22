import Langlands.Representation.Classification.Segments
import Langlands.Representation.Classification.Tempered

/-!
# Langlands data for `GL_n` over a p-adic field

Three forms of the data of the Langlands classification, with the induced
representations they determine: tempered blocks with strictly decreasing real
exponents, essentially square-integrable blocks with decreasing exponents, and
precedence-ordered families of segments. The Langlands quotient and Zelevinsky's
subrepresentation are recorded only by relations: neither existence nor
uniqueness of an irreducible quotient or subrepresentation is assumed.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uV uF

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

section Twisted

variable {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The block family `(ν^(u_1) σ_1, …, ν^(u_r) σ_r)`, with `ν = |det|`. -/
def twistedBlocks
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (u : Fin B.length → ℝ) :
    letI := T.topology
    ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
  fun i => T.segmentFactor (σ i) (u i)

/-- `i(ν^(u_1) σ_1, …, ν^(u_r) σ_r)`: normalized parabolic induction from the
standard upper block parabolic of `B` of the twisted block family. -/
def twistedProductInduced
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (u : Fin B.length → ℝ) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor B).obj (T.twistedBlocks B σ u)

theorem twistedProductInduced_representation
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (u : Fin B.length → ℝ) :
    letI := T.topology
    (T.twistedProductInduced B σ u).representation =
      T.normalizedProductInduced B (fun i => (T.twistedBlocks B σ u i).representation) :=
  rfl

/-- Isomorphic block families induce isomorphic representations. -/
def twistedProductInducedIso
    {σ σ' : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    (e : ∀ i, σ i ≅ σ' i) (u : Fin B.length → ℝ) :
    T.twistedProductInduced B σ u ≅ T.twistedProductInduced B σ' u :=
  letI := T.topology
  (T.normalizedProductInductionFunctor B).mapIso
    (Pi.isoMk fun i => SmoothRep.twistIso _
      (T.isOpen_ker_determinantPowerCharacter (B.size i) (u i)) (e i))

end Twisted

/-- Langlands data in tempered form on `GL_n(F)`: an ordered block shape
`(n_1, …, n_r)`, irreducible tempered representations `π_i` of `GL_(n_i)(F)`, and
real exponents `u_1 > ⋯ > u_r`. -/
structure TemperedLanglandsDatum (n : ℕ) where
  /-- The ordered block shape `(n_1, …, n_r)` of `n`. -/
  shape : GeneralLinear.BlockShape n
  /-- The tempered blocks `π_i`. -/
  blocks : letI := T.topology
    ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (shape.size i) F.Carrier)
  irreducible : ∀ i, letI := T.topology
    Representation.IsIrreducible (blocks i).representation
  tempered : ∀ i, letI := T.topology
    T.IsTempered (blocks i).representation
  /-- The real exponents `u_i`. -/
  exponent : Fin shape.length → ℝ
  strictAnti : StrictAnti exponent

namespace TemperedLanglandsDatum

variable {T} {n : ℕ} (d : TemperedLanglandsDatum.{uV, uF} T n)

/-- The standard module `i(ν^(u_1) π_1, …, ν^(u_r) π_r)`. -/
def standardModule :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  T.twistedProductInduced d.shape d.blocks d.exponent

theorem standardModule_representation :
    letI := T.topology
    d.standardModule.representation =
      T.normalizedProductInduced d.shape
        (fun i => (T.twistedBlocks d.shape d.blocks d.exponent i).representation) :=
  rfl

/-- `π` is an irreducible quotient of the standard module. This is the relation
satisfied by the Langlands quotient; it asserts neither existence nor
uniqueness. -/
def IsLanglandsQuotient
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  Classification.IsIrreducibleQuotient d.standardModule.representation π.representation

/-- `π` is the irreducible head of the standard module: every irreducible quotient
map has the kernel of the given one. -/
def IsLanglandsHead
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  Classification.IsIrreducibleHead d.standardModule.representation π.representation

theorem IsLanglandsHead.isLanglandsQuotient
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsLanglandsHead π) : d.IsLanglandsQuotient π := by
  obtain ⟨hπ, q, hq, -⟩ := h
  exact ⟨hπ, q, hq⟩

end TemperedLanglandsDatum

/-- Langlands data in essentially square-integrable form on `GL_n(F)`: an ordered
block shape, irreducible essentially square-integrable representations `π_i`,
each with a real exponent `α(π_i)` for which `ν^(-α(π_i)) π_i` carries an invariant
positive definite form, and `α(π_1) ≥ ⋯ ≥ α(π_r)`. -/
structure SquareIntegrableLanglandsDatum (n : ℕ) where
  /-- The ordered block shape `(n_1, …, n_r)` of `n`. -/
  shape : GeneralLinear.BlockShape n
  /-- The essentially square-integrable blocks `π_i`. -/
  blocks : letI := T.topology
    ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (shape.size i) F.Carrier)
  irreducible : ∀ i, letI := T.topology
    Representation.IsIrreducible (blocks i).representation
  essentiallySquareIntegrable : ∀ i, letI := T.topology
    T.IsEssentiallySquareIntegrable (blocks i).representation
  /-- The exponent `α(π_i)` with the unitary structure of `ν^(-α(π_i)) π_i`. -/
  unitaryExponent : ∀ i, letI := T.topology
    UnitaryExponentData (T.determinantNorm (shape.size i)) (blocks i).representation
  antitone : Antitone fun i => (unitaryExponent i).exponent

namespace SquareIntegrableLanglandsDatum

variable {T} {n : ℕ} (d : SquareIntegrableLanglandsDatum.{uV, uF} T n)

/-- The exponents `α(π_i)`. -/
def exponent (i : Fin d.shape.length) : ℝ := (d.unitaryExponent i).exponent

/-- The induced representation `i(π_1, …, π_r)`. -/
def induced :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor d.shape).obj d.blocks

theorem induced_representation :
    letI := T.topology
    d.induced.representation =
      T.normalizedProductInduced d.shape (fun i => (d.blocks i).representation) :=
  rfl

/-- `π` is an irreducible quotient of `i(π_1, …, π_r)`. -/
def IsLanglandsQuotient
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  Classification.IsIrreducibleQuotient d.induced.representation π.representation

/-- `π` is the irreducible head of `i(π_1, …, π_r)`, Henniart's `J(π_1, …, π_r)`. -/
def IsLanglandsHead
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  Classification.IsIrreducibleHead d.induced.representation π.representation

theorem IsLanglandsHead.isLanglandsQuotient
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsLanglandsHead π) : d.IsLanglandsQuotient π := by
  obtain ⟨hπ, q, hq, -⟩ := h
  exact ⟨hπ, q, hq⟩

end SquareIntegrableLanglandsDatum

/-- The ordered block shape `(deg Δ_1, …, deg Δ_r)` of a finite family of segments,
for any `n` equal to the sum of the degrees. -/
def segmentShape {r : ℕ} (Δ : Fin r → Segment.{uV, uF} T) {n : ℕ}
    (h : ∑ i, (Δ i).degree = n) : GeneralLinear.BlockShape n where
  length := r
  size i := (Δ i).degree
  positive i := (Δ i).degree_pos
  sum_eq := h

@[simp]
theorem segmentShape_length {r : ℕ} (Δ : Fin r → Segment.{uV, uF} T) {n : ℕ}
    (h : ∑ i, (Δ i).degree = n) : (T.segmentShape Δ h).length = r := rfl

@[simp]
theorem segmentShape_size {r : ℕ} (Δ : Fin r → Segment.{uV, uF} T) {n : ℕ}
    (h : ∑ i, (Δ i).degree = n) (i : Fin r) : (T.segmentShape Δ h).size i = (Δ i).degree :=
  rfl

/-- A finite family of segments `Δ_1, …, Δ_r` whose degrees add up to `n`, together
with representations `π_i` of `GL_(deg Δ_i)(F)`, the candidates for the special
constituents attached to the segments. -/
structure SegmentProductDatum (n : ℕ) where
  /-- The number `r` of segments. -/
  length : ℕ
  /-- The segments `Δ_1, …, Δ_r`, in order. -/
  segments : Fin length → Segment.{uV, uF} T
  degree_sum : ∑ i, (segments i).degree = n
  /-- The representations `π_i` of `GL_(deg Δ_i)(F)`. -/
  blocks : letI := T.topology
    ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (segments i).degree F.Carrier)

namespace SegmentProductDatum

variable {T} {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n)

/-- The block shape `(deg Δ_1, …, deg Δ_r)`. -/
def shape : GeneralLinear.BlockShape n := T.segmentShape d.segments d.degree_sum

/-- The multisegment `{Δ_1, …, Δ_r}`. -/
def multisegment : Multisegment.{uV, uF} T :=
  (List.ofFn d.segments : Multiset (Segment.{uV, uF} T))

theorem multisegment_isOrdering : d.multisegment.IsOrdering d.segments := rfl

/-- The induced representation `i(π_1, …, π_r)` on `GL_n(F)`. -/
def induced :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor d.shape).obj d.blocks

theorem induced_representation :
    letI := T.topology
    d.induced.representation =
      T.normalizedProductInduced d.shape (fun i => (d.blocks i).representation) :=
  rfl

/-- No earlier segment precedes a later one. -/
def IsPrecedenceOrdered : Prop := T.IsPrecedenceOrdered d.segments

/-- Each `π_i` is the irreducible head of the induced representation of its
segment: the relation satisfied by `St(Δ_i)`, Kudla's `Q(Δ_i)`. -/
def HasSegmentHeads : Prop := ∀ i, T.IsSegmentHead (d.segments i) (d.blocks i)

/-- Each `π_i` is the irreducible socle of the induced representation of its
segment: the relation satisfied by Zelevinsky's `⟨Δ_i⟩`. -/
def HasSegmentSocles : Prop := ∀ i, T.IsSegmentSocle (d.segments i) (d.blocks i)

/-- The segment form of the Langlands quotient: the family is precedence-ordered,
each `π_i` is the head of its segment, and `π` is an irreducible quotient of
`i(π_1, …, π_r)`. -/
def IsLanglandsQuotient
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  d.IsPrecedenceOrdered ∧ d.HasSegmentHeads ∧
    Classification.IsIrreducibleQuotient d.induced.representation π.representation

/-- The head form of `IsLanglandsQuotient`. -/
def IsLanglandsHead
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  d.IsPrecedenceOrdered ∧ d.HasSegmentHeads ∧
    Classification.IsIrreducibleHead d.induced.representation π.representation

/-- Zelevinsky's form: the family is precedence-ordered, each `π_i` is the socle of
its segment, and `π` is an irreducible subrepresentation of `i(π_1, …, π_r)`. -/
def IsZelevinskySubrepresentation
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  d.IsPrecedenceOrdered ∧ d.HasSegmentSocles ∧
    Classification.IsIrreducibleSubrepresentation d.induced.representation π.representation

/-- The socle form of `IsZelevinskySubrepresentation`. -/
def IsZelevinskySocle
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  d.IsPrecedenceOrdered ∧ d.HasSegmentSocles ∧
    Classification.IsIrreducibleSocle d.induced.representation π.representation

theorem IsLanglandsHead.isLanglandsQuotient
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsLanglandsHead π) : d.IsLanglandsQuotient π := by
  obtain ⟨ho, hh, hπ, q, hq, -⟩ := h
  exact ⟨ho, hh, hπ, q, hq⟩

theorem IsZelevinskySocle.isZelevinskySubrepresentation
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsZelevinskySocle π) : d.IsZelevinskySubrepresentation π := by
  obtain ⟨ho, hs, hπ, j, hj, -⟩ := h
  exact ⟨ho, hs, hπ, j, hj⟩

end SegmentProductDatum

variable {T}

/-- `π` is a Langlands quotient attached to the multisegment `a`: for some
precedence-ordered ordering of `a` and heads `π_i` of its segments, `π` is the
irreducible head of `i(π_1, …, π_r)`. Independence of the ordering is not
asserted. -/
def Multisegment.IsLanglandsHead {n : ℕ} (a : Multisegment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  ∃ d : SegmentProductDatum.{uV, uF} T n, d.multisegment = a ∧ d.IsLanglandsHead π

/-- `π` is Zelevinsky's representation attached to the multisegment `a`: for some
precedence-ordered ordering of `a` and socles `π_i` of its segments, `π` is the
irreducible socle of `i(π_1, …, π_r)`. Independence of the ordering is not
asserted. -/
def Multisegment.IsZelevinskySocle {n : ℕ} (a : Multisegment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  ∃ d : SegmentProductDatum.{uV, uF} T n, d.multisegment = a ∧ d.IsZelevinskySocle π

end PadicField.TopologicalData

end Langlands
