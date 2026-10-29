# Derivatives of cuspidal representations, segment socles and their products

Authors: Worker 758 (initial draft) and Worker 508 (source verification and
submission), for task 8e5b4563-0365-41c7-b134-70f2a0b36292.

This pair states five propositions and imports the separate cuspidal
statement, together giving six propositions about the Bernstein–Zelevinsky
derivatives `Derivative.generalLinearDerivative T ψ N k hk` from the published
module `Langlands.Representation.Derivative.Iteration` (task
d3e94f0f-56d3-4a0f-ac7d-473214ea8038). **None of the six is proved here.**
Each is a `Prop`-valued `def` in namespace `Langlands.Classification`.
`SupercuspidalDerivatives` is defined in the paired lower module
`Langlands.Representation.Classification.SupercuspidalDerivativesStatement`,
so its eventual proof can avoid all segment-socle imports. The other five
are defined in this module. The proofs are separate successor tasks.

## Sources

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)* (1980),
  `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  Printed page = zero-based PDF index + 164. Used: §3.5 (p.182),
  §4.1–4.3 (p.184), §4.4–4.5 (p.185) and the proof of Theorem 4.2 (p.184).
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
  reductive p-adic groups I* (1977), `bernstein-zelevinsky-1977-induced-i`,
  SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  Printed page = zero-based PDF index + 440. Used: §3.5 (p.452), §4.3–4.4
  (p.454), Lemma 4.5, Corollary 4.6 and Lemma 4.7 (p.455).

No errata entry for either source is registered in the project literature
index or the public notes.

## Parameters and conventions

Every proposition has the telescope
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)` and
installs `letI := T.topology`; no canonical topology is substituted.

- **Universes.** (a) is `SupercuspidalDerivatives.{uF, uW}`, with its own
  carrier universe `uW`. (b)–(f) have universe parameters `.{uF, uV}`: `uV` is
  the universe of segment bases, and the carriers are in `Type (max uF uV)`,
  which `SegmentProductDatum`, `IsSegmentSocle` and `IsSupercuspidalSupport`
  require. The functor is applied at that carrier universe:
  `Derivative.generalLinearDerivative.{uF, uW}` in (a) and
  `Derivative.generalLinearDerivative.{uF, max uF uV}` in (b)–(f).
- **Notation.** Below, `D ψ N k hk` abbreviates
  `Derivative.generalLinearDerivative T ψ N k hk : SmoothRep ℂ (GL_N) ⥤ SmoothRep ℂ (GL_(N-k))`.
  For `k ≥ 1` it is `Ψ⁻ ∘ (Φ⁻)^(k-1)` after restriction to the mirabolic
  subgroup, as in BZ77 §3.5 and §4.3; for `k = 0` it is the identity.
- **Every `ψ`.** Each proposition is quantified over every
  `ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`
  (continuous and nontrivial). None assumes that such a `ψ` exists. That is
  `HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement` (task
  748faef5-6f7d-46d3-bb39-60e91bd997d7).
- **Explicit orders.** Derivative orders are explicit natural numbers. No
  level or highest-derivative predicate is introduced. Order bounds `hk : k ≤ N`
  enter as universally quantified hypotheses, never as embedded proof terms,
  except `le_rfl` for the top derivative in (a).
- **Zero and nonzero.** A derivative vanishes when
  `Subsingleton ((D ψ N k hk).obj X)` and is nonzero when
  `Nontrivial ((D ψ N k hk).obj X)`. Both use the carrier coercion of
  `SmoothRep`.
- **`λ`.** For a datum `d : T.SegmentProductDatum n`,
  `λ = ∑ i, (d.segments i).rank`. In Ze80 4.2–4.5 notation this is `∑ m_i`,
  where `Δ_i = [ρ_i, ρ_i']` with `ρ_i ∈ Irr G_(m_i)`. In (d)–(f) the order is
  a free index `k` with hypotheses `hk : k ≤ n` and `k = ∑ i, (d.segments i).rank`.
  Both are always satisfiable (`k ≤ n` follows from `d.degree_sum`, since every
  length is positive). A consumer can therefore apply the statements to two
  data whose `λ` agree only propositionally, at one functor index. Worker 219
  asked for this form (peer message c95afb3218e156a38ad9f3eb0754d6e6).
- **`Δ⁻`.** For `Δ = [ρ, ν^(m-1) ρ]` with `m = Δ.length ≥ 2`, Zelevinsky's
  `Δ⁻ = [ρ, ν^(m-2) ρ]` keeps the beginning `Δ.base` and drops the end. It is
  written `⟨Δ.base, Δ.length - 1, _⟩`. The proof field establishes that the
  shortened length is positive. The inline constructor needs no truncation
  helper or extra import.

## Normalization

The functors are composites of the published determinant-normalized
`Mirabolic.psiMinus` and `Mirabolic.phiMinus`
(`Langlands.Representation.Derivative.MirabolicMinus`). They twist the
unnormalized coinvariant functors by `|det|^(-1/2)` of the output group. The
source normalizes by `mod_U^(-1/2)` (BZ77 §1.8(b), §3.2), where `mod_U(m)` is
the module of `u ↦ m u m⁻¹` on the unipotent radical `U ≅ F^(n-1)` of the
mirabolic subgroup. For `m ∈ GL_(n-1)` this module is `|det m|`. So the
Library convention is the source convention once that Haar-modulus equality
is known. The comparison is the separate statement task
a622f240-4846-4086-b34f-f650ba636ee4, with proof task
f947a735-872d-44db-a9ea-954d17dec4bd. The six statements are about the
Library functors as published. Their proofs must use that comparison, or work
directly with `|det|`, wherever a source argument uses `mod_U`.

The source assertion `⟨Δ⟩^(m) ≅ ⟨Δ⁻⟩` of Ze80 3.5, with `Δ⁻` keeping the
beginning, has the right direction for this normalization. Take the rank-1
case `ρ = χ` a character of `GL_1`. Then `⟨[χ, ν^(m-1) χ]⟩` is the
irreducible subrepresentation of `χ × νχ × ⋯ × ν^(m-1) χ`, which is the
character `χ ν^((m-1)/2) ∘ det` of `GL_m`. (For `m = 2`, the trivial character
lies in the normalized induction `ν^(-1/2) × ν^(1/2)`.) Its first derivative
is `Ψ⁻` of the restriction to the mirabolic subgroup: the coinvariants under
`U` are the same character on the Levi `GL_(m-1)`, twisted by `|det|^(-1/2)`.
This gives `χ ν^((m-2)/2) ∘ det = ⟨[χ, ν^(m-2) χ]⟩`, the segment with the
same beginning and one position fewer.

## The six statements

### (a) `SupercuspidalDerivatives.{uF, uW}` — BZ77 §4.4

For every `ψ`, `n` and `A : SmoothRep.{0, uF, uW} ℂ (GL_(n+1))` that is
irreducible (`A.IsIrreducible`) and supercuspidal
(`GeneralLinear.IsSupercuspidal A.representation`):

1. for every `k` with `0 < k < n + 1`, `(D ψ (n+1) k hk).obj A` is
   `Subsingleton`;
2. `Module.finrank ℂ ((D ψ (n+1) (n+1) le_rfl).obj A) = 1`.

Source: BZ77 §4.4, p.454: for an irreducible cuspidal `ρ` of `G_n`, the
derivatives `ρ^(k)` vanish for `0 < k < n` and `ρ^(n)` is the
one-dimensional representation of `G_0`. The source cites Gelfand–Kazhdan
for the restriction to the mirabolic subgroup and for uniqueness of Whittaker
models. The rank is written `n + 1` so that it is positive. The case `k = 0`
is excluded because `D ψ N 0 _` is the identity.

### (b) `SegmentSocleDerivatives.{uF, uV}` — Ze80 Theorem 3.5

For every `ψ`, segment `Δ` and `π : SmoothRep ℂ (GL_(Δ.degree))` with
`T.IsSegmentSocle Δ π` (that is, `π ≅ ⟨Δ⟩`):

1. for every `k ≤ Δ.degree` with `0 < k` and `k ≠ Δ.rank`, the derivative
   `(D ψ Δ.degree k hk).obj π` is `Subsingleton`;
2. if `Δ.length = 1`, then `Module.finrank ℂ ((D ψ Δ.degree Δ.rank hm).obj π) = 1`;
3. if `2 ≤ Δ.length`, then for every `hdeg : Δ.degree - Δ.rank = (Δ.length - 1) * Δ.rank`,
   `T.IsSegmentSocle ⟨Δ.base, Δ.length - 1, _⟩ (T.castRank hdeg ((D ψ Δ.degree Δ.rank hm).obj π))`.

Source: Ze80 Theorem 3.5, p.182: for `Δ = [ρ, ρ']` with `ρ ∈ Irr G_m`,
`⟨Δ⟩^(k) = 0` unless `k = 0` or `k = m`, and `⟨Δ⟩^(m) = ⟨Δ⁻⟩`. Here
`m = Δ.rank`. Conjunct 2 is the source's case `Δ⁻ = ∅`: the derivative is
the one-dimensional representation `⟨∅⟩` of `G_0`. Conjunct 3 is the
nonempty case. The derivative lives on `GL_(Δ.degree - Δ.rank)`, and
`⟨Δ⁻⟩` on `GL((Δ.length - 1) * Δ.rank)`, the degree of `Δ⁻` by definition. The
published exact rank transport `T.castRank` (`Classification.SingletonSegmentSocle`)
moves it along the equality `hdeg`. That equality always holds, so taking it
as a hypothesis loses nothing.

### (c) `HighestDerivativeSupportShift.{uF, uV}` — Ze80 4.4(d), from BZ77 Lemma 4.7(b)

For every `ψ`, `n`, `ω : SmoothRep ℂ (GL_n)`, `k ≤ n` with `ω` irreducible,
`(D ψ n k hk).obj ω` nontrivial and every derivative of order `j > k`
`Subsingleton` (so `k` is the highest order with a nonzero derivative), and
every `σ : SmoothRep ℂ (GL_(n-k))` that is an irreducible subrepresentation of
`(D ψ n k hk).obj ω` (`IsIrreducibleSubrepresentation`, which allows an
injective intertwiner up to isomorphism): if `s` and `s'` are supercuspidal
supports of `ω` and `σ` (`T.IsSupercuspidalSupport`), then
`s'.map (CuspidalDatum.twist 1) ≤ s` as multisets.

Source: Ze80 4.4(d), p.185, deduced from BZ77 Lemma 4.7(b), p.455.
The rendered original states `νφ_ω − φ_σ ≥ 0` and defines
`(νφ)(ρ) = φ(νρ)`, where `φ_ω` is the multiplicity function of `supp ω`.
Thus `φ_σ(ρ) ≤ φ_ω(νρ)` for every cuspidal `ρ`. Equivalently,
`ν · supp σ ⊆ supp ω` as multisets. The twist is a bijection on cuspidal
classes, and `CuspidalDatum.twist 1` is `ρ ↦ νρ` with `ν = |det|`
(`Classification.Segments`). This is precisely the Lean conclusion. Reading
the inequality and the shift definition together resolves the text-layer
ambiguity without changing the printed formula.

**Direction check.** Take `ω = ⟨Δ⟩` with `Δ = [ρ, ν^(m-1) ρ]` and `m ≥ 2`.
Its highest derivative is `σ = ⟨Δ⁻⟩` by (b), and
`supp σ = {ρ, …, ν^(m-2) ρ}`. Hence
`ν · supp σ = {νρ, …, ν^(m-1) ρ} ⊆ supp ω`. This agrees with the printed
formula and BZ77 Lemma 4.7(b). It also matches the use of 4.4(d) in Ze80 4.5:
an end of an underived segment, shifted by `ν`, must be a beginning of
another segment, producing juxtaposition.

### (d) `NonjuxtaposedSegmentSocleConstituentLevel.{uF, uV}` — Ze80 Proposition 4.3

For every `ψ`, `n` and `d : T.SegmentProductDatum n` with
`d.HasSegmentSocles` (each block `π_i` is `⟨Δ_i⟩`), no two segments at
different positions juxtaposed (`Segment.IsJuxtaposed`), every `k` with
`hk : k ≤ n` and `k = λ`, and every irreducible subquotient `ω` of
`d.induced` (`SmoothRep.IsSubquotient`): `(D ψ n k hk).obj ω` is nontrivial,
and every derivative of `ω` of order `j > k` is `Subsingleton`.

Source: Ze80 Proposition 4.3, p.184: if `Δ_i` and `Δ_j` are not juxtaposed
for any `i, j`, every irreducible subquotient `ω` of `π = ⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩`
has `λ(ω) = λ(π) = ∑ m_i`. A segment is never juxtaposed with itself, so
restricting to `i ≠ j` matches the source's "for any `i, j`". Repeated equal
segments at different positions are allowed. `d.induced` is the published
upper normalized induction with right translation, in the order of
`d.segments`.

### (e) `NonjuxtaposedSegmentSocleDerivativeStrictMono.{uF, uV}` — lattice form of Ze80 Proposition 4.3

Same hypotheses on `ψ`, `n`, `d` and `k` as in (d). For all subrepresentations
`K₁ < K₂` of `d.induced.representation`,
`range (D(ι₁)) < range (D(ι₂))` as Mathlib subrepresentations of
`((D ψ n k hk).obj d.induced).representation`, where
`ιⱼ = SmoothRep.subtype d.induced Kⱼ` is the inclusion and
`D(ιⱼ) = (D ψ n k hk).map ιⱼ`, read through `SmoothRep.hom`.

Source: this is how Proposition 4.3 is used in the proof of Theorem 4.2
(p.184) and in Proposition 4.6 (step (3), pp.185–186). By exactness of
derivatives (BZ77 3.2, 3.5), the order-`λ` derivative takes the inclusion
`K₁ ⊂ K₂` to an inclusion, and `K₂/K₁ ≠ 0` has an irreducible subquotient,
whose order-`λ` derivative is nonzero by (d); so the inclusion of derivatives
is strict. The Library has no inclusion morphism between two
subrepresentations, so the statement compares the images of the two
inclusions into `d.induced`. These images are the derivatives of `K₁` and `K₂`
seen inside the derivative of `d.induced` (by exactness). This explanation is
the intended proof route, not part of the statement.

### (f) `SegmentSocleProductHighestDerivative.{uF, uV}` — Ze80 Theorem 3.5 with BZ77 Corollary 4.6

For every `ψ`, `n`, `d` with `d.HasSegmentSocles` (no non-juxtaposition
hypothesis), and every `k` with `hk : k ≤ n` and `k = λ`:

1. every derivative of `d.induced` of order `j > k` is `Subsingleton`;
2. there is `d' : T.SegmentProductDatum (n - k)` whose segment list
   `List.ofFn d'.segments` is the list of `Δ_i⁻ = ⟨Δ_i.base, Δ_i.length - 1, _⟩`
   for the `i` with `2 ≤ Δ_i.length`, in the original order, with
   `d'.HasSegmentSocles` and an isomorphism
   `(D ψ n k hk).obj d.induced ≅ d'.induced` in the category of smooth
   representations;
3. if every segment has length 1, `Module.finrank ℂ ((D ψ n k hk).obj d.induced) = 1`.

Source: the proof of Ze80 Theorem 4.2, p.184, uses that the highest
derivative of `⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` is `⟨Δ_1⁻⟩ × ⋯ × ⟨Δ_r⁻⟩`. This follows from
Theorem 3.5 and the Leibniz rule (BZ77 Lemma 4.5 / Corollary 4.6, p.455): the
order-`λ` derivative of a product has a filtration whose quotients are
products of derivatives of the factors with orders summing to `λ`, and only
one of these, the product of the top derivatives, is nonzero. The
isomorphism is a genuine isomorphism, not an equality of constituents.
Factors with `Δ_i⁻ = ∅` are omitted, because `⟨∅⟩` is the unit for the
product. Conjunct 3 covers the case where all `Δ_i⁻` are empty. There the
derivative lives on `GL_0`, and a consumer needs no fact about the empty
product.

## Status

All six propositions are unproved by this contribution. They are inputs to
the proof 23e98d90-6055-4e35-91a9-b0f5d8a84961 of
`UnlinkedSegmentSocleProductIrreducible` (which uses (e) and (f)) and to the
proof a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9 of
`LinkedSegmentSocleReverseProductStructure` (step (3), using (d)–(f)).

## Imports and independence

Direct imports: the lower
`Langlands.Representation.Classification.SupercuspidalDerivativesStatement`,
`Langlands.Representation.Classification.LanglandsData`,
`Langlands.Representation.Classification.SupercuspidalSupport`,
`Langlands.Representation.Classification.SingletonSegmentSocle`,
`Langlands.Representation.Derivative.Iteration` and
`Langlands.HarmonicAnalysis.Basic`. Their module-level transitive closure
within `Langlands`, at Library commit
`9f141aa49982eab63f32f392c4c63dcb83837a19`, has 110 modules. It contains no
module that states or proves `UnlinkedSegmentSocleProductIrreducible`,
`LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`,
`SegmentSocleProductIrreducibility`, `JuxtaposedSegmentSocleReverseProductStructure`,
`LinkedSegmentSocleReverseProductQuotientHom`, `AdjacentUnlinkedSegmentSocleSwap`,
`TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing`,
`GenericSegmentProductUniqueness` or `SegmentHeadProductIrreducibility`.
It contains three statement modules, `MultisegmentClassificationStatement`,
`OrderedSegmentSquareIntegrableConversionStatement` and
`TemperedBlockStatement`. They are reached through `SingletonSegmentSocle`. They only
define propositions, including `OrderedMultisegmentSocleExistence` and
`SquareIntegrableLanglandsClassification`, and prove none of them. No
excluded conclusion is used.

The lower cuspidal module imports only `Classification.Supercuspidal`,
`Derivative.Iteration` and `HarmonicAnalysis.Basic`. Its transitive
`Langlands` import closure at that base has 57 modules and contains no
segment-socle statement or segment classification conclusion. The six
proposition bodies are unchanged from the initial draft; only (a)'s module
location was separated for upstream BZ77 consumers. This is a statement
import audit, not a claim that any derivative theorem is proved.
