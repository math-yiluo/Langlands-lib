# Cuspidal Jacquet modules of a product of two segment socles on one line

Authors: Worker 1032 and Worker 999.

Lean module: `Langlands.Representation.Classification.TwoSegmentSocleShuffleJacquetStatement`.

## Declarations

- `Langlands.Classification.shuffleExponent S a₀ a₁ i` (internal definition). For
  `S : Finset (Fin m)` it is the exponent at position `i` of the shuffle of the
  two increasing runs `a₀, a₀ + 1, …` and `a₁, a₁ + 1, …` in which the positions of
  `S` carry the first run. Explicitly, `i ∈ S` gets `a₀ + #{j ∈ S | j < i}` and
  `i ∉ S` gets `a₁ + #{j ∉ S | j < i}`.
- `Langlands.Classification.shuffleFactors F T A m hr S a₀ a₁` (internal
  definition). These are the block factors `i ↦ T.segmentFactor A (shuffleExponent S a₀ a₁ i)`,
  that is `ν^(e_S(i)) A = A ⊗ |det|^(e_S(i))`, of the uniform shape
  `BlockShape.uniform m r hr`.
- `Langlands.Classification.TwoSegmentSocleShuffleJacquet.{uF,uV,uW} F T`
  (proposition definition, not proved here).

## Statement

Fix a prime `p`, a p-adic field `F` and compatible topological data `T`. Take
the following data:

- a cuspidal datum `ρ` of rank `r = ρ.rank`, with an actual supercuspidal
  representative `A` (`ρ.IsRepresentedBy A`);
- reals `a₀, a₁` and naturals `m₀, m₁`;
- a datum `d : T.SegmentProductDatum ((m₀ + m₁) * r)` with `d.length = 2` and
  `d.HasSegmentSocles`, whose segments satisfy:
  - `Δ₀ = d.segments 0` has beginning `ρ.twist a₀` and length `m₀`;
  - `Δ₁ = d.segments 1` has beginning `ρ.twist a₁` and length `m₁`.

So `d.induced` is Zelevinsky's `⟨Δ₀⟩ × ⟨Δ₁⟩`: its two blocks, in this order, are
actual irreducible socles of the increasing segment inductions, and `d.induced` is
their normalized upper parabolic product. Let `C = BlockShape.uniform (m₀ + m₁) r`
and let `J = CuspidalJacquetMultiplicity.upperJacquet T C d.induced.obj`, the
actual normalized upper Jacquet module along `C`, a representation of the block
Levi `GL_r × ⋯ × GL_r` (`m₀ + m₁` factors). The statement asserts both of the
following:

1. `HasCompositionSeriesLength J ((m₀ + m₁).choose m₀)`.
2. For every irreducible representation `τ` of the Levi `C.Levi F.Carrier`, on
   a carrier in an arbitrary universe `uW`, and every `m : ℕ`,
   `HasJordanHolderMultiplicity J (Rep.of τ) m` holds if and only if `m` is the
   number of `S : Finset (Fin (m₀ + m₁))` such that `S.card = m₀` and the
   external tensor `externalSmoothObject (shuffleFactors F T A.obj (m₀ + m₁) ρ.rank_pos S a₀ a₁)`
   is equivalent to `τ`.

In words, the composition factors of `r_C(⟨Δ₀⟩ × ⟨Δ₁⟩)` are the shuffle tensors
`⊗ᵢ ν^(e_S(i)) A`, one for each of the `(m₀+m₁).choose m₀` shuffles. The
multiplicity of a given irreducible `τ` counts the shuffles whose tensor is
equivalent to `τ`, so equal tensors from different shuffles are counted
separately.

## Provenance

This is a derived specialization of published results. No single printed
statement has this form. The sources are Zelevinsky, *Induced representations of
reductive p-adic groups II* (Ann. Sci. ENS (4) 13, 1980), registered as
`zelevinsky-1980-induced-ii` (SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`), and
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(Ann. Sci. ENS (4) 10, 1977), registered as `bernstein-zelevinsky-1977-induced-i`
(SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`).
Page locators give the printed page and the zero-based PDF page index.

- Ze80 1.2 (printed p. 170, PDF index 6) is the geometric lemma, a particular case
  of BZ77 2.12 (printed p. 448, PDF index 8). It says that `r ∘ i` is glued from
  explicit pieces indexed by double cosets.
- Ze80 1.6 (printed pp. 171–172, PDF indices 7–8) gives the "coordinate form" of
  that lemma. Each piece is indexed by a nonnegative integer matrix `B(w)` with
  prescribed row and column sums. It is built from the Jacquet modules of the
  factors along the row partitions of `B(w)`, recombined by induction along the
  column partitions.
- Ze80 1.7 (printed pp. 172–173, PDF indices 8–9) packages these computations in
  the representation bialgebra. Its part (b) says that the comultiplication is a
  ring homomorphism, which "follows directly from 1.6". It is cited only as the
  condensed form of the same computation, not as a separate input.
- Ze80 3.1 (printed pp. 180–181, PDF indices 16–17) characterizes `⟨Δ⟩` for
  `Δ = [ρ, ν^(m-1) ρ]` by `r_{(r,…,r)}(⟨Δ⟩) = ρ ⊗ νρ ⊗ … ⊗ ν^(m-1) ρ`. It also
  identifies `⟨Δ⟩` as the unique irreducible submodule of `ρ × νρ × … × ν^(m-1) ρ`.
  The Library states this formula as `SegmentSubrepresentationFullJacquet`. The
  proof of Ze80 3.4 (printed p. 181, PDF index 17) uses that `⟨Δ⟩` has zero Jacquet
  module along a composition whose parts are not all multiples of `r`.

Combining these, the pieces of the geometric-lemma filtration of
`r_C(⟨Δ₀⟩ × ⟨Δ₁⟩)` correspond to matrices with two rows, of sums `m₀ r` and
`m₁ r`, and `m₀ + m₁` columns, each of sum `r`. A piece vanishes unless each row
partition consists of multiples of `r`, so each column has a single entry `r`. The
surviving matrices are the `(m₀+m₁).choose m₀` sets `S` of columns whose entry `r`
lies in the first row. The piece of `S` is the irreducible tensor
`⊗ᵢ ν^(e_S(i)) A`: the factors of `r(⟨Δ₀⟩)` fill the positions of `S` in their
original increasing order, and those of `r(⟨Δ₁⟩)` fill the other positions. The
twist exponents add, because a representative of `ρ.twist a` is `A ⊗ |det|^a` and
`segmentFactor (A ⊗ |det|^a) j ≅ A ⊗ |det|^(a+j)`.

The intended later proof uses two Library statements as inputs:
`Langlands.Geometric.PadicGeometricLemmaTheorem` (module
`Langlands.Representation.Geometric.GeometricLemmaStatement`) and
`Langlands.Classification.SegmentSubrepresentationFullJacquet` (module
`Langlands.Representation.Classification.SegmentFullJacquetStatement`). This
statement module neither imports nor restates them. It also neither uses nor
restates the general cuspidal-support count `GLCuspidalJacquetMultiplicityStatement`
of the imported module. That count concerns a cuspidal induction. This statement
concerns a product of two segment socles, which in general are not cuspidal.

## Scope

The statement keeps arbitrary primes, finite p-adic fields, the supplied
compatible topology, the actual upper normalized induction and Jacquet functor,
and arbitrary real exponents `a₀, a₁`. It allows repeated segments, equal
segments and linked segments, and it adds no linkage, genericity, distinctness or
finite-length premise. The universes `uF`, `uV`, `uW` are independent. Library
segments have positive length, so the hypotheses can hold only when `m₀` and
`m₁` are positive. For `m₀ = 0` or `m₁ = 0` the proposition holds vacuously.

## Dependencies and independence

The module imports only `Langlands.Representation.Classification.LanglandsData`,
`Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement` and
`Langlands.Representation.Tensor.Finite`. It uses only their definitions:
`SegmentProductDatum`, `HasSegmentSocles`, `induced`, `BlockShape.uniform`,
`segmentFactor`, `CuspidalDatum.twist`, `CuspidalJacquetMultiplicity.upperJacquet`,
`HasCompositionSeriesLength`, `HasJordanHolderMultiplicity` and
`FiniteTensor.externalSmoothObject`. It assumes no Library proposition. The module does not
use the segment-socle product structure results downstream of it, such as
`JuxtaposedSegmentSocleReverseProductStructure`,
`LinkedSegmentSocleReverseProductStructure`, `SegmentSocleProductIrreducibility` or
`SegmentHeadProductIrreducibility`. It also does not use derivatives.

## Development check

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` over Library
commit `c59c0940bd7d47ad634dc767445532ca1108111f` compiled the module with no errors
or warnings. Its inspection of `TwoSegmentSocleShuffleJacquet` reports a
`Prop`-valued definition with universe parameters `uF uV uW` and only the
standard axioms.
