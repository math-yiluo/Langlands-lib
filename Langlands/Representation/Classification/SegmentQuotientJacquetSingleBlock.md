# The whole-block case of weak segment Jacquet factorization

Authors: Worker 485 and Worker 964.

This internal helper module proves only the one-block case of the proposed
all-shape weak segment Jacquet factor assertion. It does not prove the
all-shape assertion or the parent norm formula. Its provenance is elementary
composition of published Jacquet, single-block, singleton tensor and
rank-transport maps; no literature result beyond those published maps is used.

Throughout, `p` is a prime, `F : PadicField.{uF} p`, `T : F.TopologicalData`,
`B : GeneralLinear.BlockShape n` is an actual block shape of total rank `n`,
and `hB : B.length = 1`. The Jacquet module `B.JacquetModule ρ` is the actual
coinvariant quotient of the restriction of `ρ` to the standard upper block
parabolic by its unipotent radical, and `B.jacquetMk ρ` is its quotient map.

## The quotient map as an equivalence

`T.singleBlockNormalizedJacquetEquiv B hB ρ` applies to any complex
representation `ρ` of `GL_n(F)` on a carrier in an independent universe `uV`.
Its source is `ρ.comp (B.leviEmbedding F.Carrier)`, the original action
restricted through the actual Levi embedding. Its target is the normalized
Jacquet module `T.normalizedJacquet B ρ`. Its linear map is exactly
`B.jacquetMk ρ`.

The intertwining law uses the published
`T.normalizedJacquet_mk_eq_inv_halfModulus`. That law says the Levi acts on a
class `B.jacquetMk ρ v` by the inverse half modulus times the class of the
embedded block-diagonal action. The published `T.singleBlock_leviHalfModulus`
says this half modulus is `1` for one block, so the normalization disappears.
Bijectivity combines the published
`B.jacquetMk_injective_of_length_le_one`, valid for at most one block, with
`B.jacquetMk_surjective`. No smoothness, nonzeroness, irreducibility,
admissibility or finite-length hypothesis is used.

## The transported singleton tensor

`T.singleBlockTransportedTensorEquiv B hB A` applies to a smooth object `A` of
`GL_n(F)`. For each block index `j`, the factor is `A` transported along
`(B.singleBlock_size hB j).symm`, an object of `GL_{B.size j}(F)`. The source
is the actual `B.blockTensor` of the representations of this family. The
target is `A.representation.comp (B.leviEmbedding F.Carrier)`.

At the unique index `i = B.singleBlockIndex hB`, the construction first applies
the published `B.singleBlockTensorEquiv`. That map identifies the singleton
tensor with the factor at `i`, acting through the coordinate `m ↦ m i`. It
then applies the inverse of the published
`FiniteTensor.rankCastRepresentationEquiv F T h A` with
`h = B.singleBlock_size hB i`, precomposed with the same coordinate map. That
inverse carries the transported action to `A` acting through the matrix
reindexing `e = GeneralLinear.reindex (finCongr h)`. The published
`B.singleBlockLeviEquiv_symm_coordinate` gives `e (m i) = B.leviEmbedding m`,
so the composite intertwines with the original action restricted to the
actual Levi embedding.

`T.singleBlockNormalizedJacquetTensorEquiv B hB A` is the inverse of the first
equivalence for `A.representation`, followed by the inverse of the second. It
runs from the actual normalized Jacquet module of `A` to the singleton external
tensor of the transported family.

## The weak-segment corollary

`segmentQuotientJacquetFactors_singleBlock`, under `letI := T.topology`, takes
any `Δ : T.Segment.{max uF uV, uF}` and any smooth `π` of
`GL_{Δ.degree}(F)` with carrier universe `max uF uV`. It assumes exactly the
supplied weak relation `T.IsSegmentQuotient Δ π`: `π` is an irreducible
quotient of the segment induction for some supercuspidal representative of
`Δ.base`. For each block shape `B` of total rank `Δ.degree` with one block, it
supplies the following data.

- A length function `k`.
- Segments `Γ`, with degree equalities `hdeg i : (Γ i).degree = B.size i`.
- Smooth objects `σ i` of `GL_{B.size i}(F)`.

It proves these clauses.

- Positivity `0 < k i`.
- The block sizes `B.size i = Δ.rank * k i`.
- The total `∑ i, k i = Δ.length`.
- The lengths `(Γ i).length = k i`.
- The descending interval base
  `(Γ i).base = Δ.member (Δ.length - (∑ j with j < i, k j) - k i)`.
- The weak relation `T.IsSegmentQuotient (Γ i) ((hdeg i).symm ▸ σ i)`.
- A representation equivalence from
  `T.normalizedJacquet B π.representation` to
  `B.blockTensor (fun i => (σ i).representation)`.

The proof takes `k i = Δ.length`, `Γ i = Δ`, and
`hdeg i = (B.singleBlock_size hB i).symm`. It takes `σ i` to be `π` transported
along the same equality to block rank `B.size i`. Positivity is
`Δ.length_pos`. The size clause rewrites `B.size i` to
`Δ.degree = Δ.length * Δ.rank` and commutes the product. The sum is a sum over
one index. For the base clause, every `j` equals the unique index, so no `j`
satisfies `j < i`. The prefix sum is therefore empty and the base identity
becomes `Δ.base = Δ.member 0`, the published `Segment.member_zero`. For the
weak clause, transporting `σ i` back along `hdeg i` cancels the forward
transport, by case analysis on the equality. The supplied hypothesis is then
used unchanged. The equivalence is `T.singleBlockNormalizedJacquetTensorEquiv`
for `π`. The supplied weak quotient is never strengthened to a head relation,
and no proper-block Jacquet calculation or constituent existence is assumed.

## Universes and scope

The three constructions keep the field universe `uF` and carrier universe `uV`
independent. The corollary also keeps both universe parameters independent. It
uses the carrier universe `max uF uV` that the weak segment relation requires.
All shapes in this module have exactly one block. Proper-block vanishing, the
proper two-block formula, all-shape transitivity, tensor Jacquet compatibility
and the weak-to-strong bridge remain separate obligations with their own
owners.

## Dependency audit

The module imports `Langlands.Representation.Classification.Segments`,
`Langlands.Representation.CuspidalSupport.MinimalJacquetProof` and
`Langlands.Representation.Parabolic.RegroupingFactorEquivalences`. Their
complete project import closure has 96 published modules, and all 96 imported
Lean/Markdown pairs are byte-identical to Library commit
`4021bb1d1ec99e65990e08addda3ade7caa73058`. Neither the Lean closure nor its
paired Markdown names any of the thirteen excluded tasks inherited from the
parent norm-formula task. These cover forward special square-integrability,
ordered conversion, square-integrable and regular exhaustion, both
classifications, tempered block uniqueness, multisegment exhaustion, ordered
strong-head existence, quotient coverage, segment-head product
irreducibility, generic segment-product uniqueness and Zelevinsky multisegment
socle exhaustion. The closure also does not name the named conclusions of those
tasks, such as `SegmentSpecialEssentialSquareIntegrability` or
`MultisegmentSocleExhaustion`. The proof uses no derivative formula,
Zelevinsky's section 9.3 analytic result, his section 9.17 conjecture or any
downstream classification. The all-shape factor statement owned by task
`15540667-d654-4bfa-b699-c20981ea964c` is not imported.

Development compilation in the approved environment returned zero
diagnostics. Inspection of all four declarations reported level parameters
`uF, uV` and only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. These checks are development evidence only; independent review
and Library publication are still required.
