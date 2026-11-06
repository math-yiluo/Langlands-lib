# Essentially square-integrable assembly images, assuming head classification

Worker 1429 proves Worker 1700's statement
`Langlands.Correspondence.AssemblySquareIntegrablePreimageStatement` under one
explicit hypothesis: the multisegment head classification
`Langlands.Classification.MultisegmentHeadClassification` (Rodier 1982, §4.3,
Theorem 3(b)) for the canonical topological data of `F`. This hypothesis is a
published statement that has not been proved. The module therefore proves an
implication. It does not prove the statement unconditionally.

## Declarations

| Declaration | Content |
| --- | --- |
| `PadicField.TopologicalData.SegmentProductDatum.singleton` | For a segment `Δ` and a representation `π` of `GL_(deg Δ)(F)`, the segment product datum of rank `deg Δ` with one segment `Δ` and block `π`. |
| `PadicField.TopologicalData.SegmentProductDatum.singleton_multisegment` | The multisegment of `singleton Δ π` is `{Δ}` (a `simp` lemma). |
| `PadicField.TopologicalData.Multisegment.isLanglandsHead_singleton` | If `π` is a segment head of `Δ` (`T.IsSegmentHead Δ π`), then `π` is a Langlands head of the one-segment multisegment `{Δ}` (`Multisegment.IsLanglandsHead`). Here `T` is arbitrary topological data on `F`. |
| `PadicField.TopologicalData.Multisegment.isLanglandsHead_singleton_of_degree_eq` | The same for a representation of `GL_k(F)`, given `h : Δ.degree = k`; the segment-head hypothesis is stated for the transport of `π` along `h`. |
| `Correspondence.isIrreducible_of_classOf_eq` | If the finite-representation class of a local Weil representation `B` equals the forgetful image `weilClassForget F σ` of an irreducible Weil class `σ` of dimension `d+1`, then `B.representation` is irreducible. |
| `Correspondence.assemblySquareIntegrablePreimage_of_headClassification` | `MultisegmentHeadClassification.{uF, uA} F F.canonicalTopologicalData → AssemblySquareIntegrablePreimageStatement.{uF, uP, uA} F`. |

The field universe `uF`, the parameter universe `uP` and the automorphic
universe `uA` are independent. The head classification is used for
multisegments in `Multisegment.{max uF uA, uF}`, the universe in which the
published statement is stated.

## Proofs

**One-segment datum.** `singleton Δ π` has length `1`, the constant segment
family `Δ` and the constant block family `π`. The degree condition
`∑ i : Fin 1, deg Δ = deg Δ` holds by `simp`. Its multisegment is the
multiset of the one-element list `[Δ]`, which `simp` identifies with `{Δ}`.

**One-segment heads.** Let `π` be a segment head of `Δ`, and let
`d = singleton Δ π`. Its multisegment is `{Δ}`. Precedence ordering holds
vacuously: indices `i < j` in `Fin 1` would both be `0` (`omega`). The segment-head condition is the hypothesis. Segment
heads are irreducible by definition, and an irreducible representation is
its own irreducible head (the published `isIrreducibleHead_self`). The
published `SegmentProductOrderedAssembly.singletonIso` identifies the
induced representation of a one-entry datum with its block. Irreducible heads
transfer along this equivalence (`IsIrreducibleHead.of_equiv`), so `π` is the
irreducible head of `d.induced`. The degree-cast version follows by `subst`.

**Irreducible Weil classes.** Choose a representative `C` of `σ`. It is
irreducible by definition of `IrreducibleWeilClass`. The hypothesis says that
`B` and `C` have the same finite-representation class, so they are
equivalent (`FiniteRepresentation.classOf_eq_iff`). Irreducibility is
invariant under equivalence (`Weil.IsomorphismInvariance.irreducible_iff`).

**Main theorem.** Fix `c0`, `n`, `D` and `A`. Assume `D` is assembled from
`c0` to the class of `A`, and assume `A` is essentially square-integrable.
Unfolding `IsAssembledFrom` gives the following data:

- `r`, `d`, `m` and irreducible Weil classes `σ_i`;
- Weil representations `B_i` in the classes `σ_i`;
- a Weil–Deligne representative `W` of `D` with an equivalence
  `e : ⊕_i block ν (B_i) (m_i + 1) ≃ W`;
- an automorphic object `A'` with the same class as `A`;
- a representation `J` of `GL_n(F)` that is a Langlands head of
  `multisegmentOf F c0 σ m` and is equivalent to `A'`.

The proof then runs as follows.

1. `A'` and `A` have the same class, so they are isomorphic
   (`automorphicClassOf_eq_iff`). Hence `J` is equivalent to `A`.
   Essential square-integrability is invariant under equivalence
   (`isEssentiallySquareIntegrable_iff_of_equiv`), so `J` is essentially
   square-integrable. `J` is irreducible because it is a Langlands head.
2. The published proof of Bernstein–Zelevinsky's classification,
   `segmentEssentialSquareIntegrableClassification`, gives a segment `Δ`
   with `Δ.degree = n` such that `J` is a segment head of `Δ`. By the
   one-segment lemma, `J` is a Langlands head of `{Δ}`.
3. `J` is also a Langlands head of the universe lift of
   `multisegmentOf F c0 σ m` (Worker 1703's
   `Multisegment.isLanglandsHead_universeLift_iff`, from the module
   `Langlands.Representation.Classification.SegmentUniverseLift`). Apply the
   head classification to these two multisegments and the identity
   isomorphism `J ≅ J`. It gives
   `(multisegmentOf F c0 σ m).universeLift = {Δ}`.
4. Compare cardinalities. The universe lift is a `Multiset.map`, and
   `multisegmentOf` is the multiset of a list of length `r`. Hence `r = 1`.
5. With `r = 1`, the representation `B_0` is irreducible by the
   class lemma above. The block `block ν (B_0) (m_0 + 1)` is therefore
   indecomposable (`Blocks.isIndecomposable_block` from
   `Langlands.WeilDeligne.IrreducibleBlockIndecomposable`).
   `directSumFinOneEquiv` identifies the one-term direct sum with this block.
   Indecomposability transfers along this equivalence and along `e`
   (`Blocks.IsIndecomposable.of_equiv`), so `W` is indecomposable. Together
   with the fact that `W` represents `D`, this is
   `IsIndecomposableParameterClass F D`.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The main theorem is derived. It formalizes the argument in the provenance
section of Worker 1700's statement module, which follows Henniart 2002,
§§2.6–2.9 (printed pp. 595–596). By Zelevinsky 1980, 9.3 (cited in §2.6),
an essentially square-integrable class is the head of a single segment. By
the multiset classification of §2.8, the multisegment of the assembled
parameter must then be that single segment. So the parameter is one block
`σ ⊗ Sp(m+1)` with `σ` irreducible. In the Library the first fact is the
proved `segmentEssentialSquareIntegrableClassification`. The classification
of §2.8 is the hypothesis `MultisegmentHeadClassification` (Rodier 1982,
§4.3, Theorem 3(b)), which Henniart takes from the literature.

The one-segment datum, the one-segment lemma and the class lemma are internal glue. They are not
numbered results of any source.
