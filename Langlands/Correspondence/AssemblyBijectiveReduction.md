# Bijectivity of the assembly, reduced to the multisegment classification

Author: Worker 1704.

## Scope and provenance

This module reduces `Langlands.Correspondence.AssemblyBijectiveStatement`
([AssemblyRelation.md](AssemblyRelation.md)) to three published propositions that
it does not prove:

- `Classification.MultisegmentHeadClassification F F.canonicalTopologicalData`
  (Rodier 1982, Theorem 3(b) in multiset form): two Langlands heads of
  multisegments at the same rank are isomorphic iff the multisegments are equal;
- `Classification.MultisegmentHeadExhaustion F F.canonicalTopologicalData`
  (Rodier 1982, Theorem 3(c)): every irreducible smooth representation of rank
  `n` is the Langlands head of a multisegment of degree `n`;
- `AssemblyWellDefinedStatement F`: every parameter class is assembled to exactly
  one representation class.

The two classification propositions are taken at carrier universe `uV := uA`,
so they quantify over multisegments in `Multisegment.{max uF uA, uF}`. See
[../Representation/Classification/MultisegmentClassificationStatement.md](../Representation/Classification/MultisegmentClassificationStatement.md).
The reduction appears only as explicit hypotheses of the theorems below. The
module does not prove `AssemblyBijectiveStatement` itself, and it does not prove
any of the three propositions.

Provenance: internal. The module formalizes no literature theorem. The reduction
is the standard argument: injectivity follows from the classification, and
surjectivity from exhaustion together with well-definedness. Everything else is
proved here or comes from the Library and from three support modules:

- the universe lift of segments and multisegments,
  [../Representation/Classification/SegmentUniverseLift.md](../Representation/Classification/SegmentUniverseLift.md);
- the multisegment and block-sum combinatorics,
  [AssemblyMultisegments.md](AssemblyMultisegments.md);
- the block-sum parameter class,
  [../Weil/Local/BlockSumParameter.md](../Weil/Local/BlockSumParameter.md).

## Universe descent (namespace `Langlands.PadicField.TopologicalData`)

The multisegments built by `multisegmentOf` live in `Multisegment.{uA, uF}`. The
classification propositions speak about `Multisegment.{max uF uA, uF}`. The lift
`Multisegment.universeLift` of `SegmentUniverseLift` is injective and preserves
Langlands heads. For surjectivity we also need every multisegment in the larger
universe to be a lift.

- `supercuspidalClass_universeLift_surjective T n`: every supercuspidal class of
  `GL_n(F)` with carriers in `Type (max uF uV)` is the lift of a class with
  carriers in `Type uV`. Take a representative `B`. The proved small-model theorem
  `padicIrreducibleSmoothSmallRealization` gives an irreducible smooth
  representation `σ` in `Type uV` with an equivalence `e` to `B`. `σ` is
  supercuspidal (`GeneralLinear.isSupercuspidal_of_equiv`). The lift of `σ` is
  isomorphic to `B` through the composite of the inverse ULift equivalence and
  `e⁻¹`.
- `CuspidalDatum.universeLift_surjective`,
  `Segment.universeLift_surjective`, `Multisegment.universeLift_surjective`:
  the lifts of cuspidal data (fieldwise), of segments (descend the base, then
  `Segment.exists_universeLift_eq`), and of multisegments
  (`Multiset.map_surjective_of_surjective`) are surjective.

## Block sums (namespace `Langlands.Correspondence`)

- `rank_eq_of_classOf_eq`: a representative of an irreducible Weil class of rank
  `k` has rank `k`.
- `exists_representative`: every irreducible Weil class has a continuous
  irreducible representative (the class is a quotient of representations
  carrying those two properties).
- `blockSumClass F σ m n hn` (definition): for irreducible Weil classes
  `σ i` of ranks `d i + 1`, lengths `m i`, and `n = ∑ i, (d i + 1) * (m i + 1)`
  (hypothesis `hn`), this is the parameter class of rank `n` of the block sum
  `⊕_i σ_i ⊗ Sp(m_i + 1)`. It is `Weil.Local.blockSumParameterClass` applied to
  representatives chosen by `exists_representative` and to the block lengths
  `m i + 1`. The rank is moved from `∑ i, rank(B i) * (m i + 1)` to `n` using
  `rank_eq_of_classOf_eq` and `hn`.
- `isBlockSum_blockSumClass`: `blockSumClass F σ m n hn` satisfies the published
  `IsBlockSum F σ m`. The witnesses are the chosen representatives and the block
  sum itself (`forget_blockSumParameterClass`, identity equivalence).

## The reduction

Fix `c0 : SupercuspidalMap F` and `c : FullMap F` with `IsAssemblyOf F c0 c`.

- `assembly_injective hHC hc0 hc n`: if `hHC` holds and every `c0 k` is
  injective, then `c n` is injective. Suppose `c n D = c n D'`. The assembly
  gives block data `(σ, m)` and `(σ', m')` with `IsBlockSum`, automorphic objects
  `A`, `A'` and Langlands heads `J`, `J'` of `multisegmentOf F c0 σ m` and
  `multisegmentOf F c0 σ' m'`, equivalent to `A` and `A'`. The classes of `A` and
  `A'` agree, so `automorphicClassOf_eq_iff` gives an equivalence `A ≃ A'`, hence
  an isomorphism `J ≅ J'`. Both heads are also heads of the lifted multisegments
  (`Multisegment.isLanglandsHead_universeLift_iff`). By `hHC` the lifted
  multisegments are equal, and by `Multisegment.universeLift_injective` so are
  the original ones. `multisegmentOf_matching` then matches the block data by a
  bijection `Fin r ≃ Fin r'`, and `IsBlockSum.eq_of_matching` gives `D = D'`.
- `assembly_surjective hHE hWD hc0 hc n`: if `hHE` and `hWD` hold and every
  `c0 k` is surjective, then `c n` is surjective. Take a class `π` with
  representative `A`. Its universe lift `J` to `max uF uA` is irreducible
  (`SmoothRep.isIrreducible_universeLift_iff`). By `hHE`, `J` is the Langlands
  head of some multisegment `b` of degree `n`. By
  `Multisegment.universeLift_surjective`, `b` is a lift of some `a`; `J` is a
  head of `a` and `a` has degree `n`. By `exists_multisegmentOf_eq`, `a` is
  `multisegmentOf F c0 σ m`, and `degree_multisegmentOf` gives
  `n = ∑ i, (d i + 1) * (m i + 1)`. Let `D := blockSumClass F σ m n _`. Then
  `IsAssembledFrom F c0 D π` holds: use `isBlockSum_blockSumClass`, the object
  `A`, the head `J` and the inverse ULift equivalence `J ≃ A`. By `hWD` the
  assembled class is unique, so `c n D = π`.
- `assemblyBijective_of_classification hHC hHE hWD :
  AssemblyBijectiveStatement F`: combine the two, using the injective and the
  surjective halves of `SupercuspidalRankwiseBijective F c0`.

Universe parameters: `uF` (field), `uP` (parameter carriers) and `uA`
(automorphic carriers) are independent. The classification hypotheses are
instantiated at `.{uF, uA}`.
