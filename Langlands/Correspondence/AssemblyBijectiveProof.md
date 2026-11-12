# Bijectivity of the assembly

Author: Worker 4838.

## Result

`Langlands.Correspondence.assemblyBijective :
AssemblyBijectiveStatement.{uF, uP, uA} F` proves the target proposition of
[AssemblyRelation.md](AssemblyRelation.md) for every prime `p` with
`[Fact p.Prime]` and every `F : PadicField.{uF} p`, with `uF`, `uP` and `uA`
independent. Let `c0 : SupercuspidalMap F` be rankwise bijective and let
`c : FullMap F` satisfy `IsAssemblyOf F c0 c`. Then `c n` is injective and
surjective at every rank `n`. The theorem has exactly the two hypotheses of the
statement. No classification, correspondence or well-definedness premise is
added: every input below is a proved Library theorem.

Source of the argument: Henniart 2002, §2.9 (printed p.596). There the full
bijection is built from the supercuspidal one through the block decomposition
and the Langlands classification. The Lean proof follows that route through the
published reduction
[AssemblyBijectiveReduction.md](AssemblyBijectiveReduction.md) by Worker 1704.

The module uses the canonical topology `F.canonicalTopologicalData` on `F` and
on `GL_n(F)` as local instances, as in the reduction module.

## Multiset head classification

`multisegmentHeadClassification_canonical F :
Classification.MultisegmentHeadClassification.{uF, uA} F F.canonicalTopologicalData`.

Take Langlands heads `π` of a multisegment `a` and `π'` of `b`, at the same rank
`n`. By definition (`Multisegment.IsLanglandsHead`, in
[../Representation/Classification/LanglandsData.md](../Representation/Classification/LanglandsData.md))
there are segment product data `d` and `d'` with `d.multisegment = a`,
`d'.multisegment = b`, `d.IsLanglandsHead π` and `d'.IsLanglandsHead π'`.
Substitute `a` and `b`. Weaken both heads to quotients
(`SegmentProductDatum.IsLanglandsHead.isLanglandsQuotient`). The published
conditional `orderedMultisegmentHeadClassification_of_squareIntegrable`
([../Representation/Classification/OrderedMultisegmentHeadClassificationReduction.md](../Representation/Classification/OrderedMultisegmentHeadClassificationReduction.md))
has two premises, both proved in the Library:

- `squareIntegrableLanglandsClassification`
  ([../Representation/Classification/SquareIntegrableLanglandsClassificationProof.md](../Representation/Classification/SquareIntegrableLanglandsClassificationProof.md));
- `segmentSpecialParameterUniqueness`
  ([../Representation/Classification/SegmentSpecialParameterUniquenessProof.md](../Representation/Classification/SegmentSpecialParameterUniquenessProof.md)).

With them it gives `d.multisegment = d'.multisegment ↔ Nonempty (π ≅ π')`, which
is the claim. This lemma is stated only for the canonical topological data used
here. It is not a proof of the general `MultisegmentHeadClassification` target
of another task.

## Injectivity

`assembly_injective` from the reduction module, applied to
`multisegmentHeadClassification_canonical F` and to the injective halves of
`SupercuspidalRankwiseBijective F c0`. Equal assembled classes give isomorphic
Langlands heads, hence equal multisegments, hence matched block data, hence
equal parameter classes. The details are in
[AssemblyBijectiveReduction.md](AssemblyBijectiveReduction.md).

## Surjectivity

`assembly_surjective_of_surjective hc0 hc n`: if every `c0 k` is surjective and
`IsAssemblyOf F c0 c`, then `c n` is surjective. The argument is that of
`assembly_surjective` in the reduction module. It differs in two places: head
exhaustion is the proved theorem rather than a premise, and the last step uses
the unconditional uniqueness of the assembled class instead of
`AssemblyWellDefinedStatement`.

1. Take a class `π` with representative `A`
   (`automorphicClass_has_representative`). Its universe lift `J` to
   `max uF uA` is irreducible (`SmoothRep.isIrreducible_universeLift_iff`).
2. By the proved `Classification.multisegmentHeadExhaustion`
   ([../Representation/Classification/MultisegmentHeadExhaustionProof.md](../Representation/Classification/MultisegmentHeadExhaustionProof.md)),
   `J` is the Langlands head of a multisegment `b` of degree `n`.
3. By `Multisegment.universeLift_surjective`, `b` is the lift of some `a` in
   universe `uA`. By `Multisegment.isLanglandsHead_universeLift_iff` and
   `Multisegment.universeLift_degree`, `J` is a head of `a` and `a` has degree
   `n`.
4. Since `c0` is surjective, `exists_multisegmentOf_eq` writes `a` as
   `multisegmentOf F c0 σ m` for irreducible Weil classes `σ i` and lengths
   `m i`. Then `degree_multisegmentOf` gives `n = ∑ i, (d i + 1) * (m i + 1)`.
5. Let `D := blockSumClass F σ m n _`. Then `IsAssembledFrom F c0 D π` holds:
   use `isBlockSum_blockSumClass`, the object `A`, the head `J` and the inverse
   ULift equivalence `J ≃ A`.
6. `IsAssemblyOf F c0 c` gives `IsAssembledFrom F c0 D (c n D)`. The proved
   `isAssembledFrom_unique` ([AssemblyUniqueness.md](AssemblyUniqueness.md))
   says two classes assembled from the same `D` are equal, so `c n D = π`.

## Assembly

`assemblyBijective F` combines the two halves at each rank `n`, using the
injective and surjective halves of `SupercuspidalRankwiseBijective F c0`.

Axioms used: `propext`, `Classical.choice`, `Quot.sound`.
