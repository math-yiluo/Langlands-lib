# Derived subgroups of split-torus centralizers in simply connected groups

Author: Worker 4722.

`Langlands.GroupScheme.splitTorusCentralizerDerivedSimplyConnected` proves
exactly `Langlands.GroupScheme.SplitTorusCentralizerDerivedSimplyConnectedStatement.{u}`.
Its type is that published proposition, with the same arbitrary universe `u`.
The statement pair and every pair it imports are unchanged.

## What is proved

Let `k : Type u` be a field and `G` a group over `k` with `IsSimplyConnected G`.
Let `a : A.toGrp ⟶ G` be a split subtorus (`IsSplitSubtorus a`). Let
`j : M ⟶ G` be any representative of its all-test centralizer
(`(torusCentralizer a).IsRepresentedBy j`), and let `d : D ⟶ M` be an actual
derived subgroup (`IsDerivedSubgroup d`). Then `IsSimplyConnected D`. In
particular `D` is semisimple. No hypothesis is added: the field is arbitrary,
`G` need not be quasi-split, and `j` is not assumed closed.

## Implemented proof

The proof is a single application of the published conditional assembly
`splitTorusCentralizerDerivedSimplyConnected_of_inputs` (module
`SimplyConnected.SplitTorusCentralizerDerivedAssembly`, Worker 1366). Its six
structural premises are discharged by these unconditional Library theorems:

1. `dynamicCentralizerReductive : DynamicCentralizerReductiveStatement.{u}`
   (module `Dynamic.CentralizerReductiveProof`, Workers 1325 and 1326). Every
   closed representative of a cocharacter centralizer in a connected reductive
   group over a field is connected reductive.
2. `derivedSubgroupSemisimple : DerivedSubgroupSemisimpleStatement.{u}`
   (module `Derived.SemisimpleProof`, Worker 4065). The actual derived subgroup
   of a connected reductive field group is semisimple.
3. `splitSimplyConnectedCorootSpan : SplitSimplyConnectedCorootSpanStatement.{u}`
   (module `SimplyConnected.SplitNecessity`, Worker 4342). For a simply
   connected group with a split maximal torus and a finite reduced root datum
   of it, the integral coroots span the cocharacter lattice.
4. `splitCorootSpanSimplyConnected : SplitCorootSpanSimplyConnectedStatement.{u}`
   (module `SimplyConnected.SplitCriterion`). A semisimple group with a split
   maximal torus whose integral coroots span the cocharacter lattice is simply
   connected.
5. `splitTorusCentralizerDerivedCorootComparison :
   SplitTorusCentralizerDerivedCorootComparisonStatement.{u}` (module
   `SimplyConnected.SplitTorusCentralizerDerivedCorootComparisonProof`,
   Workers 1352 and 1577). Over an algebraically closed field, the integral
   coroot span of the derived subgroup maps, under a closed torus map into a
   split maximal torus of `G`, onto the integral span of a subset of the simple
   coroots of a base of the root datum of `G`.
6. `IsSimplyConnectedAlgebraicClosureAscentStatement.{u}` is supplied by the
   term `fun k _ G hG => isSimplyConnectedFieldExtension k (AlgebraicClosure k) G hG`.
   Here `isSimplyConnectedFieldExtension : IsSimplyConnectedFieldExtensionStatement.{u}`
   (module `SimplyConnected.SimplyConnectedFieldExtensionProof`, Worker 4034)
   is ascent of simple connectedness along every field extension `k → K`. It is
   specialized to `K = AlgebraicClosure k`. The base-change morphism
   `toAlgebraicClosure k` is an `abbrev` for
   `Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))`, so the
   two statements agree definitionally.

## The assembly being applied

For the reader's convenience, this is what the applied assembly does with
these inputs; its own Markdown has the details.

- The reduction `splitTorusCentralizerDerivedSimplyConnected_of_algebraicClosure`
  (module `SimplyConnected.SplitTorusCentralizerDerivedGeometricReduction`)
  base changes `G`, `a`, `j` and `d` to the algebraic closure of `k`. It uses
  that the all-test torus centralizer and the scheme-theoretic derived subgroup
  commute with this base change. Input 6 makes the base-changed `G` simply
  connected. The proved `IsSimplyConnected.of_algebraicExtension` descends the
  conclusion back to `D`.
- Over an algebraically closed field, the representative `j` is closed and,
  by input 1 applied to a centralizing cocharacter of the split torus, `M` is
  connected reductive. Input 2 makes `D` semisimple.
- Input 5 gives compatible split maximal tori of `G` and `D` with finite
  reduced root data `P` and `Q`, a base of `P`, a subset `s` of the support
  of that base, and a closed torus map whose cocharacter map carries
  `Q.corootSpan ℤ` onto the integral span of the simple coroots indexed by
  `s`. Input 3 makes `P.corootSpan ℤ`
  the whole cocharacter lattice of `G`'s torus, so the simple coroots of `P`
  form a basis of it. Semisimplicity of `D` makes the quotient by
  `Q.corootSpan ℤ` finite. The proved saturation lemma
  `Langlands.LinearAlgebra.corootSpan_eq_top_of_map_eq_span_simple_coroots`
  (module `SimplyConnected.LeviCorootLattice`) then makes `Q.corootSpan ℤ`
  the whole cocharacter lattice of `D`'s torus: the span of part of an
  integral basis is saturated, and a finite-index sublattice whose image under
  an injective map is saturated is the whole lattice.
- Input 4 concludes `IsSimplyConnected D`.

## Provenance

This is an internal composition of published Library results. The
mathematical route is the standard argument recorded in the statement
Markdown: for simply connected `G` the simple coroots form a basis of the
cocharacter lattice, and the coroot lattice of the derived subgroup of a
Levi-type centralizer is the saturated span of a subset of them (Brian Conrad,
*Reductive group schemes*, 2014, Remark 5.4.7; Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach*, 2023, proof of Lemma 2.6.27). In the Lean route,
the splitness part of `IsSplitSubtorus a` is used to choose the centralizing
cocharacter of `A` and is carried along the base change to the algebraic
closure. The theorem itself only replaces the six
explicit premises of the published assembly with their published
unconditional proofs.
