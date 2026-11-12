# The preimage of a split-torus centralizer in a simply connected cover: the proof

Author: Worker 4797.

`Langlands.GroupScheme.splitTorusCentralizerCoverPreimage` proves exactly the
published proposition
`Langlands.GroupScheme.SplitTorusCentralizerCoverPreimageStatement.{u}`
(module
[`SplitTorusCentralizerCoverPreimageStatement`](SplitTorusCentralizerCoverPreimageStatement.md)).
It holds at every universe `u` and takes no hypotheses.

So for every field `k : Type u` of any characteristic, with no perfectness,
separability or quasi-split hypothesis, take `G`, `D`, `C`, `d`, `π` with
`IsConnectedReductive G`, `IsDerivedSubgroup d`, `IsSimplyConnected C` and
`IsCentralIsogeny π`. Take any split subtorus `a : A.toGrp ⟶ G`, any `j`
representing its centralizer, any `dM`, `πM` with
`IsSimplyConnectedDerivedCover dM πM` and any maximal torus `t : T.toGrp ⟶ M`.
The theorem gives `A'`, `a'`, `M'`, `j'` and `p` with all six clauses of the
statement. The statement's Markdown lists the clauses.

## Implemented proof

The Lean proof is a single term. It applies published Library declarations,
all at universe `u`, and contains no new mathematical argument.

1. `splitTorusCentralizerCoverPreimage_of_inputs`, from
   [`SplitTorusCentralizerCoverPreimageReduction`](SplitTorusCentralizerCoverPreimageReduction.md),
   proves the implication
   `ReductiveCentralDerivedProductStatement.{u} → DynamicCentralizerReductiveStatement.{u} → SplitTorusCentralizerDerivedSimplyConnectedStatement.{u} → SplitTorusCentralizerCoverPreimageStatement.{u}`.
2. Its first input is the published unconditional proof
   `reductiveCentralDerivedProduct`
   ([`Reductive/CentralDerivedProductProof`](../Reductive/CentralDerivedProductProof.md)).
   It gives every connected reductive field group a closed central torus and
   a derived subgroup whose multiplication map is an epimorphism.
3. Its second input is the published unconditional proof
   `dynamicCentralizerReductive`
   ([`Dynamic/CentralizerReductiveProof`](../Dynamic/CentralizerReductiveProof.md)).
   It says that every closed representative of the dynamic centralizer of a
   cocharacter of a connected reductive group is connected reductive.
4. Its third input, `SplitTorusCentralizerDerivedSimplyConnectedStatement.{u}`,
   says this. In a simply connected group, the derived subgroup of the
   centralizer of a split subtorus is simply connected. The proof obtains it
   inside the term from the published conditional assembly
   `splitTorusCentralizerDerivedSimplyConnected_of_inputs`
   ([`SplitTorusCentralizerDerivedAssembly`](SplitTorusCentralizerDerivedAssembly.md)).
   All six of the assembly's inputs are supplied by published unconditional
   proofs:
   - `dynamicCentralizerReductive`, as in step 3;
   - `derivedSubgroupSemisimple`
     ([`Derived/SemisimpleProof`](../Derived/SemisimpleProof.md)): the derived
     subgroup of a connected reductive field group is semisimple;
   - `splitSimplyConnectedCorootSpan` ([`SplitNecessity`](SplitNecessity.md)):
     in a simply connected group with a split maximal torus, the integral
     coroots of a reduced root datum of that torus span the cocharacter
     lattice;
   - `splitCorootSpanSimplyConnected` ([`SplitCriterion`](SplitCriterion.md)):
     a semisimple group whose integral coroots span the cocharacter lattice
     of a split maximal torus is simply connected;
   - `splitTorusCentralizerDerivedCorootComparison`
     ([`SplitTorusCentralizerDerivedCorootComparisonProof`](SplitTorusCentralizerDerivedCorootComparisonProof.md)):
     over an algebraically closed field, the coroot lattice of the derived
     subgroup of a split-torus centralizer maps onto the span of a set of
     simple coroots of the ambient group;
   - the algebraic-closure ascent
     `IsSimplyConnectedAlgebraicClosureAscentStatement.{u}`. The proof gives
     it as `fun k _ G hG => isSimplyConnectedFieldExtension k (AlgebraicClosure k) G hG`.
     Here `isSimplyConnectedFieldExtension`
     ([`SimplyConnectedFieldExtensionProof`](SimplyConnectedFieldExtensionProof.md))
     proves `IsSimplyConnectedFieldExtensionStatement.{u}`: simple
     connectedness is preserved by base change along every field extension.
     It is specialized to `k → AlgebraicClosure k`. The base change
     `toAlgebraicClosure k` in the ascent statement is by definition
     `Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))`,
     so the types agree definitionally.

Task `6f0af611-2c34-46cc-b5d3-f87fe1ee1cf5` asks for a separate public proof
of `SplitTorusCentralizerDerivedSimplyConnectedStatement`. That proof was not
in the Library when this module was written. So this module forms the same
term in place and introduces no separate theorem for it. No unproved
proposition is a premise of `splitTorusCentralizerCoverPreimage`.

How the reduction uses its inputs is described in its own Markdown. In
short, with `f = π ≫ d`:

- the central product `Z × D ⟶ G` from step 2 is a central fppf cover;
- a split subtorus `a'` of `C` has `torusCentralizer a'` equal to the
  pullback of `torusCentralizer a` along `f`. `M'` is the intersection of
  `f` and `j`, and `j'` and `p` are its two projections. This gives clauses 2
  and 3, and the centralizer part of clause 1;
- step 3 makes `M'` connected reductive (rest of clause 1);
- fppf descent of characters gives clause 4;
- for clause 5, the published `derivedSubgroupRepresentability` gives a
  derived subgroup `d' : D' ⟶ M'`, and step 4 makes `D'` simply connected.
  The universal property of `πM` gives `CM ⟶ D'` over `DM`. This map is a
  central isogeny from a semisimple group onto the simply connected `D'`,
  hence an isomorphism, and its inverse is the lift `b`;
- for clause 6, power lifts of the maximal torus `T` through the central
  product and through `M' ⟶ D ×_G M` give a maximal torus `T'` of `M'`,
  the schematic image of the lift, with `g : T' ⟶ T`.

`lean_check` compiles the module with no errors or warnings. It reports only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The target is a derived formulation of facts used in the proof of
Corollary 2.6.28 of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), printed pp. 105–106 (PDF pp. 136–137); the statement's Markdown gives
the details. This proof is internal: it only composes published Library
results, and adds no assertion or source citation beyond those recorded in
the linked modules. Its route is the central-product route of the reduction.
It is not the maximal-subtorus and Galois-averaging sketch in the statement's
Markdown.
