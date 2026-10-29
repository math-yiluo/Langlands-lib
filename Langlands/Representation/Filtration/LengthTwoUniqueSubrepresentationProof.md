# Proof of the length-two unique-subrepresentation criterion

Authors: Worker 163 (the complete Lean proof and original explanation) and
Worker 1014 (publication preparation, expanded explanation and dependency audit).
The Lean proof preserves Worker 163's shared draft.

The closed theorem `Langlands.lengthTwoUniqueSubrepresentationCriterion`
proves exactly the published proposition
`Langlands.LengthTwoUniqueSubrepresentationCriterion.{uK,uG,uV,uW}` from
`Langlands.Representation.Filtration.LengthTwoUniqueSubrepresentationStatement`.
It imports that statement by Lean name. The statement pair and all imported
pairs are unchanged.

## Data, universes and conclusions

The coefficient field, group, source carrier and target carrier have four
independent universes `uK`, `uG`, `uV` and `uW`. The source `A` is an actual
smooth representation. The target is an arbitrary algebraic representation
`σ` on `W`; it has no topology or smoothness premise. The group is supplied
with `Group` and `TopologicalSpace` instances, exactly as in the statement;
continuity of the group operations is not needed by this algebraic proof.

The theorem introduces precisely the statement's hypotheses: strict
monotonicity of the natural count `μ` on actual invariant subspaces,
`μ ⊥ = 0`, `μ ⊤ ≤ 2`, a nonzero intertwiner `f`, failure of irreducibility
of `A`, and containment in `f.ker` of every subspace of count one. There is
no extra theorem-valued assumption, finite-dimensionality assumption or
separately supplied composition series.

It constructs a composition series of length exactly two, proves equality
uniqueness of the nonzero proper invariant subspace, and proves irreducibility
of the actual smooth subrepresentation and quotient for every such subspace.
Irreducibility includes nonzeroness. Uniqueness concerns elements of
`Subrepresentation A.representation`, rather than isomorphism classes.

## Implemented count and kernel argument

`LengthTwo.count_eq_one_of_proper` uses `LengthTwo.count_pos` and strict
containment in the top subspace to obtain
`0 < μ S < μ ⊤ ≤ 2`; hence `μ S = 1`.

`LengthTwo.exists_proper_of_not_irreducible` uses the nonzero map to prove
that bottom and top of the invariant-subspace lattice are distinct. If every
subspace were bottom or top, this nontrivial lattice would be simple, making
`A` irreducible. The nonirreducibility premise therefore supplies an actual
nonzero proper subspace.

`LengthTwo.eq_ker_of_count_le_two` applies the annihilation premise to any
nonzero proper `S`, giving `S ≤ f.ker`. The kernel is nonzero because it
contains `S`, and proper by `LengthTwo.ker_ne_top_of_ne_zero`. Its count is
also one. Strict monotonicity rules out strict containment, so `S = f.ker`.
The final theorem chooses a nonzero proper `S` and identifies every other
one with the same kernel. This proves the exact existential uniqueness clause.
The additional annihilation premise is essential; the length bound alone
does not establish uniqueness.

## Composition series and actual smooth factors

For any nonzero proper `S`, the count bounds make `0 ⊂ S` and `S ⊂ A` covering
pairs by `LengthTwo.covBy_of_count`. The published `LengthTwo.twoStep S`
is the actual zero-to-full filtration with steps `⊥`, `S`, `⊤`, and
`LengthTwo.twoStep_hasSimpleFactors` proves its two graded quotients
irreducible. This directly witnesses `HasCompositionSeriesLength A.obj 2`.

`LengthTwo.proper_subrepresentation_and_quotient_irreducible` identifies
the factors with the requested actual smooth objects. It uses the published
canonical inclusion `SmoothRep.subtype A S` and quotient `SmoothRep.mkQ A S`.
Their underlying linear maps are the submodule inclusion and quotient map.
The proof uses `Submodule.range_subtype` and `Submodule.ker_mkQ` to verify
exactness and the equality of the inclusion's range with `S`.

`MultiplicityAdditivityProof.two_step_equivs` then gives actual representation
equivalences from the two graded pieces to
`SmoothRep.subrepresentation A S` and `SmoothRep.quotient A S`.
Its implementation quotients the range by zero for the first piece and
descends the surjective quotient map for the second piece.
`LengthTwo.isIrreducible_of_equiv` transfers the simple-factor proofs through
these equivalences. Smoothness of the two objects already follows from the
published injective and surjective smoothness-transfer constructions.

## Derived provenance

This is an internal algebraic generalization of the count and annihilation
step in Bernstein--Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), §2.16(1), printed pp.449--450/PDF pp.10--11.
The positive additive count is introduced in §2.14 on printed p.449/PDF p.10.
The registered source is `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
These passages were read in the registered original. No matching project
errata entry was present.

In the source, Jacquet functors and Frobenius reciprocity establish the
representation-specific count and annihilation assertions. Here their
sufficient algebraic consequences are explicit premises. The arbitrary-field,
independent-universe formulation is derived rather than quoted from BZ77.
The implemented proof uses the existing filtration and quotient infrastructure
to expose the actual smooth objects required by applications.

Every application to normalized induction must still establish all these
premises. This theorem supplies no induction reducibility, actual Jacquet
equivalence, or unconditional two-supercuspidal product theorem.

## Import and mathematical dependency audit

The complete project import closure of this proof has the following 26
modules, all under `Langlands.Representation`:

- `Category.Basic`, `Category.Subquotients`.
- `Smooth.Definitions`, `Smooth.Transfer.SubquotientStatement`,
  `Smooth.Transfer.SubquotientProof`.
- `Filtration.Definitions`, `Filtration.ObjectDefinitions`,
  `Filtration.LengthTwoUniqueSubrepresentationStatement`,
  `Filtration.LengthTwoMatchingStatement`, `Filtration.LengthTwoMatching`,
  `Filtration.LengthCriterionStatement`, `Filtration.LengthCriterionProof`,
  `Filtration.RepresentationLength`.
- `Filtration.MultiplicityStatement`,
  `Filtration.MultiplicityAdditivityStatement`,
  `Filtration.MultiplicityAdditivityProof`,
  `Filtration.MultiplicityIndependenceProof`,
  `Filtration.MultiplicityTransportStatement`,
  `Filtration.MultiplicityTransportProof`,
  `Filtration.JordanHolderStatement`,
  `Filtration.JordanHolderComparisonProof`,
  `Filtration.JordanHolderTransportProof`,
  `Filtration.GradedRefinementStatement`,
  `Filtration.GradedRefinementProof`,
  `Filtration.IntervalLiftStatement`,
  `Filtration.IntervalLiftProof`.

The count, covering-pair and nonzero-map lemmas used from `LengthTwoMatching`
were checked directly. The relevant proof of covering-pair irreducibility
pulls back an invariant subspace of the quotient to an intermediate invariant
subspace; it is ordinary module algebra. The quotient equivalences used from
`MultiplicityAdditivityProof` were checked directly through
`quotient_equiv_of_surjective`, `quotient_bot_equiv`, `source_equiv_range` and
`two_step_equivs`. They use actual linear maps, kernel/range equalities and
bijectivity, with no representation-theoretic input. The remaining transitive
project imports provide general filtrations, module length and Jordan--Hölder
calculus. Mathlib supplies representation, module, order and category
infrastructure. All 26 imported Lean/Markdown pairs match the published base.

Consequently neither the import closure nor the mathematical proof route uses
any excluded task, conclusion, proof successor or downstream consequence:
individual special-head/reverse-socle or segment-socle/reverse-head existence;
analytic segment classification; special square-integrability or
`SegmentSpecialEssentialSquareIntegrability`; multisegment special-head
exhaustion; ordered strong-head existence; quotient coverage; ordered
conversion; tempered uniqueness; `SquareIntegrableLanglandsClassification`;
square-integrable or regular exhaustion; special-head product irreducibility
or `GenericSegmentProductUniqueness`; `OrderedMultisegmentSocleExistence`;
`MultisegmentSocleExhaustion`; `SegmentSocleProductIrreducibility`; adjacent
socle commutation; `SegmentFullJacquetFormula` and its statement or exact
proof successor; `SegmentHeadJacquetFormula`; `SegmentSocleJacquetFormula`;
or `SegmentSpecialJacquetExponentNormFormula`.

There is no assumed derivative formula from Ze80 §§3.5 or 9.6 or BZ77,
no segment product irreducibility criterion from Ze80 4.2 or 9.7,
no analytic or square-integrability input from Ze80 9.3, and no classification
or exhaustion theorem. In fact no derivative result is used, even under the
operator's allowance for independently proved BZ77 general derivatives.
The segment-socle portion of task
`8e5b4563-0365-41c7-b134-70f2a0b36292` is also absent. The BZ77 citation
records provenance of this derived algebraic argument and introduces no
unproved representation-theoretic premise into the proof.

Development inspection of the exact theorem reports the independent universes
`uK,uG,uV,uW` and only `propext`, `Classical.choice` and `Quot.sound`.
Compilation is development evidence; independent acceptance and publication
of this proof are separate checks.
