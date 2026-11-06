# Negation stability of the actual relative roots: proof

Authors: Worker 1310, with the generic-centralizer route suggested by Worker 1650.
The generic-centralizer setup adapts Worker 1422's published
`Reductive/RootReducednessReduction`. The final splitting-field assembly
adapts Worker 1317's published `Rational/AbsoluteRootRestriction`.

`Langlands.GroupScheme.relativeRootNegation` proves exactly
`Langlands.GroupScheme.RelativeRootNegationStatement.{u}`. For every field
`k : Type u`, connected reductive group scheme `G` over `Spec k`, and maximal
split torus inclusion `i : T.toGrp ⟶ G`, it proves
`∀ α ∈ relativeRoots i, -α ∈ relativeRoots i`.
The roots are the published actual nonzero characters with nonzero
all-test-algebra adjoint weight space in the Lie algebra. Negation is additive
inversion in the original character lattice. The field and its characteristic
are arbitrary; no splitness assumption on `G`, reducedness assumption on the
relative-root system, or nonemptiness assumption on its roots is added.
The final theorem has no premises.

## Implemented proof

The helper `neg_mem_roots_of_split_maximalTorus` treats a split maximal torus
over an arbitrary field. Given a root `α`, choose
`RootReducedness.kernelCocharacter` for `α` and the finite actual root set.
Its pairing with `α` is zero, and every ambient root pairing to zero with it
is integrally dependent with `α`. These properties and the finiteness input
are the published lemmas in `Reductive/RootReducednessReduction` and
`Rational/RootSupportFiniteness`.

Use the canonical affine representative of the dynamic centralizer of that
cocharacter. The published theorem `dynamicCentralizerReductive`
(`Dynamic/CentralizerReductiveProof`) makes its source `L` connected
reductive. The original torus factors through `L`; it is still maximal by
`IsMaximalTorus.of_comp`.

`RootReducedness.mem_roots_torusFactor` places `α` among the roots of `L`.
Conversely, `RootReducedness.mem_roots_of_mem_roots_torusFactor` identifies
each root of `L` as an ambient root pairing to zero with the chosen
cocharacter. Each is therefore integrally dependent with `α`. Since `α`
and every root are nonzero, the published lattice dependence lemma makes
any two roots of `L` integrally dependent.

Apply the independently proved
`RootReducedness.neg_mem_roots_of_rankOne`
(`Reductive/RootReducednessProof`) to `L` and its split maximal torus.
It gives the root `-α` in `L`; the same root comparison includes it among
the roots of `G`. This rank-one negation theorem uses a proper Borel and
a nonidentity normalizer class over an algebraic closure, followed by
descent. Its proof does not assume the general relative-root negation
statement. No root-datum existence or rank-one positive-root uniqueness
premise is used by the present helper.

For the final theorem, the published
`exists_maximalTorus_extension_of_finiteType` supplies a maximal torus `M`
containing the given maximal split torus `T`. The `IsTorus` witness supplies
a same-universe field extension `K` splitting `M`.
`connectedReductiveFieldExtensionStatement`
(`Reductive/FieldExtensionProof`) proves connected reductivity after this
extension, and `maximalTorusBaseChange`
(`Torus/MaximalBaseChangeProof`) proves maximality of the pulled-back `M`.
The helper above gives opposite roots for this split maximal torus.

Finally, `roots_negation_of_splittingField_restriction`
(`Rational/AbsoluteRootRestriction`) descends these opposites. That lemma
lifts an original root to an actual root of `M` over `K`, negates the lift,
and uses additivity of restriction and character pullback to descend
membership of the negative original character. Rewriting the containing
torus factorization gives the conclusion for `i`; `relativeRoots i` and
`roots i` are definitionally equal.

## Provenance and dependencies

This is an internal derived proof from the published results named above.
The generic-centralizer setup adapts the implemented proof of
`rootReducedness_of_rankOne`; the final extension and descent setup adapts
`relativeRootNegationStatement_of_rootDatum_fieldExtension_maximalTorus`,
replacing its root-datum argument with the split-maximal-torus helper.
The rank-one negation proof and every other statement-valued dependency
are supplied by unconditional published theorems. The target statement
and every Lean/Markdown pair it imports are unchanged.

The target's paired Markdown records the original-literature provenance
in Kaletha–Prasad, Section 2.6(b). This module makes no new
original-literature claim; it documents the implemented Library derivation.
