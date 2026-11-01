# Proof of the original-action additive tensor-Hom equivalences

`Langlands.Algebra.nonUnitalTensorHomAdjunction` proves the exact published
closed proposition `Langlands.Algebra.NonUnitalTensorHomAdjunctionTheorem`.
Its eight independent universe parameters are, in order, `uR`, `uS`, `uX`,
`uY`, `uZ`, `uX'`, `uY'`, `uZ'`. The theorem has no additional premise. It
combines the right and left existence, naturality, refined existence and
refined naturality targets from `NonUnitalTensorHomAdjunctionStatements`.

## Provenance and scope

This is an internal additive generalization motivated by David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original theorem I.2.2.1–I.2.2.3, corollary I.2.2.5–I.2.2.6,
its proof and the following naturality remark are on printed pages 15–16 /
PDF pages 21–22; these pages were read for this proof. The statement's paired
Markdown records the conventions and the supplementary earlier-edition errata
audit. Renard cites bibliography [34], pages 97–98, for the theorem's proof;
this development does not claim to have read that reference.

The implemented argument is the direct additive quotient construction described
below. It proves the published original-action targets for arbitrary nonunital
rings and their specified additive module actions, including zero or degenerate
actions over unital rings. The refinement assumes only idempotented R and
nondegenerate X. No idempotentedness of S or nondegeneracy of Y, Z or the whole
Hom is required. The original scalar and carrier universes remain independent.

Renard's theorem is complex-linear and uses unitizations; the present result is
additive. Complex-linearity, coefficient and unitization comparisons, tensor
associativity, exactness, actual categorical adjunctions and the source F,
pseudo-F, I and P constructions remain separate obligations.

## Original carriers, actions and canonical maps

The `Right` family retains X as a right R-module, Y as a commuting R–S
bimodule and Z as a right S-module. It constructs

```text
Hom_(Sᵐᵒᵖ)(Tensor R X Y, Z) ≃+ Hom_(Rᵐᵒᵖ)(X, Hom_(Sᵐᵒᵖ)(Y,Z)).
```

The tensor action is exactly `NonUnitalBimoduleTensor.rightModule X hY`;
the action on the inner Hom is exactly
`NonUnitalBimoduleHomActions.rightSourceAction hY`, given by
`(op r • h) y = h (r • y)`.

Independently, `Left` retains X as a left R-module, Y as a commuting S–R
bimodule and Z as a left S-module. It constructs

```text
Hom_S(Tensor R Y X, Z) ≃+ Hom_R(X, Hom_S(Y,Z)).
```

Here the actions are exactly `NonUnitalBimoduleTensor.leftModule hY X` and
`NonUnitalBimoduleHomActions.sourceAction hY`, the latter given by
`(r • h) y = h (op r • y)`. This construction uses the original actions
directly. Every Hom is the published `NonUnitalModuleHom`, and every tensor
is the published balancing quotient `NonUnitalModuleTensor.Tensor`.

For each family, `curry` evaluates an original intertwiner φ on pure tensors:
`curry φ x y = φ (tmul R X Y x y)` on the right, and
`curry φ x y = φ (tmul R Y X y x)` on the left. Biadditivity follows from
the pure-tensor addition formulas. Original S-linearity follows from φ's
intertwining law and the named tensor action. Original R-linearity follows
from `tmul_balanced` and the named source action on the inner Hom.

`uncurry` uses `rightLift` or `leftLift` of the statement's actual
`evaluationPairing ψ` and its implemented `evaluationPairing_balanced`.
The remaining one-sided S-equivariance is precisely `(ψ x).map_smul`.
The complete underlying additive inverse map is therefore the published
`NonUnitalModuleTensor.lift` of that pairing. This is a definitional equality,
which proves the whole-lift clause of `equivalence_canonical`.

`equivalence` packages these maps. Original-Hom extensionality and
`NonUnitalModuleTensor.hom_ext` show that uncurrying after currying returns
φ on the entire quotient; the reverse composite is pointwise definitionally
ψ. The common `inverseIdentities` lemma expresses the equivalence's inverse
laws as the two required equalities of whole additive maps.

## Whole-map naturality

`Right.naturality` and `Left.naturality` prove the target for arbitrary E and
E' satisfying the published canonical clauses. For original maps
`f : X' → X`, `g : Y' → Y` and `k : Z → Z'`, write P for the published
`tensorHomMap` and Q for `curriedHomMap`. Extensionality in φ, x' and y'
reduces the forward square to the pure-tensor formula for `rightMap` or
`leftMap` and the two canonical evaluation formulas. Both sides become
`k (φ (f x' ⊗ g y'))` on the right, and
`k (φ (g y' ⊗ f x'))` on the left.

Thus the proof establishes the complete additive-map equality
`E'.toAddMonoidHom.comp P = Q.comp E.toAddMonoidHom`.
The common `inverse_naturality` lemma applies E' to the other square and
uses the inverse laws to deduce
`E'.symm.toAddMonoidHom.comp Q = P.comp E.symm.toAddMonoidHom`.
No unrelated residual action is placed on Z. Both ring universes and all
six carrier universes are independent in these naturality theorems.

## Actual nondegenerate-part refinement

The common `partEquivalence` upgrades the published
`NonUnitalModuleHom.factorNondegeneratePart` to an additive equivalence
between original maps from a nondegenerate M into N and original maps into
`nondegeneratePart hA N`. The factorization sends m to the same value with
its membership proof: an idempotent fixing m also fixes its image by original
linearity. The inverse postcomposes with the actual subtype inclusion.
Original-Hom and subtype extensionality prove both inverse laws and additivity.
The scalar, source and target universes are independent; no categorical
carrier restriction is used.

Each `refinedEquivalence` composes the ambient equivalence with this
factorization, after installing the same named residual Hom action. On the
right it uses `hR.op`; on the left it uses `hR`. Hence its target is exactly
the statement's `HomPart` and `RefinedHom`. If J denotes the statement's
`inclusionMap`, `refinedEquivalence_canonical` proves refined pure-tensor
evaluation and both whole-map comparisons:

```text
J.comp End.toAddMonoidHom = E.toAddMonoidHom,
End.symm.toAddMonoidHom = E.symm.toAddMonoidHom.comp J.
```

The inclusion comparison follows by extensionality, and the inverse comparison
is definitional from the composite equivalence and the chosen inverse of
`partEquivalence`.

Each `refined_naturality` uses exactly the published `refinedHomMap`, whose
inner map is `NonUnitalModuleHom.restrictNondegeneratePart` of
`rightSourceMap` or `sourceMap`, with hR.op or hR respectively. Extensionality
through the actual subtype reduces its forward square to the refined
pure-tensor evaluation formula and the same tensor-map formula as above.
`inverse_naturality` then supplies the inverse square. The closed target keeps
both source nondegeneracy hypotheses; the pointwise naturality argument for
already compatible witnesses needs no further use of them.

## Closed assembly

In each handed namespace, `existence`, `whole_naturality`,
`refined_existence` and `whole_refined_naturality` discharge the corresponding
published closed propositions. The final theorem assembles exactly these eight
proofs in the statement's order. It imports the unchanged statement module and
`NondegenerateModuleAdjunction`; the statement and its imported definitions
are preserved. Its construction and proof use only the standard Lean axioms
`propext`, `Classical.choice` and `Quot.sound`.
