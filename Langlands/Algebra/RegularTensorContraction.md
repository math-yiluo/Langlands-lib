# The canonical regular-tensor comparison

`Langlands.Algebra.regularTensorContraction` proves exactly the published
closed proposition `RegularTensorContractionTheorem` at independent universes
`uA`, `uM`, and `uN`. It proves comparison existence separately for both
ambient-module universes and both whole-map naturality clauses. The statement
and all its imported constructions are unchanged.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, I.2.3, formula (I.2.3.3),
printed page 17 / PDF page 23; the original conventions occur on printed
pages 5–7 / PDF pages 11–13, and the module and tensor constructions on
printed pages 14–17 / PDF pages 20–23. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The supplementary registered `renard-2010-corrections-complements`,
PDF pages 1–2, concerns the 2010 edition and gives no correction to this
contraction assertion.

Renard states the assertion for complex idempotented algebras. The published
target's arbitrary idempotented nonunital ring and additive-module scope is
an internal generalization: the proof uses only additivity, associativity of
the original action, balancing, and finite common local units. The additional
bundled inverse identities and naturality equations make explicit the
canonical comparison supplied by the contraction. No coefficient linearity
is asserted.

The tensor is precisely the published quotient
`NonUnitalModuleTensor.Tensor A A M`, with `rightRegular A` on the first
factor and its inherited additive group. Its left action is precisely the
published `tensorModule A M`, induced from the regular bimodule, and its
contraction is the published universal lift of the original action pairing.
On pure tensors contraction evaluates to `a • m`; the actual residual-action
equivariance follows by additive-map extensionality on pure tensors and
`mul_smul`.

`exists_normal_form` implements the common-local-unit argument. Surjectivity
of the projection reduces to induction on the integer tensor product. For a
pure tensor, an idempotent corner supplies a left unit for its first factor,
and balancing gives the normal form. The inductive assertion is strengthened
to hold above one chosen idempotent. Thus an upper bound of the two
idempotents from an addition step gives a common normal form. Every tensor
`t` consequently equals `pure A M e (contraction A M t)` for a suitable
idempotent `e`. A tensor with zero contraction vanishes, which proves
injectivity.

Applying contraction to the normal form shows that every image vector is
fixed by an idempotent. Conversely, if `e` fixes `m`, the pure tensor `e ⊗ m`
contracts to `m`. This proves exact equality of the additive range with the
actual original `nondegeneratePart hA M`, including degenerate ambient
modules.

`has_comparison` bundles contraction as an original module map `F` to this
actual part. It is bijective by the preceding injectivity and fixing-vector
calculation. The private `exists_module_inverse` constructs an additive
inverse using `AddEquiv.ofBijective` and proves its original equivariance by
injectivity of `F`; this yields an original module map `G` and both bundled
inverse identities. The factorization through the actual inclusion is
definitional. For **every** idempotent `e` fixing an input vector `m`,
`G m = pure A M e m.val`: both sides have contraction `m.val`, so injectivity
identifies them. The formula does not depend on a chosen fixing idempotent.

`nondegenerate_comparison` applies the same inverse construction to the
ambient contraction only under the explicit original hypothesis
`IsNondegenerate A M`, which supplies surjectivity onto all of `M`. It proves
both whole-module inverse identities and the corresponding formula for
every fixing idempotent.

The imported companion `RegularTensorContractionNaturality` proves
contraction naturality by pure-tensor extensionality and the original
intertwiner law. Its forward comparison square follows from the two
factorizations and contraction naturality after the actual part inclusion.
The inverse square follows by applying the target inverse and the bundled
inverse identities. These are equalities of entire additive composites using
the actual `tensorMap` and `restrictNondegeneratePart`, for arbitrary
comparison witnesses and independent ambient universes.

No unitality, commutativity, nontriviality, or ambient nondegeneracy premise
is added to the general comparison. Zero rings and zero actions remain in
scope. The proof requires neither general tensor nondegeneracy nor resizing.
Coefficient refinements, induction functors and adjunctions, formula
(I.2.3.4), associativity, Hom adjunction, exactness, and corner comparisons
are outside this result.
