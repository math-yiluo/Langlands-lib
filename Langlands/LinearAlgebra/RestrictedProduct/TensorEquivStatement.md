# Inverse laws for the restricted-product tensor equivalences

`RestrictedProduct.TensorEquivInverseLaws` is a proposition definition in
`Langlands.LinearAlgebra.RestrictedProduct.TensorEquivStatement`. It states
both inverse identities for each of the published equivalences in
`Langlands.LinearAlgebra.RestrictedProduct.TensorEquiv`, using the published
canonical forward maps and the equivalences' actual `.symm` inverses.
This module states a target; it contains no theorem proving that target.
An accepted exact proof is a subsequent phase.

The declaration has four independent universe parameters, in the order
`.{uR, uM, uι, uN}`. Its full outer type is
`RestrictedProduct.TensorEquivInverseLaws.{uR, uM, uι, uN} : Prop`.
Every mathematical datum and instance is universally quantified inside its
value. The value is a conjunction `A ∧ B`, whose two clauses quantify their
data separately. Consequently, the first clause retains general modules
without acquiring the second clause's ring or algebra hypotheses.

## Clause A: the general `R`-linear inverse laws

The first clause universally quantifies:

- `R : Type uR` and `M : Type uM`, with `[CommRing R]`,
  `[AddCommGroup M]` and `[Module R M]`;
- `[Module.FinitePresentation R M]` and `[Module.Flat R M]`;
- an arbitrary index type `ι : Type uι`;
- `N : ι → Type uN`, with `[∀ i, AddCommGroup (N i)]` and
  `[∀ i, Module R (N i)]`;
- an arbitrary filter `ℱ : Filter ι`;
- arbitrary submodules `L : ∀ i, Submodule R (N i)`.

Neither `M` nor any `N i` is required to be a ring or an algebra. For these
data, put

```lean
e := lTensorEquiv R M N ℱ L
f := lTensor R M N ℱ L
```

Here `e` is an `R`-linear equivalence and `f` is the canonical `R`-linear
map, both with domain

```lean
M ⊗[R] (Πʳ i, [N i, L i]_[ℱ])
```

and codomain

```lean
Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ].
```

The coordinate submodule `rangeLTensor R M N L i` is
`LinearMap.range (LinearMap.lTensor M (L i).subtype)`. Thus the codomain uses
the image of the inclusion-induced map from `M ⊗[R] L i` into
`M ⊗[R] N i`, recorded as an `R`-submodule.

Clause A asserts the conjunction

```lean
(∀ x : M ⊗[R] (Πʳ i, [N i, L i]_[ℱ]), e.symm (f x) = x) ∧
(∀ y : Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ],
  f (e.symm y) = y).
```

Both `x` and `y` range over all elements of these types. The identities are
equalities in the tensor product and restricted product themselves.

## Clause B: the `M`-linear inverse laws

The second clause independently universally quantifies:

- `R : Type uR` and `M : Type uM`, with `[CommRing R]`, `[CommRing M]`
  and `[Algebra R M]`;
- an arbitrary index type `ι : Type uι`;
- coordinate rings `N : ι → Type uN`, with `[∀ i, Ring (N i)]` and
  `[∀ i, Algebra R (N i)]`;
- arbitrary `R`-submodules `L : ∀ i, Submodule R (N i)`;
- an arbitrary filter `ℱ : Filter ι`;
- `[Module.Flat R M]` and `[Module.FinitePresentation R M]`.

The coordinate rings `N i` need not be commutative, and the `L i` need not
be subrings. For these data, put

```lean
e := lTensorEquivLeft R M N L ℱ
f := lTensorLeft R M N ℱ L
```

The explicit orders differ: the equivalence takes `R M N L ℱ`, while the
map takes `R M N ℱ L`. Both are `M`-linear, with the same domain as in
clause A and codomain

```lean
Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ].
```

Here `rangeLTensorLeft R M N L i` is the range of
`TensorProduct.AlgebraTensorModule.lTensor _ _ (L i).subtype`, as an
`M`-submodule of `M ⊗[R] N i`. The `M`-action on the tensor product is
through the left factor; the codomain has the induced restricted-product
`M`-module structure. These are the actions of the published maps and
equivalences.

Clause B asserts the conjunction

```lean
(∀ x : M ⊗[R] (Πʳ i, [N i, L i]_[ℱ]), e.symm (f x) = x) ∧
(∀ y : Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ],
  f (e.symm y) = y).
```

Again, both identities quantify arbitrary elements. They use the actual
tensor-image codomain, without identifying its coordinate submodules with
the abstract tensor products `M ⊗[R] L i`.

## Scope and dependency

Every index type and filter is allowed in each clause, including an empty
index type, the bottom filter and every principal filter. There is no
finite-index, cofinite-filter, `NeBot`, freeness, projectivity or
number-field restriction. Bijectivity, equivalences and inverse laws are
not hypotheses: the local names `e` and `f` abbreviate the existing
constructions. No restriction to pure tensors or coordinate equalities is
made.

The sole import is
`Langlands.LinearAlgebra.RestrictedProduct.TensorEquiv`. Through that
module the target uses `lTensor`, `lTensorLeft`, `rangeLTensor` and
`rangeLTensorLeft` from the published `Tensor` module. The equivalences
package those maps using `LinearEquiv.ofBijective` and the published
comparison proof. Their forward maps are definitionally the corresponding
canonical maps. This statement module introduces only the Prop target,
with no helper, new map, new equivalence or instance. The imported pairs
are unchanged.

## Provenance and attribution

This is an internal target derived from the accepted constructions, with
the mathematical specification by Worker 98 and the Lean/Markdown
formulation by Worker 288. The Imperial original constructs the
equivalences at lines 234–244 of
[`FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean`](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean#L234-L244),
at commit `923d45174c500aa1d994ba973bac38ea39eacbf7`. The general module
hypotheses are at lines 28–32 and 102, and the algebra hypotheses at
240–244. The original file was read in full. It does not separately state
the new grouped inverse-law target.

The snapshot is registered as
`external-lean-reuse-snapshots-2026-10-21`, with fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The file under `ImperialCollegeLondon--FLT/source` has SHA-256
`a750850ebe7c7bc80532fafbc865067df53f9686be9bc7a60d99961c158b4e9b`.
The source is copyright 2025 Matthew Jasper, author Matthew Jasper,
under Apache-2.0. Its notice is retained in the Lean header, and the
upstream license is retained at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The prominent derivation notice explains the new grouped target,
separate quantification and unchanged imported constructions. No
original proof or equivalence construction is copied into this module.

Mathlib at pinned commit `5ed2965256430c3649e86755f9576b54eca72435`,
`Mathlib/Algebra/Module/Equiv/Defs.lean:353–359`, provides the ordinary
laws `LinearEquiv.apply_symm_apply` and `LinearEquiv.symm_apply_apply`.
Those laws, together with the canonical forward maps of the published
equivalences, motivate this target. This provenance does not constitute
an accepted proof of the exact grouped proposition.

The relevant public
[finite-adele base-change audit](../../../notes/reuse/finite-adele-base-change-audit.md),
sections 3–6 and Appendix B, was consulted for provenance and license
guidance. Its compatibility patches concern other source locations.
No applicable project errata file or Imperial snapshot errata or `NOTICE`
file was found. No Anthropic derivative code is used.

## Development validation

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), `lean_check` built
the paired statement module with no errors or warnings. Inspection reports
a definition returning `Prop`, with `statement_returns_prop: true` and
exactly the universe parameters `[uR, uM, uι, uN]`. The only transitive
axioms are `propext`, `Classical.choice` and `Quot.sound`. A separate
private diagnostic inspected the full unapplied types of the two imported
equivalences and the two maps. These development checks do not establish
independent semantic acceptance or an exact proof of this target.
