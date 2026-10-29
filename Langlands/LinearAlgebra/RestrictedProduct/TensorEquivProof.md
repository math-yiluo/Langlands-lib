# Inverse laws for the restricted-product tensor equivalences: proof

Worker 963 wrote this proof. Worker 98 specified the task and suggested the
route through Mathlib's ordinary inverse laws. The proof is internal: it
derives consequences of constructions already published in the Library and
copies no code from the Imperial original.

## Exact theorem

The module `Langlands.LinearAlgebra.RestrictedProduct.TensorEquivProof`
imports only the unchanged published statement module
`Langlands.LinearAlgebra.RestrictedProduct.TensorEquivStatement`. Its one
declaration is

```lean
theorem RestrictedProduct.tensorEquivInverseLaws_proof.{uR, uM, uι, uN} :
  RestrictedProduct.TensorEquivInverseLaws.{uR, uM, uι, uN}
```

The theorem has no term parameters, no hypotheses and no instance arguments
of its own. Its whole type is the closed target proposition. The four
universe parameters `uR`, `uM`, `uι` and `uN` are independent, in this
order: `R : Type uR`, `M : Type uM`, `ι : Type uι` and `N : ι → Type uN`.

The target is a conjunction `A ∧ B`. Each clause universally quantifies its
own data and instances.

- **Clause A** quantifies a commutative ring `R` and an additive commutative
  group `M` with `[Module R M]`, `[Module.FinitePresentation R M]` and
  `[Module.Flat R M]`; an index type `ι`; additive commutative groups `N i`
  with `[∀ i, Module R (N i)]`; a filter `ℱ : Filter ι`; and submodules
  `L : ∀ i, Submodule R (N i)`. Neither `M` nor any `N i` needs a ring
  structure. With `e := lTensorEquiv R M N ℱ L` and
  `f := lTensor R M N ℱ L`, it asserts `e.symm (f x) = x` for every
  `x : M ⊗[R] (Πʳ i, [N i, L i]_[ℱ])`, and `f (e.symm y) = y` for every
  `y : Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ]`. Here `e` is an
  `R`-linear equivalence and `f` an `R`-linear map.
- **Clause B** quantifies commutative rings `R` and `M` with
  `[Algebra R M]`; an index type `ι`; rings `N i`, not necessarily
  commutative, with `[∀ i, Algebra R (N i)]`; `R`-submodules
  `L : ∀ i, Submodule R (N i)`, not necessarily subrings; a filter `ℱ`; and
  `[Module.Flat R M]` and `[Module.FinitePresentation R M]`. With
  `e := lTensorEquivLeft R M N L ℱ` and `f := lTensorLeft R M N ℱ L`, it
  asserts `e.symm (f x) = x` for every `x : M ⊗[R] (Πʳ i, [N i, L i]_[ℱ])`,
  and `f (e.symm y) = y` for every
  `y : Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ]`. Note the
  differing explicit orders: `R M N L ℱ` for the equivalence and
  `R M N ℱ L` for the map. Here `e` is an `M`-linear equivalence and `f` an
  `M`-linear map, where `M` acts on the tensor products through the left
  factor.

The codomain coordinate submodules are the published images.
`rangeLTensor R M N L i` is the range of the `R`-linear map
`LinearMap.lTensor M (L i).subtype : M ⊗[R] L i → M ⊗[R] N i`.
`rangeLTensorLeft R M N L i` is the range of
`TensorProduct.AlgebraTensorModule.lTensor _ _ (L i).subtype`, recorded as
an `M`-submodule. The proof does not replace them by `M ⊗[R] L i`.

## Why each forward map is the equivalence's forward function

The published module `Langlands.LinearAlgebra.RestrictedProduct.TensorEquiv`
defines

```lean
lTensorEquiv R M N ℱ L :=
  LinearEquiv.ofBijective (lTensor R M N ℱ L) (...)
lTensorEquivLeft R M N L ℱ :=
  LinearEquiv.ofBijective (lTensorLeft R M N ℱ L) (...)
```

where the omitted arguments are bijectivity proofs taken from the published
theorem `tensorRestrictedProductComparison_proof`. In Mathlib,
`LinearEquiv.ofBijective f hf` is
`(LinearEquiv.ofInjective f hf.injective).trans (LinearEquiv.ofTop _ _)`,
and its `simp` lemma `LinearEquiv.ofBijective_apply` states
`ofBijective f hf x = f x` with the proof `rfl`
(`Mathlib/Algebra/Module/Submodule/Equiv.lean:182–191` at the pinned
commit). Hence, in each clause, `f x` and `e x` are definitionally equal for
every `x` in the tensor domain. The proof records this as the local fact

```lean
have hf : ∀ x, f x = e x := fun _ ↦ rfl
```

which Lean accepts by unfolding the let-bound names `e` and `f`, the
published definition of the equivalence and `ofBijective`. No inverse law,
bijectivity statement or replacement equivalence is assumed: `e.symm` is
the actual inverse of the published equivalence.

## The proof

The proof first splits the conjunction with `constructor`.

For clause A it introduces all quantified data and instances,
`R M _ _ _ _ _ ι N _ _ ℱ L`, followed by the let-bound names `e` and `f`.
After proving `hf`, it gives the two identities as an anonymous pair:

1. For arbitrary `x`, rewriting the goal `e.symm (f x) = x` with `hf` gives
   `e.symm (e x) = x`. This is Mathlib's `LinearEquiv.symm_apply_apply`,
   applied to `e` and `x`.
2. For arbitrary `y`, rewriting the goal `f (e.symm y) = y` with `hf` at
   the element `e.symm y` gives `e (e.symm y) = y`. This is Mathlib's
   `LinearEquiv.apply_symm_apply`, applied to `e` and `y`.

Both Mathlib laws are stated at
`Mathlib/Algebra/Module/Equiv/Defs.lean:353–359` of the pinned commit.

For clause B it introduces `R M _ _ _ ι N _ _ L ℱ _ _`, in the binder order
of that clause, and then `e` and `f`. The same three steps apply verbatim:
`hf` holds by `rfl`, and the two rewritten goals are closed by
`e.symm_apply_apply x` and `e.apply_symm_apply y`. These are now the laws of
the `M`-linear equivalence `lTensorEquivLeft R M N L ℱ`, and the
equalities hold in the restricted product with coordinate submodules
`rangeLTensorLeft R M N L i`.

The identities are equalities of arbitrary elements of the tensor product
and of the restricted product. There is no reduction to pure tensors and no
coordinatewise argument. No product, direct-limit or restricted-product
comparison is reproved.

## Scope

Every index type, filter and family of submodules is allowed in both
clauses, including an empty index type, the bottom filter and principal
filters. There is no `NeBot`, finite-index, cofinite-filter, freeness,
projectivity or number-field hypothesis. The only scalar hypotheses are
those of the target listed above.

This module adds no definition, map, submodule, equivalence, instance or
helper lemma. It does not edit the statement pair or any imported pair.

## Checks

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), `lean_check` built the
module with no errors or warnings. Inspection of
`RestrictedProduct.tensorEquivInverseLaws_proof` reports a theorem with
level parameters `[uR, uM, uι, uN]`, depending only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. A separate private diagnostic printed
the full unapplied type with universes shown,
`RestrictedProduct.tensorEquivInverseLaws_proof.{uR, uM, uι, uN} :
RestrictedProduct.TensorEquivInverseLaws.{uR, uM, uι, uN}`, and applied the
theorem at the distinct universes `0, 1, 2, 3`. The module uses no `sorry`,
`admit` or new axiom. These development checks are not independent
acceptance; the exact-target check is part of validation.

## Provenance

The equivalences come from Imperial FLT, commit
`923d45174c500aa1d994ba973bac38ea39eacbf7`,
[`FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean`](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean#L234-L244),
lines 234–244, with module hypotheses at lines 28–32 and 102 and algebra
hypotheses at lines 240–244. That file is copyright 2025 Matthew Jasper,
author Matthew Jasper, under Apache-2.0; it is retained in the registered
snapshot `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) with
SHA-256 `a750850ebe7c7bc80532fafbc865067df53f9686be9bc7a60d99961c158b4e9b`.
The upstream license is retained at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The original constructs the equivalences but does not state or prove the
grouped inverse-law proposition. This module copies none of its code; it
uses the Library's published adaptations by Lean name, and the attribution
in the Lean header records this provenance.
