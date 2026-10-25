# Restricted-product tensor comparison and bijectivity targets

`RestrictedProduct.TensorRestrictedProductComparison.{uR, uM, uι, uN}` is a
`def` returning `Prop`. It states three assertions about the canonical maps
imported from `Langlands.LinearAlgebra.RestrictedProduct.Tensor`. It proves
none of them. Its body is `A ∧ (B ∧ C)`, where each clause universally
quantifies its own types, instances, submodules and filter. Thus the hypotheses
needed for bijectivity do not restrict the scalar comparison, and the ring
hypotheses needed for the `M`-linear map do not restrict the general module
assertion.

The four universes are independent: `R : Type uR`, `M : Type uM`,
`ι : Type uι` and `N : ι → Type uN`. Each clause quantifies all these data
at the indicated universes. The declaration has no term parameters. Its
explicit universe order is `uR, uM, uι, uN`.

## The maps and their actual codomains

For any commutative ring `R`, additive commutative group `M` with `Module R M`,
and family of additive commutative groups `N i` with `Module R (N i)`, the
published map is

```lean
lTensor R M N ℱ L :
  M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[R]
    Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ]
```

Here `L i : Submodule R (N i)` and `ℱ : Filter ι` are arbitrary. A restricted
product consists of coordinate families belonging to the specified submodules
for `ℱ`-eventually every index. The submodule `rangeLTensor R M N L i` is
`LinearMap.range (LinearMap.lTensor M (L i).subtype)`: the image of
`M ⊗[R] L i` in `M ⊗[R] N i`. It is an image, without an assumption that
tensoring the inclusion is injective.

When `R` and `M` are commutative rings with `Algebra R M`, and every `N i`
is a ring with `Algebra R (N i)`, the second published map is

```lean
lTensorLeft R M N ℱ L :
  M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[M]
    Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ]
```

The coordinates need only `Ring`, not `CommRing`. The `L i` remain arbitrary
`R`-submodules; no multiplicative closure or `M`-module structure on `L i` or
`N i` is required. `rangeLTensorLeft` is the range of
`TensorProduct.AlgebraTensorModule.lTensor` applied to `(L i).subtype`, as an
`M`-submodule. The action of `M` is on the left tensor factor. In both maps,
the published coordinate formula sends `m ⊗ x` to the family `i ↦ m ⊗ x i`.

Under the algebra hypotheses, the two range submodules have definitionally
equal underlying sets: their defining tensor-inclusion maps have the same
underlying function. The restricted-product carrier uses these sets, so the
two codomain types are definitionally identified after forgetting the scalar
structure. The first clause uses the ordinary function coercion `⇑` and this
identification, just as the original source does. It compares functions into
the actual restricted product, not merely their composites into an unrestricted
product. It assumes no equality of submodules, transport equivalence, or
identification of the image with the unembedded tensor product.

## The three clauses

1. **Scalar comparison.** For all `R`, `M`, `ι`, `N`, `L` and `ℱ` with
   `[CommRing R] [CommRing M] [Algebra R M]`,
   `[∀ i, Ring (N i)] [∀ i, Algebra R (N i)]`, the assertion is
   `⇑(lTensorLeft R M N ℱ L) = lTensor R M N ℱ L`. Lean also coerces the
   right side to its underlying function. This clause has no finite-presentation,
   flatness, or finiteness hypothesis. It restates
   [`coe_lTensorLeft_eq_lTensor`, source lines 93–100](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean#L93-L100).

2. **General `R`-linear bijectivity.** For all `R`, `M`, `ι`, `N`, `L` and
   `ℱ` with `[CommRing R] [AddCommGroup M] [Module R M]`,
   `[Module.FinitePresentation R M] [Module.Flat R M]`, and
   `[∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]`, the assertion is
   `Function.Bijective (lTensor R M N ℱ L)`. Neither `M` nor the coordinates
   need a ring or algebra structure. This restates
   [`lTensor_bijective`, source lines 170–223](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean#L170-L223),
   with the module hypotheses from
   [lines 28–32](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean#L28-L32)
   and finite presentation and flatness from
   [line 102](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean#L102).
   The section variable `S : Set ι` from line 102 does not occur in that
   theorem's type and is not a parameter of this clause.

3. **`M`-linear bijectivity.** For all `R`, `M`, `ι`, `N`, `L` and `ℱ` with
   `[CommRing R] [CommRing M] [Algebra R M]`,
   `[Module.Flat R M] [Module.FinitePresentation R M]`, and
   `[∀ i, Ring (N i)] [∀ i, Algebra R (N i)]`, the assertion is
   `Function.Bijective (lTensorLeft R M N ℱ L)`. This restates
   [`lTensorLeft_bijective`, source lines 225–232](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean#L225-L232).
   Scalar compatibility comes from the specified algebras and the canonical
   map's existing local scalar-tower constructions; no extra scalar-tower
   instance is assumed here.

All three clauses allow every index type, every `R`-submodule family and every
filter, including principal filters and the bottom filter. There is no `Finite ι`,
`NeBot ℱ`, cofinite-filter restriction, freeness, chosen projective structure,
or assumed equivalence or bijectivity. The bijectivity hypotheses are finite
presentation and flatness, preserving the actual source declarations rather
than the shorter phrase “finite flat” in its equivalence docstrings.

## Scope and checking

The only new declaration is the grouped Prop target. The imported nine
canonical-map declarations are unchanged. This module contains no proof of the
comparison or bijectivity assertions, no principal-filter equivalence or
direct-limit construction, and no final `lTensorEquiv` or `lTensorEquivLeft`.
The independent arbitrary-product comparison is neither restated nor assumed.
No topology or norm assertion is made.

A private `lean_check` probe inspected the full unapplied types of all nine
imported declarations, the full expanded grouped target and its universes.
It compiled without errors or warnings. A separate declaration inspection
confirmed `statement_returns_prop = true` and the universe parameters
`uR, uM, uι, uN`. The target depends only on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; it introduces no axiom or
proof hole. These checks establish well-formedness, not proofs of the clauses
or independent semantic acceptance.

## Provenance and modification notice

The original is Matthew Jasper's
`FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean` in
ImperialCollegeLondon/FLT at commit
`923d45174c500aa1d994ba973bac38ea39eacbf7`. The full 259-line source was read
in the registered source `external-lean-reuse-snapshots-2026-10-21`, under
`ImperialCollegeLondon--FLT/source`. Its registered content fingerprint is
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The precise source assertions and their hypothesis locations are linked above.
The surrounding source map is the
[finite-adele base-change audit](../../../notes/reuse/finite-adele-base-change-audit.md),
sections 2–6 and Appendix B; that audit is not acceptance of these assertions.

Worker 288's modifications replace the three original proved declarations by
one Prop definition, move each assertion's hypotheses inside its own universal
quantifiers, make the four independent universes explicit, and import the
published canonical maps and Mathlib's finite-presentation and flatness classes.
The conjunction is internal organization of the three cited assertions, not a
stronger source theorem. The original proofs, auxiliary constructions and final
equivalences are omitted. No compatibility patch (a)–(d) from the audit and no
new elaborator option is required. No Anthropic derivative material is used.

The Lean header retains “Copyright (c) 2025 Matthew Jasper”, “Authors: Matthew
Jasper”, and the Apache-2.0 license notice, with a prominent modification notice.
The original license is already retained at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The source snapshot contains no `NOTICE` file.
