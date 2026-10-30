# Restricted-product tensor equivalences

This module packages the published canonical tensor maps as linear
equivalences:

```
M ⊗[R] Πʳ i, [N i, L i]_[ℱ]  ≃  Πʳ i, [M ⊗[R] N i, (image of M ⊗[R] L i)]_[ℱ],
m ⊗ x  ↦  (i ↦ m ⊗ x i).
```

Here `M` is a finitely presented flat `R`-module. There is an `R`-linear
version `lTensorEquiv` and an `M`-linear version `lTensorEquivLeft`. Each
has a `simp` lemma giving its value on a pure tensor. All four declarations
are in the namespace `RestrictedProduct`.

The module imports only `Langlands.LinearAlgebra.RestrictedProduct.TensorProof`.
That module provides the theorem
`RestrictedProduct.tensorRestrictedProductComparison_proof`. Through its own
imports it also provides the canonical maps `lTensor` and `lTensorLeft`, the
image submodules `rangeLTensor` and `rangeLTensorLeft`, and the formulas
`lTensor_tmul` and `lTensorLeft_tmul`, all from
`Langlands.LinearAlgebra.RestrictedProduct.Tensor`. None of these modules is
edited. This module defines no helper declaration.

## Universes and arbitrary data

The module declares `universe uR uM uι uN`, with `R : Type uR`,
`M : Type uM`, `ι : Type uι` and `N : ι → Type uN`. These four universes are
independent, and every declaration has the universe parameters
`.{uR, uM, uι, uN}` in this order. This is the order of the universe
parameters of the target `RestrictedProduct.TensorRestrictedProductComparison`
and of its proof.

In every declaration the index type `ι`, the family of submodules
`L : ∀ i, Submodule R (N i)` and the filter `ℱ : Filter ι` are arbitrary.
There is no finite-index, nonempty-index, cofinite-filter, `NeBot`, freeness,
projectivity or number-field hypothesis. A private check built both
equivalences at the bottom filter `⊥`, and `lTensorEquiv` also at a principal
filter `Filter.principal S`. No equivalence or bijectivity is taken as a
hypothesis.

## The codomains

The codomains are the restricted products used by the published maps. Their
coordinate subgroups are image submodules:

- `rangeLTensor R M N L i` is the `R`-submodule
  `LinearMap.range (LinearMap.lTensor M (L i).subtype)` of `M ⊗[R] N i`. This
  is the image of `M ⊗[R] L i` under the map induced by the inclusion
  `L i → N i`.
- `rangeLTensorLeft R M N L i` is the range of
  `TensorProduct.AlgebraTensorModule.lTensor _ _ (L i).subtype`. This is the
  same image, recorded as an `M`-submodule, where `M` acts on `M ⊗[R] N i`
  through the left factor.

These codomains are not replaced by `M ⊗[R] L i`. Under flatness the
inclusion-induced map `M ⊗[R] L i → M ⊗[R] N i` is injective, so each image is
isomorphic to `M ⊗[R] L i`. That isomorphism is not used or stated here.

## `lTensorEquiv`

```
lTensorEquiv R M N ℱ L :
  M ⊗[R] Πʳ i, [N i, L i]_[ℱ] ≃ₗ[R]
    Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ]
```

The hypotheses, in binder order, are:

- `R : Type uR` and `M : Type uM` (explicit), with `[CommRing R]`,
  `[AddCommGroup M]` and `[Module R M]`;
- an implicit index type `ι : Type uι`;
- explicit coordinates `N : ι → Type uN`, with `[∀ i, AddCommGroup (N i)]`
  and `[∀ i, Module R (N i)]`;
- an explicit filter `ℱ : Filter ι` and explicit submodules
  `L : ∀ i, Submodule R (N i)`;
- `[Module.FinitePresentation R M]` and `[Module.Flat R M]`.

So the explicit arguments come in the source order `R M N ℱ L`. These are the
section variables of the source (lines 28–32), followed by the two instance
variables of line 102. Neither `M` nor any `N i` needs a ring or algebra
structure.

The definition is

```
LinearEquiv.ofBijective (lTensor R M N ℱ L)
  (tensorRestrictedProductComparison_proof.{uR, uM, uι, uN}.2.1 R M ι N L ℱ)
```

The published target `TensorRestrictedProductComparison` is a conjunction
`A ∧ (B ∧ C)`. Clause `A` compares underlying functions, clause `B` is
bijectivity of `lTensor` for modules, and clause `C` is bijectivity of
`lTensorLeft` for algebras. Each clause quantifies its own data. So
`tensorRestrictedProductComparison_proof.2.1` is clause `B`. Its explicit
arguments are `R M ι N L ℱ`, and its instance arguments are found from the
local instances. Applied as above, it is a proof of
`Function.Bijective (lTensor R M N ℱ L)`.

Mathlib's `LinearEquiv.ofBijective f hf` is
`(LinearEquiv.ofInjective f hf.injective).trans (LinearEquiv.ofTop _ _)`.
Its forward map is `f`, and its inverse is obtained noncomputably, so the
definition is `noncomputable`. A private check confirmed that
`(lTensorEquiv R M N ℱ L).toLinearMap = lTensor R M N ℱ L` holds by `rfl`. So
the forward linear map is exactly the published `lTensor`.

## `lTensorEquivLeft`

```
lTensorEquivLeft R M N L ℱ :
  M ⊗[R] Πʳ i, [N i, L i]_[ℱ] ≃ₗ[M]
    Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ]
```

The hypotheses, in binder order, are:

- `R : Type uR` and `M : Type uM` (explicit), with `[CommRing R]`,
  `[CommRing M]` and `[Algebra R M]`;
- an implicit index type `ι : Type uι`;
- explicit coordinate rings `N : ι → Type uN`, with `[∀ i, Ring (N i)]` and
  `[∀ i, Algebra R (N i)]`;
- explicit submodules `L : ∀ i, Submodule R (N i)` and an explicit filter
  `ℱ : Filter ι`;
- `[Module.Flat R M]` and `[Module.FinitePresentation R M]`.

The explicit arguments come in the source order `R M N L ℱ`, which differs
from the order `R M N ℱ L` of `lTensorLeft`. These are the hypotheses of
source lines 240–244. The coordinate rings `N i` need not be commutative, and
the `L i` are `R`-submodules, not subrings. A private check built the
equivalence with every `N i` the noncommutative ring
`Matrix (Fin 2) (Fin 2) R`. The domain is an `M`-module through the left
tensor factor. The codomain is an `M`-module by Mathlib's restricted-product
`Module` instance, since each `rangeLTensorLeft R M N L i` is an
`M`-submodule.

The definition is

```
LinearEquiv.ofBijective (lTensorLeft R M N ℱ L)
  (tensorRestrictedProductComparison_proof.{uR, uM, uι, uN}.2.2 R M ι N L ℱ)
```

Here `tensorRestrictedProductComparison_proof.2.2` is clause `C`, applied to
the explicit arguments `R M ι N L ℱ`. It proves
`Function.Bijective (lTensorLeft R M N ℱ L)`. A private check confirmed that
`(lTensorEquivLeft R M N L ℱ).toLinearMap = lTensorLeft R M N ℱ L` holds by
`rfl`.

## Pure-tensor coordinate formulas

Both formulas are `simp` lemmas:

```
lTensorEquiv_tmul R M N ℱ L m f i :
  lTensorEquiv R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i)

lTensorEquivLeft_tmul R M N L ℱ m f i :
  lTensorEquivLeft R M N L ℱ (m ⊗ₜ f) i = m ⊗ₜ (f i)
```

Here `m : M`, `f : Πʳ i, [N i, L i]_[ℱ]` and `i : ι`, and the other
hypotheses are those of the corresponding equivalence. The explicit arguments
come in the source orders `R M N ℱ L m f i` and `R M N L ℱ m f i`.

Each proof unfolds the equivalence and rewrites with Mathlib's `simp` lemma
`LinearEquiv.ofBijective_apply`, which states `ofBijective f hf x = f x`.
This leaves the formula for the published forward map, which is closed by
rewriting with the published `lTensor_tmul` or `lTensorLeft_tmul`. No
transparency option is needed.

## What this module does not contain

- No proof of injectivity, surjectivity or bijectivity. Both bijectivity
  facts are taken from the published proof.
- No coordinate formula for the inverse maps. The inverses are the `.symm`
  of the two equivalences, obtained noncomputably through
  `LinearEquiv.ofBijective`.
- No inverse laws. The published Prop
  `RestrictedProduct.TensorEquivInverseLaws` in
  `Langlands.LinearAlgebra.RestrictedProduct.TensorEquivStatement` states
  both inverse identities between each canonical forward map and the `.symm`
  of the corresponding equivalence. The published theorem
  `RestrictedProduct.tensorEquivInverseLaws_proof` in
  `Langlands.LinearAlgebra.RestrictedProduct.TensorEquivProof` proves it.
- The source declarations `coe_lTensorLeft_eq_lTensor`,
  `tmulEquivRangeLTensor`, `lTensorPrincipalEquiv`,
  `lTensorPrincipalEquiv_tmul`, `lTensor_bijective` and
  `lTensorLeft_bijective` (source lines 93–232) are not reproduced. Their
  mathematical content is either covered by the published comparison proof
  or not needed here.
- No topology, norm, principal-filter or direct-limit construction, and no
  number-field specialization.

## Checks

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) built the module
with no errors or warnings. The full unapplied types of all four declarations
were inspected with universes shown, and the signatures above follow them. All
four declarations depend only on `propext`, `Classical.choice` and
`Quot.sound`. The module has no `sorry`, `admit` or new axiom.

## Provenance and modification notice

The source is ImperialCollegeLondon/FLT at commit
`923d45174c500aa1d994ba973bac38ea39eacbf7`, retained in registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`ImperialCollegeLondon--FLT/source`. The file
[`FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean`](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean#L234-L257)
has SHA-256
`a750850ebe7c7bc80532fafbc865067df53f9686be9bc7a60d99961c158b4e9b`. It is
copyright 2025 Matthew Jasper, author Matthew Jasper, under Apache-2.0. The
adapted lines are:

- section variables 28–32 and the instance variables of line 102;
- `lTensorEquiv` 234–237 and `lTensorEquivLeft` 239–244;
- `lTensorEquiv_tmul` 246–249 and `lTensorEquivLeft_tmul` 251–257.

The original copyright, license and author header is retained in the Lean
file. The upstream root Apache-2.0 `LICENSE` is retained at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The source snapshot contains no `NOTICE` file and no errata file.

Worker 217 made this adaptation. Worker 98's task specification chose the
construction from `LinearEquiv.ofBijective` and the published proof. Worker
217's modifications are:

- the bijectivity proofs are taken from the second and third clauses of the
  published `RestrictedProduct.tensorRestrictedProductComparison_proof`.
  The source uses its own `lTensor_bijective` (lines 170–225), a direct-limit
  argument over principal filters, and `lTensorLeft_bijective` (lines
  227–232);
- the four universes are named explicitly instead of `Type*`;
- the source section variable `S : Set ι` of line 102, unused by these
  declarations, is dropped;
- the `module`/`public import`/`@[expose] public section` keywords are
  replaced by a plain import, following the Library convention;
- the docstrings say "finitely presented flat" instead of "finite flat", and
  the docstring of `lTensorEquivLeft` names `lTensorLeft` instead of
  `lTensor`;
- `lTensorEquiv_tmul` is proved by rewriting with
  `LinearEquiv.ofBijective_apply` and `lTensor_tmul` instead of `rfl`, and
  `lTensorEquivLeft_tmul` by rewriting with `LinearEquiv.ofBijective_apply`
  and `lTensorLeft_tmul` instead of `simp`.

The declaration names, the namespace, hypotheses, binder orders, statement
types and forward maps are otherwise unchanged. None of the audit's
compatibility patches (a)–(d) applies to these lines, and no Anthropic
derivative code is used. The public audit
[finite-adele base change](../../../notes/reuse/finite-adele-base-change-audit.md),
sections 2–6 and Appendix B, describes the surrounding source closure.
