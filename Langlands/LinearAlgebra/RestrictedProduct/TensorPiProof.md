# Tensoring a finitely presented module with an arbitrary product: proof

Author of this adaptation: Worker 146. The finite-presentation diagram argument
is adapted from Madison Crim's Imperial FLT source cited below.

## Exact theorem and hypotheses

The module imports the unchanged Library statement
`Langlands.LinearAlgebra.RestrictedProduct.TensorPiStatement` and proves:

```lean
theorem RestrictedProduct.tensorPiComparison_proof.{uR, uM, uι, uN} :
  RestrictedProduct.TensorPiComparison.{uR, uM, uι, uN}
```

The theorem has no term parameters outside its target. Unfolding that target
gives precisely

```lean
∀ (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]
  [Module.FinitePresentation R M] {ι : Type uι} (N : ι → Type uN)
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)],
  Function.Bijective (TensorProduct.piRightHom R R M N)
```

Thus the canonical linear map from `M ⊗[R] (∀ i, N i)` to
`∀ i, M ⊗[R] N i` is bijective. It sends `m ⊗ f` to `i ↦ m ⊗ f i`,
by Mathlib's `TensorProduct.piRightHom_tmul`. The universes of `R`, `M`,
`ι` and `N i` are independent. The index type may be infinite or empty.
No flatness, projectivity, freeness of `M`, or finiteness of any `N i`
is assumed. The theorem applies as `tensorPiComparison_proof R M N`.

## Implemented argument

There is one private helper, `piRightHom_fin_bijective`, proving the comparison
for `M = Fin n → R`. This is exactly the special case used at the two free
terms of a finite presentation. It is an internal proof lemma, not a separately
exported finite-free API or a new equivalence definition.

For any module `P`, Mathlib's tensor commutativity equivalence followed by
`TensorProduct.piScalarRight R R P (Fin n)` identifies
`(Fin n → R) ⊗[R] P` with `Fin n → P`. On pure tensors the map sends
`x ⊗ p` to `j ↦ x j • p`. The helper uses this construction separately for
`P = ∀ i, N i` and for each `P = N i`. Keeping these as separate local terms
allows their different universe levels.

The local linear equivalence `flip`, whose underlying equivalence is
`Equiv.piComm`, exchanges the indices in
`Fin n → ∀ i, N i` and `∀ i, Fin n → N i`. Composing the first scalar tensor
equivalence, this index exchange, and the coordinatewise inverses of the
second equivalences gives a local equivalence `E` with the desired source
and target. `TensorProduct.ext'` reduces equality of its linear map with
`piRightHom` to pure tensors. After applying the injective coordinate
scalar tensor equivalence, both sides send `(x, y)` to
`j ↦ x j • y i`. Simplification and definitional equality prove this.
The bijectivity of `E` therefore gives the helper's conclusion.
Only `Fin n` is required to be finite in this argument; `ι` stays arbitrary.

For the main theorem, `Module.FinitePresentation.exists_fin' R M` supplies
natural numbers `n, m` and linear maps

```text
R^m --f--> R^n --g--> M --> 0
```

with `g` surjective and `Function.Exact f g`. The implementation names the
three vertical comparison maps `i₁`, `i₂`, `i₃` and the horizontal tensor
maps `f₁`, `f₂`, `g₁`, `g₂` in the diagram

```text
R^m ⊗ (Π i, N i) --f₁--> R^n ⊗ (Π i, N i) --f₂--> M ⊗ (Π i, N i) --> 0
        | i₁                    | i₂                    | i₃
        v                       v                       v
Π i, (R^m ⊗ N i) --g₁--> Π i, (R^n ⊗ N i) --g₂--> Π i, (M ⊗ N i) --> 0.
```

All tensors are over `R`. The top arrows are `f.rTensor` and `g.rTensor`.
The bottom arrows apply those maps at each coordinate, expressed as
`LinearMap.pi` of maps composed with `LinearMap.proj`. Both squares commute:
`TensorProduct.ext'`, the pure-tensor formulas and function extensionality
reduce each square to the same pure tensor at each coordinate.

`TensorProduct.rTensor_exact` proves exactness of the top row at its middle
term and exactness of the corresponding row at every coordinate below.
`LinearMap.rTensor_surjective` proves surjectivity of the second top map
and of each coordinate's second map. For the bottom row's exactness,
the proof chooses a preimage at each coordinate of an element in the kernel;
the reverse direction follows by applying coordinatewise exactness.
The same coordinatewise choice establishes surjectivity of `g₂`.
These choices explain the use of classical choice, including for infinite
products. They require no uniform finite-support condition on the product.

Finally, `LinearMap.bijective_of_surjective_of_bijective_of_right_exact`
applies to these two right-exact rows. The private helper supplies
surjectivity of `i₁` and bijectivity of `i₂`; the conclusion is bijectivity
of the literal canonical map `i₃ = piRightHom R R M N`.

## Reuse and source attribution

The originating source is Madison Crim,
[`FLT/DedekindDomain/FiniteAdeleRing/TensorPi.lean`](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorPi.lean),
ImperialCollegeLondon/FLT commit `923d45174c500aa1d994ba973bac38ea39eacbf7`,
Copyright (c) 2025 Madison Crim, Apache-2.0. Its complete 275 lines were read.
It is retained under `ImperialCollegeLondon--FLT/source` in registered source
`external-lean-reuse-snapshots-2026-10-21`, whose content fingerprint is
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The retained file's verified SHA-256 is
`baf10f3f6816d33871de201c671e12c75a5e6f8b5c761d3d23965ebcdc01c6e5`.
No source-specific errata file was present in the Library.

The source's `tensorPiEquivPiTensor'` at lines 199–270, under hypotheses
at lines 182–184, proves this canonical bijectivity and packages it with
`IsTensorProduct.equiv`. Its diagram and coordinatewise exactness argument
are the basis of the main proof here. The implementation makes these changes:

- Mathlib's `Module.FinitePresentation.exists_fin'` replaces source
  `Module.FinitePresentation.exists_fin_exact` at lines 35–54. Its output
  lists the surjection before the relations map; the proof unpacks it in
  that order.
- The one private finite-rank helper above replaces source lines 59–175:
  the direct-sum exchange, chosen-basis and finitely supported function
  constructions are unnecessary for the two modules `Fin m → R` and
  `Fin n → R` supplied by the presentation.
- Mathlib's right-exact form of the five lemma replaces the source's
  five-term version. The two zero modules and their identity maps disappear.
- Every vertical map is Mathlib's `piRightHom`; its pure-tensor formula
  directly proves the commutative squares. Coordinatewise preimages use
  the `choose` tactic instead of explicit `Classical.choose` terms.
- The theorem proves the existing proposition, with four explicit independent
  universe names. No final equivalence or equivalence formula is introduced.
  Source `module`, `public import` and `@[expose] public section` boilerplate
  is replaced by ordinary project imports.

The Lean file retains the source header and a prominent modification notice.
The upstream license is already published at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The source snapshot has no `NOTICE` file. No Anthropic derivative code is used.
None of the wider audit's patches (a)–(d) is relevant to this module.
The public [finite-adele audit](../../../notes/reuse/finite-adele-base-change-audit.md),
sections 2–6 and Appendix B, supplied the source map and attribution guidance.

The reused Mathlib APIs are from pin
`5ed2965256430c3649e86755f9576b54eca72435`:
`Algebra/Module/FinitePresentation.lean:93–102`,
`LinearAlgebra/TensorProduct/Pi.lean:136–173`, and
`Algebra/FiveLemma.lean:251–263`, together with tensor right exactness,
linear-map extensionality and product linear equivalences. All are imported
through the statement module and `Mathlib.Algebra.FiveLemma`.

## Checks and scope

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0),
`lean_check` diagnostic `ba79adc8-5f57-4e71-8773-855380e2996b` built the
proof with zero errors and zero warnings. Declaration inspection reports
kind `theorem`, universe parameters `uR, uM, uι, uN`, and only
`propext`, `Classical.choice`, and `Quot.sound`. The exact unapplied type
has fingerprint `bf9001e25f4bc5559e52a74a55f8e1ee0d0813ab438adceaffe448a40f5c31ae`.
Private diagnostic `b0e9aa9c-1fe7-4413-aacd-5ec41efe4951` prints the full
unapplied theorem type and checks its specialization to four distinct
levels `{0, 1, 2, 3}`. It also prints the same axiom list.
These are development checks; independent semantic review, official
exact-target validation and publication are separate requirements.

The imported statement's Lean/Markdown pair is unchanged. This module proves
only the arbitrary-product bijectivity target. Restricted-product maps,
principal-filter equivalences, direct limits, inverse laws, topology,
number-field specialization and norms are outside this proof.
