# Tensor products of semisimple representations of abstract groups in characteristic zero

`Langlands.GroupScheme.CharZeroAbstractGroupTensorSemisimpleStatement.{u, v, w₁, w₂}`
is a Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: for every field `k : Type u` with `[CharZero k]`, every
group `G : Type v`, every finite-dimensional `k`-vector space `V : Type w₁`,
every finite-dimensional `k`-vector space `W : Type w₂`, and all
representations `ρ : Representation k G V` and `σ : Representation k G W`,

```text
ρ.IsSemisimpleRepresentation → σ.IsSemisimpleRepresentation →
  (ρ.tprod σ).IsSemisimpleRepresentation
```

In words: if two finite-dimensional representations of an abstract group over
a field of characteristic zero are semisimple, then so is their tensor
product.

Every ingredient is from Mathlib, used without change:

- `Representation k G V` is a monoid homomorphism `G →* (V →ₗ[k] V)`, that
  is, a linear action of the abstract group `G` on `V`. `G` carries no
  topology or algebraic structure beyond being a group.
- `FiniteDimensional k V` and `FiniteDimensional k W` say that `V` and `W`
  are finite-dimensional.
- `ρ.tprod σ : Representation k G (V ⊗[k] W)` is the tensor product
  representation, with `(ρ.tprod σ) g = TensorProduct.map (ρ g) (σ g)`, so
  `g(v ⊗ w) = ρ(g)v ⊗ σ(g)w`.
- `Representation.IsSemisimpleRepresentation ρ` is
  `ComplementedLattice (Subrepresentation ρ)`: every subrepresentation has a
  complementary subrepresentation. A `Subrepresentation ρ` is a `k`-subspace
  of `V` stable under every `ρ g`. Mathlib proves
  `isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`: this is
  equivalent to `IsSemisimpleModule k[G] ρ.asModule`. Through the order
  isomorphism `Subrepresentation.subrepresentationSubmoduleOrderIso` and
  `sSup_simples_eq_top_iff_isSemisimpleModule`, it is equivalent to `V` being
  the sum of its simple subrepresentations, which is the definition of
  semisimplicity used by Milne (Definition 4.15, for algebraic groups).

The universes of `k`, `G`, `V` and `W` are independent.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is Corollary 22.45, printed p. 478 (PDF p. 494), introduced by
"Theorem 22.42 has the following remarkable consequence (Chevalley 1955b,
p. 88).": "Let G be an abstract group, and let (V, r) and (W, s) be
representations of G on finite-dimensional vector spaces V and W over a field
k of characteristic zero. If V and W are semisimple, then so is V ⊗ W." It is
in Section 22c, which begins on printed p. 475 (PDF p. 491) with "In this
section, k is a field of characteristic zero."

Milne does not define semisimplicity separately for representations of an
abstract group. The Lean statement uses the standard notion, which agrees
with the one of Definition 4.15, printed p. 90 (PDF p. 106): "A
representation of an algebraic group is simple if it is ≠ 0 and its only
subrepresentations are 0 and itself. It is semisimple if it is a sum of
simple subrepresentations." Mathlib's `IsSemisimpleRepresentation` is the
complement form; the equivalence with the sum form is recalled above.

The provenance is derived for these reasons:

- Representations are Mathlib's `Representation k G V` on abstract vector
  spaces, and semisimplicity is Mathlib's complement form of the definition.
- The universes of `k`, `G`, `V` and `W` are arbitrary and independent. This
  is a formalization convention.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists for
Chapter 22 only corrections on pp. 468, 469, 473 and 480, and for Chapter 4
only p. 95 (proof of 4.29). For Chapter 1 it corrects the statement of 1.45
(p. 20) and Definition 1.48 of the Zariski closure (p. 21): "Let G be an
algebraic group over k and S a subgroup of G(k). The unique algebraic
subgroup H of G such S is schematically dense in H is called the Zariski
closure of S in G." The Zariski closure is used in Milne's proof of 22.45,
not in its statement. The errata snapshot of 2026-11-04 for the 2022 reprint
(source ID `milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has for
p. 478 only the entry on the proof of 22.42. None changes the statements of
4.15 or 22.45.

## For the proof (not part of this module)

The statement is proved as `charZeroAbstractGroupTensorSemisimple`
(`GroupScheme/Reductive/AbstractGroupTensorSemisimpleProof`).

Milne's proof, printed p. 478 (PDF p. 494): "We may replace G with its Zariski
closure G′ in GL_V × GL_W – as G is dense in G′ (as a scheme 1.9), the two
have the same invariant subspaces in any representation. Thus we may suppose
that G is a group variety over k, and apply the previous corollary."

Spelled out: let `S` be the image of `G` in `(GL_V × GL_W)(k)` and `G′` its
Zariski closure, an affine algebraic group over `k` with `S` schematically
dense in it (corrected Definition 1.48). The representations `V`, `W` and
`V ⊗ W` of `G` factor through `S` and extend to representations of `G′`
(the projections to `GL_V` and `GL_W`, and their tensor product). A subspace
is stable under `G′` if and only if it is stable under `S`, because its
stabilizer is a closed subgroup and `S` is dense. So `V` and `W` are
semisimple as `G′`-representations, Corollary 22.44 makes `V ⊗ W` semisimple
as a `G′`-representation, and hence as a representation of `G`. A Lean
statement of 22.44 for matrix representations is the second conjunct of
`CharZeroSemisimpleRepresentationIdentityComponentStatement`
(`GroupScheme/Reductive/SemisimpleRepresentationIdentityComponentStatement`),
proved in `GroupScheme/Reductive/SemisimpleRepresentationIdentityComponentProof`;
after choosing bases of `V` and `W`, the tensor
product representation there is the Kronecker product `ρ.tensor σ`.
