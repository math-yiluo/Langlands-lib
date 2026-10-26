# Isomorphisms for actual sheaf tensor powers

This module works for every `X : AlgebraicGeometry.Scheme.{u}` and every
actual module sheaf `P : X.Modules`. All declarations are in
`Langlands.Scheme.Modules`. There are no rank, flatness, quasi-coherence,
affineness, noetherianity, or separatedness assumptions.

The imported `Tensor` interface defines `tensorPow P 0` to be
`structureSheaf X` and `tensorPow P (n + 1)` to be
`tensorObj P (tensorPow P n)`. Thus these are right-associated powers with
a trailing structure-sheaf factor. In particular, `tensorPow P 1` is
`tensorObj P (structureSheaf X)`; the definition `tensorPowOneIso P`
identifies it with `P` by the published `tensorRightUnitor P`.

## Transporting an isomorphism

For `e : P ≅ Q`, `tensorPowIso e n` has type
`tensorPow P n ≅ tensorPow Q n`. At zero it is the identity isomorphism of
the structure sheaf. At a successor, it applies the actual sheaf tensor
bifunctor `tensorFunctor X` to the product isomorphism consisting of `e`
and the preceding power isomorphism. No replacement tensor object or
isomorphism-existence hypothesis is introduced.

The lemma `tensorPowIso_hom` states
`(tensorPowIso e n).hom = tensorPowMap e.hom n` for every natural `n`.
Its proof is induction: both zeroth maps are the identity, and at the
successor the hom of `Functor.mapIso` of a product isomorphism is
`tensorMap` of the two homs. The induction hypothesis identifies the
second hom with the published lower tensor-power map.

## Adding exponents

`tensorPowAddIso P a b` has type
`tensorObj (tensorPow P a) (tensorPow P b) ≅ tensorPow P (a + b)`.
It recurses on `a`. For `a = 0`, the left unitor removes the initial
structure-sheaf factor. For `a + 1`, the published `tensorAssociator`
first changes

```
(P ⊗ P^a) ⊗ P^b  ≅  P ⊗ (P^a ⊗ P^b),
```

where every tensor symbol denotes `tensorObj` and every power denotes
`tensorPow`. Applying `tensorFunctor X` to the identity of `P` and the
recursive addition isomorphism then gives `P ⊗ P^(a + b)`. The arithmetic
equality `(a + 1) + b = (a + b) + 1` identifies the target with the
specified power. This includes both exponents zero and never discards
the trailing unit by definitional equality.

## Multiplying exponents

`tensorPowMulIso P n m` has type
`tensorPow (tensorPow P n) m ≅ tensorPow P (n * m)`.
It recurses on the outer exponent `m`. At zero, both sides are the
structure sheaf and the isomorphism is its identity. At a successor,
the tensor bifunctor applies the recursive isomorphism in the second
factor, giving

```
P^n ⊗ (P^n)^m  ≅  P^n ⊗ P^(n * m).
```

The addition isomorphism gives `P^(n + n * m)`, and natural-number
arithmetic identifies this with `P^(n * (m + 1))`. The construction works
also for `n = 0`; no positive-exponent hypothesis is used.

## Provenance and scope

These are internal categorical constructions derived from the published
modules `Langlands.AlgebraicGeometry.Modules.Tensor` and
`Langlands.AlgebraicGeometry.Modules.TensorCoherenceMaps`. The former
supplies the actual sheafified tensor bifunctor, unitors, tensor powers,
and tensor-power maps; the latter supplies an actual associator by
transport from the localized monoidal tensor. Their Markdown companions
record the underlying sheaf-theoretic provenance. The present module
does not translate an additional literature theorem.

The constructions use Mathlib's `CategoryTheory.Iso.prod` from
`Mathlib/CategoryTheory/Products/Basic.lean` and
`CategoryTheory.Functor.mapIso` from `Mathlib/CategoryTheory/Iso.lean`
in the pinned environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
Only the component hom and inverse of each product isomorphism and its
functorial image are used. No pentagon, triangle, or pullback coherence
result is assumed or asserted by this module. All imported source pairs
are preserved.
