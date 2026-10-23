# Solvability of actual finite p-adic inertia groups

Author: Worker 109.

`Langlands.Ramification.Padic.FiniteInertiaSolvability.{u,v}` is the following
proposition, with independent universes `u` and `v`:

```lean
∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{u} p) (L : PadicField.{v} p)
  [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]
  [IsGalois K.Carrier L.Carrier],
  Group.IsSolvable
    (Langlands.Ramification.Padic.inertia L.canonicalTopologicalData K.Carrier)
```

It states that the actual inertia subgroup of every finite Galois extension
`L/K` of p-adic fields is solvable. The specified algebra makes `L.Carrier`
an extension of `K.Carrier`, and the scalar tower requires its inclusion to
respect the two specified `Padic p` algebra structures. Both `PadicField`
objects already include finite-dimensionality over `Padic p`; consequently
`L.Carrier` is finite-dimensional over `K.Carrier`. No separate relative-degree
or finiteness hypothesis is needed. The trivial extension is included.

## Existing constructions

Put `T := L.canonicalTopologicalData`. This is the existing canonical
local-field realization constructed from the spectral norm extending the
p-adic norm; the statement does not quantify over a realization certificate.
Its actual valuation ring is `T.Integers`, and its residue field is
`T.ResidueField`, the quotient by the maximal ideal.

The imported module `Langlands.LocalFactor.Ramification.Galois` defines
`integerAutomorphism T K.Carrier` by restricting a `K.Carrier` algebra
automorphism of `L.Carrier` to `T.Integers`. The restricted automorphisms form
`integerAutHom T K.Carrier`. Applying the residue-field functor gives

```lean
residueHom T K.Carrier :
  (L.Carrier ≃ₐ[K.Carrier] L.Carrier) →* RingAut T.ResidueField
```

The subgroup `inertia T K.Carrier` is exactly this homomorphism's kernel.
Thus its elements are the actual field automorphisms inducing the identity
on every residue class. The conclusion uses this subgroup's inherited group
structure. Mathlib's `Group.IsSolvable` means that its derived series is
trivial at some natural-number index.

The same imported module constructs `lowerRamificationGroup T K.Carrier i`
by requiring `σ(x) - x` to lie in the `(i+1)`st power of the maximal ideal for
every `x : T.Integers`. Its theorem `lowerRamificationGroup_zero` identifies
the zeroth lower group with this inertia kernel. It also proves normality,
antitonicity and `exists_lowerRamificationGroup_eq_bot`. The present statement
introduces no new field, action, inertia group, or filtration.

## Correspondence with the original source

The source is Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, Graduate Texts in Mathematics 67, Springer, 1979:

- Chapter IV, §1, Proposition 1, printed p.62 (PDF p.69), identifies `G₀` with
  inertia and records the normal, decreasing, eventually trivial filtration.
  The corollary to Proposition 2, printed p.63 (PDF p.70), identifies inertia
  as the Galois group over the maximal unramified intermediate extension.
- Chapter IV, §2, Propositions 5–6, printed p.66 (PDF p.73), give the
  uniformizer test and identify the unit-filtration quotients with the
  multiplicative residue group at level zero and additive residue groups
  at positive levels.
- Chapter IV, §2, Proposition 7, printed p.67 (PDF p.74), embeds
  `Gᵢ/Gᵢ₊₁` into the corresponding unit-filtration quotient using `σ(π)/π`.
  Corollary 1 gives cyclic tame quotient of order prime to the residue
  characteristic; Corollary 3, printed pp.67–68 (PDF pp.74–75), gives the
  elementary abelian positive quotients and the wild p-group.
- Chapter IV, §2, Corollary 5, printed p.68 (PDF p.75), asserts that `G₀`
  is solvable. This proposition specializes its first assertion to finite
  extensions of `Padic p`, using the actual kernel and canonical realization
  above. Its separate conclusion about the full Galois group is not part
  of this statement.

Serre's `G` corresponds to `L.Carrier ≃ₐ[K.Carrier] L.Carrier`, his integer
ring and residue field to `T.Integers` and `T.ResidueField`, and his `G₀` to
`inertia T K.Carrier`. The finite p-adic setting has finite residue fields,
so the separability conditions used for the source's inertia theory hold.
No total-ramification assumption is introduced by the source's reduction
to the inertia fixed field.

Registered source: `serre-1979-local-fields`.
Retained original: `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
SHA256: `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

## Proof boundary

This file defines a `Prop`; it proves no solvability theorem. Its hypotheses
contain neither solvability nor tame cyclicity, wild p-group structure,
ramification-quotient structure, total ramification, or class-field theory.
A successor proof must establish the exact proposition using the existing
actual objects. Following Serre would require proving the relevant quotient
structure and applying solvability of extensions; another valid route may
prove the needed derived-series bounds directly. None of those proof
ingredients is assumed here.

The separately published `Langlands.PadicField.TotallyRamifiedGaloisSolvability`
and its proof concern an arithmetic total-ramification hypothesis on finite
intermediate extensions. They are distinct from this general finite-inertia
target. This module does not import that proof or add its arithmetic hypothesis.
