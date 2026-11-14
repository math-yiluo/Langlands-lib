# Finite Galois full faithfulness for groups of multiplicative type: statement

Worker 3483.

`Langlands.GroupScheme.MultiplicativeTypeGaloisFullFaithfulnessStatement.{u}`
is a proposition definition. This module states the result; its proof is a
separate obligation.

## Mathematical meaning

Let `L/k` be a finite Galois extension of fields in universe `u`. Let `T` and
`T'` be actual commutative group schemes over `Spec k`. Suppose that there are
finitely generated abelian groups `M`, `M'` and isomorphisms of commutative
group schemes

```text
i  : T_L  ≅ D_L(M),
i' : T'_L ≅ D_L(M').
```

Here `T_L` is `(CommGroupScheme.baseChange (algebraBaseMap k L)).obj T`,
and `D_L(M)` is `Diagonalizable.groupScheme (CommRingCat.of L) M`.
These hypotheses specify that this particular extension splits both groups.
They retain the actual groups and their descent data.

Write `X(T_L) = characterLattice T_L`. Its elements are actual group-scheme
homomorphisms to `𝔾_m,L`, with their additive group law. For every additive map

```text
F : X(T'_L) →+ X(T_L),
```

the statement asserts the equivalence of:

1. For every `σ : L ≃ₐ[k] L` and every character `χ` of `T'_L`,
   `F (σ χ) = σ (F χ)`. Both actions are the existing
   `characterLattice.galoisRepresentation k L`, obtained from canonical
   transport of the base changes of the actual ground-field groups.
2. There exists exactly one group-scheme homomorphism `a : T ⟶ T'` such
   that `a_L ≫ χ = F χ` for every character `χ` of `T'_L`.

The order of composition makes the character map contravariant:
`a : T ⟶ T'` induces `X(T'_L) →+ X(T_L)`. The equality in condition 2
is equality of actual group-scheme morphisms, hence applies on every test
scheme, including nonreduced tests. Uniqueness is among all ground-field
homomorphisms with this character pullback.

The two implications together express full faithfulness at a fixed common
finite Galois splitting field. Equivariant maps are realized uniquely, and
the character pullback of a ground-field homomorphism is equivariant.

## Hypotheses and scope

The extension assumptions are exactly `[Field k] [Field L] [Algebra k L]`,
`[FiniteDimensional k L]` and `[IsGalois k L]`. The module assumptions are
`[AddCommGroup M] [AddGroup.FG M]` and the corresponding assumptions on `M'`.
The chosen isomorphisms occur as hypotheses; no compatibility with separate
chosen actions on `M` or `M'` is needed, since equivariance uses the intrinsic
actions on the actual character groups.

Torsion is allowed, including `p`-torsion in characteristic `p`. There is no
freeness, smoothness, connectedness, positive-rank or characteristic
restriction. In particular, nonsmooth diagonalizable groups such as `μ_p`
remain within the scope. The notation `characterLattice` here denotes the
character group and does not assert that it is free.

The statement supplies the homomorphism comparison for given groups split by
`L`. It does not construct a categorical anti-equivalence or a realizing
group from a Galois module, and it does not state compatibility with short
exact sequences or implement an infinite absolute Galois action.

## Source and derived formulation

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field* (2017), registered as
`milne-2017-algebraic-groups`, source SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The relevant locations are:

- Lemma 12.4 and its following evaluation description, printed p.232
  (PDF p.248): the characters of `D(M)` identify with `M`, by evaluation
  at elements of `M`.
- Theorem 12.9(a) and its proof, printed pp.233–234 (PDF pp.249–250):
  the diagonalizable construction is a contravariant equivalence over a
  field, with homomorphisms given by maps of character groups.
- Theorem 12.23 and its proof in §12.g, printed p.240 (PDF p.256), with
  the Galois-action setup on printed p.239 (PDF p.255): the character
  functor is a contravariant equivalence for groups of multiplicative
  type and finitely generated continuous absolute Galois modules.
- The proof of Theorem 12.25, printed p.240 (PDF p.256), explicitly
  computes homomorphisms as invariants over a common finite Galois
  splitting extension.

This is a **derived finite-level full-faithfulness formulation** of
Theorem 12.23, rather than a transcription of the entire equivalence.
The split comparison from Lemma 12.4 and Theorem 12.9 identifies the
`L`-character groups and their homomorphisms. Because both groups are
already diagonalizable over `L`, further separable extension adds no
characters; the absolute Galois actions on these character groups factor
through `Gal(L/k)`. Thus the invariant-hom comparison in Theorem 12.23
is exactly the equivariance condition above. Equivalently, an equivariant
character map determines an `L`-homomorphism compatible with Galois
descent, hence a unique `k`-homomorphism. Ground-field homomorphisms
commute with this transport. This explains the iff form and its
uniqueness clause; it is a mathematical derivation, not a Lean proof.

The retained official errata for the 2017 edition contain no correction
to Lemma 12.4 or Theorems 12.9, 12.23 and 12.25.

## Relation to the existing Library

- [DiagonalizableCharacterStatement](DiagonalizableCharacterStatement.md)
  and its published proof provide the split diagonalizable character
  and homomorphism comparison, retaining torsion.
- [GaloisModuleRealizationStatement](GaloisModuleRealizationStatement.md)
  and its published proof supply the distinct essential-surjectivity
  assertion for finitely generated finite-Galois modules.
- [FiniteGaloisCharacterDescent](FiniteGaloisCharacterDescent.md) provides
  unique homomorphism reconstruction when the target over `L` is a
  split torus. The present statement also permits torsion in the
  target character group.
- [LatticeGalois](LatticeGalois.md) defines the actual Galois actions used
  in the statement. The model is the existing
  `CommGroupScheme (Spec (CommRingCat.of k))` architecture.
