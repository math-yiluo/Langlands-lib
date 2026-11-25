# Finite Galois character anti-equivalence

This proposition states the categorical classification for a specified finite
Galois splitting field using the actual character functor. It is a derived
finite-level form of Milne's classification of groups of multiplicative type.
The declaration is a Prop-valued statement; no proof is supplied here.

## Exact assertion

Let `k L : Type u` be fields with a `k`-algebra structure on `L`. Assume both
`FiniteDimensional k L` and `IsGalois k L`. These hypotheses mean that `L/k`
is a finite Galois extension. The field and character modules retain the
arbitrary universe `u`.

`MultiplicativeTypeGaloisEquivalenceStatement` asserts that the specific functor
`SplitMultiplicativeType.characterFunctor k L` has Mathlib's
`Functor.IsEquivalence` property:

```text
(SplitMultiplicativeType k L)ᵒᵖ
  ⥤ Action (FGModuleCat.{u} ℤ) (L ≃ₐ[k] L).
```

An object of the source before passage to the opposite category is an actual
commutative `k`-group scheme whose `L`-pullback is isomorphic to `D_L(M)` for
some finitely generated abelian `M`. The isomorphism and model are existential
witnesses of an object property. All actual ground-field homomorphisms between
these objects are morphisms. The target is the existing category of finitely
generated integral modules with an action of `Gal(L/k)` and equivariant linear
maps.

The specified functor sends `T` to its actual group of characters over `L`,
with the canonical transport action of the Galois group. Its maps are
precomposition by the actual base-changed group homomorphisms. Its forgetful
compatibility identifies it with the published unrestricted character functor.
Thus the proposition concerns this actual functor, rather than the existence
of an unspecified equivalence between the two categories.

The equivalence property entails full faithfulness and essential surjectivity.
In particular, every equivariant integral linear map of actual character groups
comes from exactly one ground-field homomorphism in the reversed direction,
and every finitely generated integral representation is isomorphic to an
actual character representation. A proof must establish those properties for
the specified functor.

No smoothness, connectedness, reducedness, freeness or characteristic
restriction is imposed. Torsion, including characteristic-primary torsion, and
finite nonsmooth diagonalizable factors are retained. Splitting by this `L`
is required; the source is not the category of every multiplicative-type
group over `k`.

## Provenance and proof obligations

The registered original is J. S. Milne, *Algebraic Groups* (2017),
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Section 12.g, printed p.239 / PDF p.255, introduces the contravariant actual
character functor with continuous absolute-Galois action. Theorem 12.23,
printed p.240 / PDF p.256, states its equivalence for groups of multiplicative
type and finitely generated integral Galois modules. The proof of Corollary
12.25 on that page uses a common finite Galois splitting field and Galois
descent of homomorphisms.

This target restricts the source to groups split by the specified finite
Galois extension and the module action to its finite Galois group. A
representation of that group inflates to a continuous absolute-Galois action;
the corresponding multiplicative-type group is split by `L`. Conversely a
group split by `L` has such a character action. This is the finite-level
derivation from Milne's theorem, rather than a claim that its original
absolute-Galois formulation is identical to the Lean statement.

The original pages and complete retained official 2017 errata were read.
No correction affects these passages.

The Library's `MultiplicativeTypeGaloisFullFaithfulnessStatement` isolates the
homomorphism assertion on supplied diagonalizable models; it is proved
separately, as `multiplicativeTypeGaloisFullFaithfulness` in
`MultiplicativeTypeGaloisFullFaithfulnessProof`. The published module-realization theorem provides
the actual group, its specified `L`-splitting and an equivariant additive
equivalence for a finitely generated integral representation. A proof of this
categorical target must convert those comparisons to the bundled action
category and apply them to the actual character functor.

No quasi-inverse or categorical proof is constructed in this module, which
only states the proposition.
Absolute-Galois continuity, arbitrary varying splitting fields and
compatibility with short exact sequences are separate assertions.
