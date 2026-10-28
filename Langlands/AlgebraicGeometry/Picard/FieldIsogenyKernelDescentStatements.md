# Descent and Picard-zero prerequisites for field kernel duality

This module states two separate obligations for an isogeny `f : A → B` of
actual abelian schemes over an arbitrary field `k`. Their conjunction is
`Langlands.AbelianScheme.FieldIsogenyKernelDescentStatements`. All three
declarations are `Prop`-valued definitions; this module proves none of them.

`FieldTrivialPullbackCharacterBijectiveStatement` asserts bijectivity, for
every test `k`-scheme `T`, of the already constructed map

```text
trivialHomPullbackClassCharacter f (universalGlobalFunctions A) :
  TrivialHomPullbackClasses f T → Cartier.characters(kernelCommGroupScheme f)(T).
```

The domain consists of isomorphism classes of actual line bundles `L` on
`T ×_k B` whose actual pullback along `f_T` is isomorphic to the structure
sheaf of `T ×_k A`. It retains no choice of a trivialization. The codomain
is the existing relative character functor, whose elements are actual
homomorphisms from the base-changed scheme-theoretic kernel to `Gm_T`.
The tested map is exactly the normalized transported-action character
already defined in `KernelCharacterIndependence`. Neither a replacement
map nor a descent equivalence is supplied as an input.

`FieldTrivialPullbackPicardZeroStatement` asserts that every actual
rigidified family `L` on `T ×_k B` whose underlying line bundle satisfies
that same trivial-pullback condition satisfies `IsPicardZeroFamily B L`.
The latter is the Library's geometric-fibre condition: after passage to
each algebraically closed field over `T`, the corresponding line bundle is
invariant under every translation. The conclusion concerns that exact
condition, rather than membership in an unspecified Picard scheme.

Both statements quantify over every field and every test scheme. They
assume only the existing `IsIsogeny f` condition, namely finiteness,
flatness and surjectivity of the underlying morphism. There is no
separability, reducedness, characteristic, degree or extra geometric
assumption. In particular, nonreduced parameter schemes and inseparable
extensions are included. Neither statement assumes existence of a dual.

## Source and provenance

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft built 2012-02-08, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VII, Proposition (7.4), printed pp.99–100 / PDF pp.103–104,
classifies trivial-pullback line bundles by characters of a finite
locally free commutative group acting freely. Its proof uses the effective
descent equivalence of Proposition (7.2), printed p.98 / PDF p.102, and
the transported action divided by the trivial action of Example (7.3).
It explicitly treats arbitrary parameter schemes and base change.

The first predicate is the field-isogeny specialization of this
classification to the existing intrinsic character. A proof must establish
the quotient and descent hypotheses and compare the actual construction,
including its orientation; the definitions alone do not do this.

The second predicate isolates the geometric Picard-zero comparison needed
when using this classification in the proof of Theorem (7.5), printed
p.100 / PDF p.104. That proof identifies dual-kernel classes with
trivial-pullback line bundles. The predicate here spells out the additional
comparison required by the Library's definition of geometric Picard zero.
It is a derived intermediate obligation, not a separately numbered claim
quoted from the source. In particular, the source's short discussion of
representatives is not presented here as a Lean proof of translation
invariance.

These targets separate effective descent from the geometric Picard-zero
comparison. They do not assert the final bijectivity of
`dualKernelPointCharacter`, alter its published target, or prove a
dual-isogeny theorem. Separate proofs and the comparison with the actual
Poincaré representatives are still required.
