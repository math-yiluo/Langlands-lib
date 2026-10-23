# Away adelic transport along rational homomorphisms

This module bundles the actual maps on away rational Tate modules as linear
equivalences over the away finite adeles, and as linear maps and equivalences
over a rational endomorphism algebra tensored with those adeles. All declarations
are in `Langlands.AbelianScheme.Tate`.

## Carriers and hypotheses

Fix a scheme `S`, a test scheme `T : Over S`, abelian schemes `A`, `B`, `C`
over `S`, and a natural number `m`. The carrier is

\[
V^m A(T)=\operatorname{RationalAway}(A,T,m)
 =\mathbb Q\otimes_{\mathbb Z}\operatorname{Away}(A,T,m).
\]

The integral factor consists of compatible actual torsion sections at positive
orders coprime to `m`. For prime `m = p` this is the prime-to-p carrier; the
definitions also cover composite `m`, `m = 1`, and `m = 0`. Geometric fibres
are obtained by the corresponding choice of test scheme. The algebraic
transport laws require no finiteness, rank or characteristic assumption.

The full and away scalar comparisons remain explicit hypotheses:

```lean
h : Global.RationalProfiniteIntegerAdeleComparison
hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m
```

The coefficient ring is the existing `Global.PrimeToFiniteAdeles m`, denoted
below by \(\mathbb A_f^m\). The imported `primeToFiniteAdeleModule` and
`primeToFiniteAdeleAlgebraModule` use the coupled witnesses chosen from these
same proofs on both source and target. They are installed locally, rather
than as global instances. Neither comparison proposition nor independence
of its chosen witnesses is proved here.

## Transport along rational isomorphisms

An isomorphism `e : Rationalization.of A ≅ Rationalization.of B` is an
invertible rational homomorphism in the category with morphisms
`ℚ ⊗[ℤ] (A ⟶ B)`. In particular, its forward map need not be an integral
scheme morphism.

`primeToFiniteAdeleIso T hAway e` equips the equivalence underlying the
published `rationalIso` for the predicate `fun n => Nat.Coprime n m` with
\(\mathbb A_f^m\)-linearity. Its forward map is exactly
`rationalHomMap T (fun n => Nat.Coprime n m) e.hom`; its inverse is induced
by `e.inv`. Scalar linearity follows from
`rationalHomMap_primeToFiniteAdeleAction`.

The application and inverse formulas are `primeToFiniteAdeleIso_apply` and
`primeToFiniteAdeleIso_symm`. Identity and composition are
`primeToFiniteAdeleIso_refl` and `primeToFiniteAdeleIso_trans`. The latter
identifies transport along `e.trans f` with first transporting along `e`,
then along `f`. The inverse formula is definitional. Identity and composition
follow by linear-equivalence extensionality and the corresponding rational
Hom map laws.

## Intertwining and tensor-algebra transport

Let `D` be a possibly noncommutative ring with a rational algebra structure,
and let `iA : D →ₐ[ℚ] Rationalization.End A` and `iB` be actual rational
endomorphism actions. The required intertwining equation for a rational
homomorphism `f` is

\[
f\circ i_A(d)=i_B(d)\circ f\quad(d\in D).
\]

In Lean, `Rationalization.comp A B C f g` means first `f`, then `g`.
Thus the equation is written
`Rationalization.comp A A B (iA d) f =
Rationalization.comp A B B f (iB d)`.

The imported tensor-algebra action satisfies
\((d\otimes a)x=V(i_A(d))(a x)\).
`rationalHomMap_primeToFiniteAdeleAlgebraAction` proves that an intertwining
`f` commutes with this entire action. Its proof uses tensor induction on
the coefficient in `D ⊗[ℚ] Global.PrimeToFiniteAdeles m`. At pure tensors
it combines `rationalHomMap_intertwines` from `AdelicTransport` with away
adelic scalar compatibility. The other cases follow from additivity.

`primeToFiniteAdeleAlgebraHomMap T hAway iA iB f hf` bundles that same
underlying rational Tate map as linear over \(D\otimes_{\mathbb Q}\mathbb A_f^m\).
Its application, identity and composition laws are
`primeToFiniteAdeleAlgebraHomMap_apply`,
`primeToFiniteAdeleAlgebraHomMap_identity`, and
`primeToFiniteAdeleAlgebraHomMap_comp`. The identity and composite
intertwining proofs are supplied by the imported
`rationalIntertwines_identity` and `rationalIntertwines_comp`.
The linear-map equalities follow by extensionality from the rational Hom laws.

`primeToFiniteAdeleAlgebraIso T hAway iA iB e he` gives the corresponding
linear equivalence when `f` is the forward map of an isomorphism.
Its application, identity, inverse and composition formulas are
`primeToFiniteAdeleAlgebraIso_apply`, `primeToFiniteAdeleAlgebraIso_refl`,
`primeToFiniteAdeleAlgebraIso_symm`, and `primeToFiniteAdeleAlgebraIso_trans`.
The inverse uses `rationalIntertwines_inverse`, whose imported proof derives
inverse intertwining from the category inverse identities. Its underlying
map agrees definitionally with the inverse equivalence. Identity and
composition again use extensionality and the rational Hom map laws.

## Provenance and scope

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), Chapter I, printed p.18 (PDF p.26), defines away rational Tate modules
and isogenies as invertible rational homomorphisms. Section III.1, printed
p.91 (PDF p.99), uses transport of endomorphism actions and levels along
isogenies; printed p.92 (PDF p.100) introduces the away adelic level condition.
The registered source is `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

This module is a derived algebraic implementation of the transport needed
by that condition. It specializes the construction in `AdelicTransport`
to the away coefficient action in `AwayRationalScalars`, reusing the actual
rational Tate functor and the rational intertwining lemmas. Arbitrary test
schemes, natural moduli and rational algebras are internal generalizations.

This unit establishes linear transport and its functorial laws. Weil pairings,
similitude multipliers, monodromy, rational topology, continuity, pointed base
change and fixed orbit classes remain separate obligations. No full-to-away
transport square or prime-to-p rational-homomorphism localization is asserted
here. In particular, these rational isomorphisms use `ℚ`, rather than the
smaller `ℤ_(p)` homomorphism category of prime-to-p isogenies.
