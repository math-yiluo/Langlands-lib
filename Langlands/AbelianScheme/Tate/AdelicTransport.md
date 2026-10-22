# Finite-adelic transport along rational homomorphisms

This module equips the actual rational Tate-module maps with finite-adelic
linearity, and with linearity over an endomorphism algebra tensored with the
finite adeles. It supplies the algebraic transport needed to carry level
structures along the rational isogenies used in Harris–Taylor's moduli problem.
All declarations are in `Langlands.AbelianScheme.Tate`.

## Objects and explicit assumptions

Let `S` be a scheme, `T : Over S` a test scheme, and `P : ℕ → Prop` a predicate
selecting positive torsion levels. Let `A`, `B`, and `C` be abelian schemes over
`S`. The carrier `Rational A T P`, imported from `Rational.lean`, is

\[
\mathbb Q\otimes_{\mathbb Z}\operatorname{Integral}(A,T,P),
\]

where the integral carrier consists of compatible families of actual torsion
sections of `A.toGrp`. The full Tate module uses the always-true predicate;
geometric-point evaluation is obtained by choosing the corresponding `T`.
The constructions work for every `P` and `T`; no rank, finite-étaleness,
characteristic, or connectedness hypothesis is needed for these algebraic laws.

Every finite-adelic construction takes
`h : Global.RationalProfiniteIntegerAdeleComparison` explicitly. The imported
`finiteAdeleModule` and `finiteAdeleAlgebraModule` use the coupled equivalence
witnesses chosen from this hypothesis in `RationalScalars.lean`. The same `h`
is used on source and target. This module neither proves the comparison
proposition nor proves independence from choices of comparison witnesses.
The module structures are installed locally in the relevant types and proofs,
rather than declared as global instances.

## Finite-adelic equivalences

An isomorphism
`e : Rationalization.of A ≅ Rationalization.of B` is an invertible element of
the category whose morphisms are actual homomorphisms tensored with
`ℚ`. This is the rational-isogeny convention of Harris–Taylor, printed p.18;
it does not require `e.hom` to be an integral scheme morphism.

`finiteAdeleIso T P h e` is an `A_f`-linear equivalence between the rational
Tate carriers, where `A_f = Global.FiniteAdeles ℚ`. Its underlying map is
exactly `rationalHomMap T P e.hom`, and its inverse is the map induced by
`e.inv`. The construction retains the equivalence underlying the imported
`rationalIso` and uses `rationalHomMap_finiteAdeleAction` to prove scalar
linearity. Thus no unrelated equivalence of abstract modules is chosen.

`finiteAdeleIso_apply` identifies the underlying map.
`finiteAdeleIso_symm` identifies the inverse with transport along `e.symm`.
`finiteAdeleIso_refl` and `finiteAdeleIso_trans` say that transport preserves
identity and composition. In the latter formula, first transporting along
`e : A ≅ B` and then along `f : B ≅ C` equals transport along `e.trans f`.
The inverse identity is definitional; the identity and composition laws follow
by extensionality from the corresponding published `rationalHomMap` laws.

## Intertwining rational endomorphisms

Let `D` be a ring with a `ℚ`-algebra structure; commutativity of `D` is not
assumed. Suppose

\[
i_A:D\longrightarrow\operatorname{End}^0(A),\qquad
i_B:D\longrightarrow\operatorname{End}^0(B)
\]

are `ℚ`-algebra homomorphisms. The intertwining hypothesis on a rational
homomorphism `f : Rationalization.Hom A B` is

\[
f\circ i_A(d)=i_B(d)\circ f\quad\text{for every }d\in D.
\]

In Lean, `Rationalization.comp A B C f g` means first `f`, then `g`, so this
hypothesis is written
`Rationalization.comp A A B (iA d) f = Rationalization.comp A B B f (iB d)`.
It is an equality of actual rational homomorphisms, not merely a supplied
equality of linear maps on an unspecified representation.

`rationalIntertwines_identity` proves the identity case by the category unit
laws. `rationalIntertwines_comp` proves closure under composition using
associativity and the two given intertwining equations.
`rationalIntertwines_inverse` proves that an intertwining isomorphism has an
intertwining inverse: compose both sides with the original isomorphism, use
its intertwining equation, and cancel using its inverse identities.

`rationalHomMap_intertwines` transfers this equality to the rational Tate
actions by applying `rationalHomMap` to it and using its composition law.
The result is

\[
V(f)\bigl(V(i_A(d))(x)\bigr)=V(i_B(d))\bigl(V(f)(x)\bigr).
\]

Here `V(f)` denotes the published map on the selected rational Tate carrier.

## Tensor-algebra linear transport

The imported `finiteAdeleAlgebraAction` constructs the commuting action of
`D ⊗[ℚ] A_f` from `iA` and finite-adelic scalars. For a pure tensor, its action
is the rational endomorphism action after the finite-adelic scalar action:

\[
(d\otimes a)x=V(i_A(d))(a x).
\]

`rationalHomMap_finiteAdeleAlgebraAction` proves that an intertwining `f`
commutes with this action. The proof uses induction on the tensor-algebra
element. At a pure tensor it combines `rationalHomMap_intertwines` with
finite-adelic scalar compatibility; additivity handles the remaining cases.

`finiteAdeleAlgebraHomMap T P h iA iB f hf` packages the same underlying
`rationalHomMap` as a `D ⊗[ℚ] A_f`-linear map. Its application lemma is
`finiteAdeleAlgebraHomMap_apply`. The identity and composition laws are
`finiteAdeleAlgebraHomMap_identity` and `finiteAdeleAlgebraHomMap_comp`;
the latter supplies the composed intertwining proof from
`rationalIntertwines_comp`. Both linear-map equalities follow by
extensionality from the imported rational Hom laws.

`finiteAdeleAlgebraIso T P h iA iB e he` packages the underlying `rationalIso`
as a `D ⊗[ℚ] A_f`-linear equivalence. Its application, identity, inverse, and
composition laws are respectively `finiteAdeleAlgebraIso_apply`,
`finiteAdeleAlgebraIso_refl`, `finiteAdeleAlgebraIso_symm`, and
`finiteAdeleAlgebraIso_trans`. The inverse uses
`rationalIntertwines_inverse`, while composition uses
`rationalIntertwines_comp`. The inverse equality is definitional;
identity and composition are proved by extensionality and the rational Hom
laws. These maps therefore transport the constructed tensor-algebra modules
functorially along the given rational isomorphisms.

## Sources, derivation, and scope

The source is Harris–Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), Chapter I, printed p.18 (PDF p.26), and Section
III.1, printed p.91 (PDF p.99), registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Page 18 defines rational Tate modules, rational endomorphisms, and isogenies
as invertible rational homomorphisms. Page 91 uses `B ⊗[ℚ] A_f`-linear level
isomorphisms and identifies objects along isogenies transporting their
endomorphism actions and levels.

This module is a derived algebraic implementation of that transport. The
arbitrary test scheme, level predicate, and rational algebra `D` are explicit
generalizations of the setting on p.91. The proofs use the published actual
Tate functor, the scalar constructions, tensor induction, and category laws;
no additional geometric theorem is inferred from the cited text.

This unit supplies linear transport only. It makes no assertion about Weil
pairings, similitude multipliers, monodromy, continuity of rational maps,
pointed base change, or invariant orbit classes. It does not provide a
prime-to-`p` finite-adele coefficient algebra or a restricted-product
comparison. Those constructions and their compatibility with this transport
remain separate obligations.
