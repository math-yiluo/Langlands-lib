# Rational scalar actions on actual Tate modules

This module extends the compatible residue action on the actual integral Tate
limit to its rationalization. Under the explicit proposition
`Langlands.Global.RationalProfiniteIntegerAdeleComparison`, it transports that
action to the existing `Langlands.Global.FiniteAdeles ℚ`. For an actual abelian
scheme and a rational algebra acting through its rational endomorphisms, it
constructs the corresponding tensor-product algebra action.

## Scalar extension

For a commutative ring `R` and an `R`-module `M`,
`Langlands.TateScalarExtension.action R M` is the rational-algebra homomorphism

\[
\mathbb Q\otimes_{\mathbb Z}R
 \longrightarrow \operatorname{End}_{\mathbb Q}
       (\mathbb Q\otimes_{\mathbb Z}M).
\]

It is obtained by tensoring the integral scalar-action homomorphism and then
using Mathlib's `LinearMap.tensorProductEnd`. The proved pure-tensor formula is

\[
(q\otimes a)(r\otimes x)=qr\otimes(a x).
\]

`map_action` proves that rationalization of any integral `R`-linear map
intertwines these actions. The proof uses tensor induction in the scalar and
vector variables; on pure tensors it reduces to integral scalar compatibility,
and the additive cases use linearity.

## The comparison hypothesis and finite-adelic action

Write `h : Global.RationalProfiniteIntegerAdeleComparison`. The definitions
`integralEquiv h` and `rationalEquiv h` choose the coupled witnesses in this
published proposition. Thus the former is a ring equivalence from the actual
compatible-residue ring to the integral finite adeles, and the latter is a
rational-algebra equivalence

\[
\mathbb Q\otimes_{\mathbb Z}\widehat{\mathbb Z}_{\mathrm{res}}
 \simeq \mathbb A_f.
\]

The comparison proposition also requires bicontinuity of the integral witness
and its normalization on integers. The present module uses its coupled
pure-tensor formula, proved here as `rationalEquiv_tmul`:

\[
e(q\otimes a)=\operatorname{diag}(q)e_0(a).
\]

These choices do not prove the comparison proposition. Every finite-adelic
construction in this file retains `h` explicitly, and no independence of the
chosen witnesses is asserted.

For a scheme `S`, a commutative group object `G` in `Over S`, a test scheme
`T : Over S`, and any predicate `P : ℕ → Prop`, the published module
`Rational G T P` is `ℚ ⊗[ℤ] Integral G T P`. Its integral factor consists of
compatible actual torsion sections at positive levels satisfying `P`.
`GroupScheme.Tate.rationalScalarAction G T P` applies the generic construction
to the published full compatible-residue action on this integral limit.
`finiteAdeleAction G T P h` composes it with `rationalEquiv h` in the inverse
direction. Its type is an algebra homomorphism to rational-linear
endomorphisms, so the action is additive, multiplicative and unital.

`finiteAdeleModule` exposes the associated module structure as a definition
that a caller can install locally. It is not registered as a global instance.
`finiteAdeleModule_smul` identifies its scalar operation with evaluation of the
algebra action. `finiteAdeleAction_diagonal` proves that diagonal rational
scalars act by the existing rational scalar multiplication;
`finiteAdeleModule_scalarTower` supplies the corresponding scalar tower.
`finiteAdeleAction_integral_tmul` proves that the chosen integral comparison
recovers the original residue action:

\[
e_0(a)(r\otimes x)=r\otimes(a x).
\]

This follows from the normalized comparison formula at `1 ⊗ a`, cancellation
of the equivalence and its inverse, and `action_tmul`.

## Prime-to-p residue scalars and maps

For every natural number `p`, `rationalAwayScalarAction` gives the action of
`ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing p` on the actual `RationalAway G T p`.
For prime `p` this is the prime-to-p specialization. The definition itself
requires no primality assumption. `rationalScalarRestrictAway p` is scalar
extension of restriction of compatible residues; its pure-tensor formula is
proved. `rationalRestrictAway_scalarAction` says that restriction of actual
full Tate families to coprime levels is compatible with this scalar map.
Its proof again reduces by tensor induction to the published integral
restriction law.

`rationalMap_awayScalarAction` proves scalar compatibility for actual
homomorphism-induced away Tate maps. `rationalMap_finiteAdeleAction` proves
compatibility with the full finite-adelic action, using the same `h` for source
and target. Both apply `map_action` to the published integral linear map.
This file constructs no separate ring of prime-to-p finite adeles and no
comparison of that ring with rationalized away residue scalars.

## Actual abelian schemes and rational endomorphisms

The namespace `Langlands.AbelianScheme.Tate` specializes `finiteAdeleAction`
and `finiteAdeleModule` using `A.toGrp` for an actual bundled abelian scheme
`A/S`. All predicates and test schemes above are retained; full modules use
the constant true predicate. A geometric fibre is obtained by taking
`T = Over.mk s` for a point valued in an algebraically closed field, as in the
imported Tate definitions. No finiteness, rank or characteristic hypothesis
is needed for this algebraic construction.

`rationalHomMap_finiteAdeleAction` extends scalar compatibility to the
published map on `Rationalization.Hom A B = ℚ ⊗[ℤ] (A ⟶ B)`. Tensor induction
reduces it to integral homomorphism compatibility and rational linearity.
`finiteAdeleHomMap` bundles this same underlying map as finite-adelic linear.
Its application formula, identity, composition and addition laws are proved
by extensionality from the corresponding rational homomorphism laws.
Composition sends `f` followed by `g` to the map for `g` composed with that
for `f`.

`rationalEndAction_commute` proves that the actual rational endomorphism
action commutes with the finite-adelic action. For a possibly noncommutative
rational algebra `D` and an algebra homomorphism
`i : D →ₐ[ℚ] Rationalization.End A`, `finiteAdeleAlgebraAction` uses the tensor
product universal property to construct

\[
D\otimes_{\mathbb Q}\mathbb A_f
 \longrightarrow \operatorname{End}_{\mathbb Q}(VA).
\]

On `d ⊗ a` it first applies the finite-adelic action of `a`, then the rational
endomorphism action of `i(d)`. This formula is proved as
`finiteAdeleAlgebraAction_tmul`. `finiteAdeleAlgebraModule` exposes the
associated module structure, again for local installation. There is no
faithfulness assumption or conclusion.

## Provenance and boundaries

The source conventions are Harris–Taylor, *The Geometry and Cohomology of
Some Simple Shimura Varieties* (2001), Chapter I, printed p.18 (PDF p.26), and
Section III.1, printed p.91 (PDF p.99), registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Page 18 defines rational Tate modules by rationalizing the integral limits
and introduces rational endomorphisms. Page 91 uses the resulting
`B ⊗_ℚ A_f`-module in the definition of level structure. The arbitrary
predicate and test scheme, the generic tensor-action helper and the explicit
comparison dependency are derived formal implementations of these source
conventions, rather than additional theorems quoted from the source.

The carrier remains `ℚ ⊗[ℤ] TA`; this construction does not tensor `TA` over
the integers with `A_f`. It establishes neither the scalar-comparison
proposition nor a comparison of rational Tate modules with a restricted
product of local rational Tate modules. Rational topology, the prime-to-p
finite-adelic comparison, torsion ranks, geometric monodromy and Weil
pairings remain separate obligations. The current file asserts no
continuity of the rational actions or maps.
