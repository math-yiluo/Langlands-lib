# All-test-scheme bijectivity of actual kernel characters over a field

`Langlands.AbelianScheme.FieldDualKernelCharacterBijectiveStatement`
is a proposition definition. For an isogeny `f : A → B` of actual
abelian schemes over `Spec k`, it asserts that the constructed intrinsic
map

```text
dualKernelPointCharacter ... T :
  (T → kernel(dual(f))) → Cartier.characters(kernel(f))(T)
```

is bijective for every test `k`-scheme `T`. The field is arbitrary.
The quantifier includes nonreduced schemes and schemes over
inseparable extensions; a bijection only on geometric points does not
satisfy this target.

Here `dual(f)` is exactly the underlying group-scheme homomorphism of
`dualCommGroupSchemeMapFromEvaluation`. Both kernels are the existing
scheme-theoretic kernels. The codomain is the existing relative
character functor: its elements are actual homomorphisms from the
base change of the primal kernel to the multiplicative group over
`T`. No Cartier-dual representing scheme, bijection, arbitrary beta,
or pairing is supplied as data.

The input `IsIsogeny f` is the existing finite, flat and surjective
condition on the underlying scheme morphism. It imposes no
separability, characteristic-zero or invertible-degree assumption.
The statement retains the existing `HasDualScheme` witnesses,
seven dual-constructor propositions, and actual inverse line bundles
`MA`, `MB` with their tensor evaluation isomorphisms. These are the
inputs of the existing actual dual-group map, rather than hypotheses
that the output beta is bijective.

The map tested is the normalized `dualKernelPointCharacter`. It sends
the actual dual-kernel point to its Poincaré representative, uses the
proved triviality of its pullback along `f`, and applies the intrinsic
kernel character. Its orientation is the transported translation
action divided by the trivial action, as in the imported construction.
Thus the predicate constrains that particular map, including its
normalization.

## Source and translation

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft built 2012-02-08, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter VII, Theorem (7.5), printed p.100 / PDF p.104, identifies
the kernel of the dual of an isogeny of abelian varieties with the
Cartier dual of its kernel. Its proof constructs the map in the
direction used here by taking a representative line bundle with
trivial pullback and applying Proposition (7.4), printed pp.99–100 /
PDF pp.103–104. The end of that proposition records compatibility
with arbitrary test-scheme base change.

This target extracts the bijectivity component of that theorem for
the Library's actual chosen dual and actual intrinsic character. The
chosen dual is specified by its rigidified Picard-zero universal
property. A proof must compare these exact constructions with the
source's Picard and character description; it cannot substitute an
unnormalized isomorphism between abstract finite groups. In
particular, establishing the surjectivity and injectivity of this
specific beta requires the descent and classification content of
the theorem. The imported definitions alone do not prove them.

## Scope and proof obligation

This file supplies a `Prop`-valued definition, no proof and no new
axiom. A separate proof task must prove this exact published
declaration.

This is the all-test-scheme bijectivity component of kernel Cartier
duality over a field. Naturality and additivity of the actual beta
remain separate obligations; this file does not package it as an
isomorphism of group-valued functors. It also does not assert that
the dual map is an isogeny, prove existence or geometry of a dual,
extend kernel duality to arbitrary base schemes, or construct a
finite Weil pairing. Those assertions need their own proofs or
precise relative hypotheses. No polarization or integral perfectness
for a nonprincipal polarization is asserted.
