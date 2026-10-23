# Tower and inclusion laws for the actual idele-class norm

This module defines three propositions in
`Langlands.Global.AdelicFunctoriality`. They concern Mathlib's actual
`NumberField.IdeleClassGroup (𝓞 K) K`, the quotient of ideles by principal
ideles, and the published continuous homomorphisms `ideleClassNorm` and
`ideleClassInclusion`. These constructions are imported unchanged.

`IdeleClassNormTower.{u,v,w}` quantifies over number fields `K : Type u`,
`L : Type v`, and `M : Type w`, with independent universes, the three
algebras `Algebra K L`, `Algebra L M`, `Algebra K M`, and their compatibility
`IsScalarTower K L M`. For every idele class `x` of `M`, it states

```text
N_{M/K}(x) = N_{L/K}(N_{M/L}(x)).
```

Both sides lie in the idele-class group of `K`.

`IdeleClassNormInclusionPower.{u,v}` quantifies over number fields
`K : Type u` and `L : Type v`, in independent universes, with `Algebra K L`.
For every idele class `x` of `K`, it states

```text
N_{L/K}(incl_{L/K}(x)) = x^[L : K].
```

The natural-number exponent is exactly `Module.finrank K L`, and both
sides lie in the idele-class group of `K`. Number-field instances supply
finite relative dimension for every extension in these statements.
Neither proposition assumes a Galois or abelian extension.
`IdeleClassNormLaws.{u,v,w}` is the conjunction of the tower proposition
at `u,v,w` and the inclusion-power proposition at `u,v`; its two components
can also be used as separate proof targets.

The second law takes norm after inclusion on a lower-field class.
The separately published
`Langlands.ClassField.Global.IdeleClassNormGaloisProduct` instead takes
inclusion after norm on an upper-field class, and uses a Galois hypothesis
to express that value as a product of conjugates.

These are proposition definitions, not proofs or assumed axioms. This
module constructs no new norm, inclusion, or class group, and supplies no
norm-index theorem, global reciprocity law, global fundamental class, or
vanishing theorem for global first cohomology.

## Source correspondence and derived realization

Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea edition (2009),
Chapter VI section 1, printed p.20 (PDF p.29), uses both laws in its two
norm-index lemmas and Reduction 1. The first lemma concerns any finite
extension `E/k`, and uses that the `[E:k]`-th power of every lower-field
idele class is a norm. The second treats a tower `E/F/k`; its displayed
index factorization uses `N_{E/k} = N_{F/k} ∘ N_{E/F}`. These two lemmas
do not require normal extensions, although Reduction 1 applies them to
the second inequality for normal extensions. Registered original:
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
Printed pp.19–21 (PDF pp.28–30) were read for context.

J. S. Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII
section 6, Lemma 6.1, printed p.214 (PDF p.223), explicitly describes norm
after inclusion as multiplication by the extension degree `m` in additive
notation. Its diagram is for particular Galois extensions arising after
adjoining a root of unity. Our multiplicative equation records the
underlying norm law for all number-field extensions; the general scope
comes from determinant norms, rather than from extending the hypotheses
of that diagram without justification. Registered original:
`milne-2020-class-field-theory`, SHA256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.
The cited page was read.

The realization on the Library maps is derived from their arithmetic
construction. As documented in [Norm](Norm.md) and
[IdeleClassNorm](IdeleClassNorm.md), the adelic norm is the product of
actual local determinant norms over the places above each base place,
and the idele-class norm is its descent to the quotient.
[Inclusion](Inclusion.md) uses the actual completed embeddings at those
places. Transitivity of determinant norms, with regrouping of places in
a tower, gives the expected first identity. The determinant norm of a
base scalar is its power by the local extension degree; the sum of those
degrees over places above a fixed base place is `[L:K]`, giving the
expected second identity. Passing through units and then the principal
quotients yields precisely the two stated equalities. This paragraph
explains their provenance and the arithmetic obligations of later proofs;
the current file does not implement those proofs. Neither cited source
is claimed to mention the Lean declarations.
