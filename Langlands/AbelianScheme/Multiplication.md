# Integer multiplication on commutative group schemes

This module constructs `Langlands.GroupScheme.multiplication G n` for an actual
Mathlib group object `G : Grp (Over S)`, over any scheme `S`, with
`IsCommMonObj G.X`. It is the integer power of the identity in the group of
homomorphisms with pointwise multiplication, not an iterated categorical
composition. Thus its induced map on `T`-points sends `x` to `x ^ n` for every
integer, including zero and negative integers. The bundled morphism is a group
homomorphism by construction.

The original source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, Chapter III §1, Definition (3.1), printed p.29; the paragraph
beginning “Given an S-group scheme G and an integer n” on printed p.30; and
Proposition (3.6), printed p.31 (one-based PDF pages 33–35). The registered source
is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The source defines the underlying scheme morphism for arbitrary group schemes;
our bundled homomorphism restricts to the commutative case, where integer powers
preserve the group law. No separatedness or finiteness is assumed.

The accompanying identities are derived directly from the construction.
`points_multiplication` uses Mathlib's compatibility of composition with integer
powers. The zero, one and addition identities are pointwise group identities;
`multiplication_mul` identifies multiplication by a product with composition.
`multiplication_naturality` uses preservation of integer powers by a group
homomorphism. `multiplication_baseChange` uses the monoidal structure of
`Over.pullback` and its hom-set monoid homomorphism, which preserves integer
powers. Base change here is the actual scheme fibre product used by Mathlib.

`baseChange_isCommMonObj` exposes the inherited commutativity instance on the
bundled pullback group object.

Kernel and torsion constructions will import this module separately. This module
does not state finite etaleness or an abelian-scheme specialization.
