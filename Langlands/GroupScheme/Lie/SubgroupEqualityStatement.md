# Subgroups with the full Lie algebra

This file states `LieSubgroupEqualityStatement`: a smooth closed subgroup of a
smooth connected affine group over a field whose Lie algebra is everything is
the whole group. It contains no proof.

## The statement

`LieSubgroupEqualityStatement` quantifies over every field `k : Type u`, every
group scheme `H : GroupScheme (Spec (CommRingCat.of k))` whose structure
morphism is `Smooth` and `IsAffineHom` and whose underlying space `H.X.left` is
a `ConnectedSpace`, every group scheme `K` over `Spec k` whose structure
morphism is `Smooth`, and every homomorphism `j : K ⟶ H`. It asserts: if

* `IsClosedSubgroup j`, that is, the underlying morphism of schemes is a
  closed immersion ([Reductive.Basic](../Reductive/Basic.md)), and
* every `X : lieKernel H k` has the form `Y.val ≫ j.hom.hom = X.val` for some
  `Y : lieKernel K k`,

then `SubgroupFunctor.range j = ⊤`: every point of `H` over every test scheme
over `Spec k` factors through `j`. Here `lieKernel H k` is the kernel of
reduction `H(k[ε]) → H(k)` on actual dual-number points
([Lie.DualNumberKernel](DualNumberKernel.md)), Milne's `Lie(H)`; the second
hypothesis says that the injective map `Lie(K) → Lie(H)` induced by `j` is
surjective.

## Provenance

Milne, *Algebraic Groups* (2017), Proposition 10.15 (printed p.190): "Let
`H ⊂ G` be algebraic groups such that `Lie(H) = Lie(G)`. If `H` is smooth and
`G` is connected, then `H = G`." Milne's proof (printed p.191) uses
Proposition 1.37 (printed p.18), `dim Lie(G) ≥ dim G` with equality exactly
when `G` is smooth. In the notation of this file Milne's `G` is `H` and
Milne's `H` is `K`.

Milne's Chapter 10 assumes throughout that all algebraic groups are affine over
the base field (chapter opening, printed p.186, PDF p.202), so affineness of
the ambient group is part of the source's hypotheses. Differences from the
source, all of which make the formal statement a special case of Milne's: the
ambient group `H` is additionally assumed smooth (Milne needs only an affine
algebraic group, which is then forced to be smooth); the subgroup is given as a
closed immersion `j`, and the conclusion `H = K` is expressed as surjectivity
of `j` on points over every test scheme. Finite type of `H` is not assumed
separately: it follows from smoothness, which gives locally of finite type,
together with affineness over `k`. Neither affineness nor finite type of `K`
is assumed separately: both follow from the closed immersion `j` into `H`.

Source ID: `milne-2017-algebraic-groups` (Proposition 10.15, printed pp.190–191,
PDF pp.206–207; Chapter 10 opening convention, printed p.186, PDF p.202;
Proposition 1.37, printed p.18, PDF p.34). This is a
proposition target, with no proof, axiom or instance asserting it.
