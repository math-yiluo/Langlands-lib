# The quotient by a central maximal torus contains no torus: statement

Worker 1379.

`CentralMaximalTorusQuotientStatement.{u}` concerns a field `k : Type u`,
a smooth affine group scheme `H` over `Spec k`, a commutative group
scheme `Z` and a homomorphism `j : Z.toGrp ⟶ H` with `IsCentral j`
(every point of `Z` maps into the published centre of `H`) and
`IsMaximalTorus j` (so `Z` is a torus, `j` is a closed subgroup, and `j`
is maximal among closed tori of `H`). Let `q : H ⟶ Q` be a homomorphism
to a group scheme `Q` over `Spec k` with
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q`: the underlying
morphism of schemes is flat, surjective and locally of finite
presentation, and the range of the scheme-theoretic kernel `kernelι q` is
`SubgroupFunctor.range j`. The statement asserts that for every
commutative group scheme `T` over `Spec k` with `IsTorus T.toGrp`, every
homomorphism `g : T.toGrp ⟶ Q` satisfies `SubgroupFunctor.range g = ⊥`,
that is, `g` sends every point of `T`, over every test scheme, to the
identity of `Q`.

`H` is not assumed connected, and `Q` is not assumed smooth or affine.

## Homomorphism form of "contains no nontrivial torus"

`SubgroupFunctor.range g = ⊥` says that `g` is the trivial homomorphism.
"Every homomorphism from a torus over `k` to `Q` is trivial" is equivalent
to Milne's "`Q` contains no nontrivial torus": a nontrivial torus in `Q`
gives a nontrivial inclusion homomorphism, and conversely the image of a
nontrivial homomorphism from a torus is a nontrivial torus in `Q`, since a
quotient of a torus is a torus (Milne, §12.e after Definition 12.14,
printed p.236, one-based PDF p.252). The Lean statement uses the
homomorphism form, which needs no notion of image.

## Source

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`.
The proof of Theorem 17.82, printed p.379 (one-based PDF p.395), says that
`T` "is maximal in `C_G(T)` if and only if `C_G(T)/T` contains no
nontrivial torus (16.43)". This statement is the "only if" direction, with
`H` in the role of `C_G(T)`, `Z` in the role of `T`, and the fppf quotient
`q` in the role of `C_G(T) → C_G(T)/T`.

Lemma 16.43, printed p.340 (one-based PDF p.356): "Let H' ⊂ H be normal
algebraic subgroups of a connected algebraic group G. If H' and H/H' are
both of multiplicative type, then H is central and of multiplicative type."

The derivation is standard. If some `g` is nontrivial, its image `S` is a
nontrivial torus in `Q`. Let `E` be the inverse image of `S` under `q`,
a smooth algebraic subgroup of `H` containing `Z`, and let `E°` be its
identity component. Since `Z` is connected, `Z ⊂ E°`; `Z` is central,
hence normal, and `E°/Z` embeds in `S`, so it is of multiplicative type.
Lemma 16.43 with `G = H = E°` and `H' = Z` makes `E°` of multiplicative
type, hence a torus (smooth and connected). It maps onto the connected
group `S`, so it strictly contains `Z`, contradicting maximality of `Z`.
Applying the lemma to `E°` rather than to `H` is why `H` need not be
connected here; in Milne's proof `C_G(T)` is connected.

This file only defines a proposition and proves nothing. It is a premise
of `CentralMaximalTorusBaseChangeReductionStatement`.
