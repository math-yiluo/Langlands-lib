# Absence of tori is invariant under field extension: statement

Worker 1379.

`NoTorusBaseChangeStatement.{u}` concerns fields `k K : Type u` with
`Algebra k K` and a smooth affine group scheme `Q` over `Spec k`. Suppose
that for every commutative group scheme `T` over `Spec k` with
`IsTorus T.toGrp`, every homomorphism `g : T.toGrp ⟶ Q` satisfies
`SubgroupFunctor.range g = ⊥`. Then for every commutative group scheme
`T` over `Spec K` with `IsTorus T.toGrp`, every homomorphism from
`T.toGrp` to the base change `Q_K` satisfies the same condition. The base
change is the published functor `GroupScheme.baseChange` along
`Spec K ⟶ Spec k`, as in `MaximalTorusBaseChangeStatement`.

`Q` is not assumed connected. The extension `K/k` is arbitrary; it may be
inseparable or transcendental, and `k` may be imperfect.

## Homomorphism form of "contains no nontrivial torus"

`SubgroupFunctor.range g = ⊥` says that `g` sends every point, over every
test scheme, to the identity, so `g` is the trivial homomorphism. Over a
field, "every homomorphism from a torus to `Q` is trivial" is equivalent to
"`Q` contains no nontrivial torus": a nontrivial torus in `Q` gives a
nontrivial inclusion homomorphism, and conversely the image of a
nontrivial homomorphism from a torus is a nontrivial torus, since a
quotient of a torus is a torus (Milne, §12.e after Definition 12.14,
printed p.236, one-based PDF p.252). So the statement says: if `Q`
contains no nontrivial torus over `k`, then `Q_K` contains no nontrivial
torus over `K`. The Lean statement uses the homomorphism form, which needs
no notion of image.

## Source

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`.
The proof of Theorem 17.82, printed p.379 (one-based PDF p.395), passes
from `k` to `k'` through the equivalence "contains no nontrivial torus
⟺ unipotent" for a connected group variety, and invariance of unipotence
under field extension. The results used are:

- Proposition 17.81, printed p.378 (one-based PDF p.394): "A connected
  group variety is unipotent if it contains no nontrivial torus."
- Corollary 14.9, printed p.282 (one-based PDF p.298): "Let G be an
  algebraic group over k, and let k' be an extension of k. Then G is
  unipotent over k if and only if G_{k'} is unipotent over k'."
- Corollary 14.18(b), printed p.284 (one-based PDF p.300): "There are no
  nontrivial homomorphisms over k ... from an algebraic group of
  multiplicative type to a unipotent algebraic group."

The derivation: tori are connected, so every homomorphism from a torus
to `Q` lands in the identity component `Q°`, a connected group variety
because `Q` is smooth. By hypothesis `Q°` contains no nontrivial torus, so
it is unipotent (17.81), and so is `(Q°)_K` (14.9). The subgroup `(Q°)_K`
is open and closed in `Q_K` and contains the identity, so every
homomorphism from a torus over `K` to `Q_K` lands in `(Q°)_K` and is
trivial (14.18(b)).

This file only defines a proposition and proves nothing. It is a premise
of `CentralMaximalTorusBaseChangeReductionStatement`.
