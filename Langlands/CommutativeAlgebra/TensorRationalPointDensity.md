# Rational points avoiding the vanishing loci of tensor elements

Authors: Worker 254, Worker 266.

This module is commutative algebra. Everything lives in the namespace
`Langlands.CommutativeAlgebra.TensorRationalPointDensity`.

## Main result

`exists_algHom_tensor_ne_zero`. Let `k : Type u` be a field and assume
`hrat`: every nontrivial commutative `k`-algebra `R : Type u` of finite type
with `Algebra.IsGeometricallyReduced k R` has a `k`-algebra map `R →ₐ[k] k`.
Let `B : Type u` be a commutative `k`-algebra of finite type that is an
integral domain and is geometrically reduced over `k`. Let `K` and `K'` be
fields that are `k`-algebras, in arbitrary universes, and let
`f : K ⊗[k] B` and `f' : K' ⊗[k] B` be nonzero. Then some `k`-algebra map
`g : B →ₐ[k] k` satisfies

- `Algebra.TensorProduct.map (AlgHom.id k K) g f ≠ 0` in `K ⊗[k] k`, and
- `Algebra.TensorProduct.map (AlgHom.id k K') g f' ≠ 0` in `K' ⊗[k] k`.

Geometrically, `f` and `f'` define proper closed subsets of `Spec B` after
base change to `K` and `K'`, and the conclusion gives a `k`-point of `Spec B`
outside both. The hypothesis `hrat` is assumed, not proved here; the caller
supplies it. Mathematically it holds when `k` is separably closed, but this
module neither proves nor uses that fact.

## Auxiliary results

- `isGeometricallyReduced_localization`: for any submonoid `M` of a
  geometrically reduced `k`-algebra `B`, `Localization M` is geometrically
  reduced over `k`.
- `equivFinsuppOfBasisLeft_map`: for a `k`-basis `𝒞` of `K` and a
  `k`-algebra map `g : B → k`, the `i`-th coordinate of
  `Algebra.TensorProduct.map (AlgHom.id k K) g x` under
  `TensorProduct.equivFinsuppOfBasisLeft 𝒞` is `g` applied to the `i`-th
  coordinate of `x`.
- `exists_ne_zero_forall_map_ne_zero`: for nonzero `f : K ⊗[k] B` there is a
  nonzero `b : B` such that `Algebra.TensorProduct.map (AlgHom.id k K) g f ≠ 0`
  for every `k`-algebra map `g : B → k` with `g b ≠ 0`.

## Proof

`isGeometricallyReduced_localization`. By
`Algebra.isGeometricallyReduced_field_iff` it suffices that
`AlgebraicClosure k ⊗[k] Localization M` is reduced.
`IsLocalization.tensorProductEquivOfMapIncludeRight` gives a ring isomorphism
from it to the localization of the reduced ring `AlgebraicClosure k ⊗[k] B` at
the image of `M`. A localization of a reduced ring is reduced, and reducedness
transfers along the injective isomorphism.

`equivFinsuppOfBasisLeft_map` is proved by induction on `x`: both sides are
additive in `x`, and they agree on pure tensors by `simp`.

`exists_ne_zero_forall_map_ne_zero`. Take the basis
`Module.Basis.ofVectorSpace k K`. The coordinate vector of `f` under
`equivFinsuppOfBasisLeft` is nonzero because the map is a linear equivalence,
so some coordinate `b` is nonzero. If `g b ≠ 0`, then by
`equivFinsuppOfBasisLeft_map` the image of `f` has the nonzero coordinate
`g b`, so it is nonzero.

`exists_algHom_tensor_ne_zero`. Get `b` for `f` and `b'` for `f'` from the
previous lemma. Since `B` is a domain, `b * b' ≠ 0`, so
`Localization.Away (b * b')` is a domain and in particular nontrivial. It is
of finite type over `k` (a Mathlib instance), and geometrically reduced by
`isGeometricallyReduced_localization`. So `hrat` gives
`φ : Localization.Away (b * b') →ₐ[k] k`. Let `g` be `φ` composed with the
localization map. The image of `b * b'` is a unit in the localization, so
`g (b * b') = g b * g b'` is nonzero. Hence `g b ≠ 0` and `g b' ≠ 0`, and the
previous lemma applies to both `f` and `f'`.

## Provenance

This is internal infrastructure. It is not a numbered statement in Conrad,
Gabber and Prasad, *Pseudo-reductive groups* (2nd ed.). It serves the proof of
Proposition C.1.6 there (pseudo-completeness of `G/P`), in the formalization
route designed by Worker 266: over a separably closed field, a rational point
of `G` translates a point over a field extension into a prescribed dense open
subset (the open cell). The vanishing loci of `f` and `f'` are the
complements of such open subsets. The argument is the standard one: a nonzero
element of `K ⊗[k] B` has a nonzero coefficient in `B` with respect to a
`k`-basis of `K`, and rational points of a geometrically reduced variety are
dense when they exist on every nonempty open subset.

Localization of a geometrically reduced algebra reuses `SeparablyClosedRationalPointProof.isGeometricallyReduced_localization`.
