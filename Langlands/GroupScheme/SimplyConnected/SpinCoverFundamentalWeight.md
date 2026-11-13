# Fundamental weights trivial on the kernel of a homomorphism

Author: Worker 64.

`Langlands.GroupScheme.TitsIndexData.FundamentalWeightTrivialOnKernel`
is a `Prop`-valued definition. It is used to say which end vertex of a
numbered type-`D` diagram is the vector vertex of a spin cover.

## Definition

Let `K` be a field, `G` an affine locally finite type group scheme over
`Spec K` with an actual index `d : TitsIndexData G`, `v : d.Vertex` a
simple vertex, and `π : G ⟶ H` any group-scheme morphism over `Spec K`.
Write `K^s` for `SeparableClosure K` and `T` for the pinning torus
`d.pinning.torus` over `K`. Base change along `K → K^s` gives
`T_{K^s}`, the morphism `(T ⟶ G ⟶ H)_{K^s}`, the root datum
`d.pinning.rootDatum` of `G_{K^s}` relative to `T_{K^s}`, and its simple
coroots `d.pinning.rootDatum.coroot b` for `b : d.Vertex`.

`d.FundamentalWeightTrivialOnKernel v π` holds when, for every character
`χ` of `T_{K^s}` with

- `latticePairing _ χ (coroot v) = 1`, and
- `latticePairing _ χ (coroot b) = 0` for every vertex `b ≠ v`,

every `U`-valued point `t` of `T_{K^s}`, for every scheme `U` over
`Spec K^s`, whose image under `(T ⟶ G ⟶ H)_{K^s}` is the identity point,
satisfies `t ≫ χ = 1`.

So the characters `χ` in question are those equal to the fundamental
weight `ω_v` of the chosen base, and the points `t` are the points of the
scheme-theoretic intersection `ker(π_{K^s}) ∩ T_{K^s}`. The proposition
says that `ω_v` is trivial on that intersection. If `X*(T_{K^s})`
contains no character with the stated pairings, the proposition holds
vacuously. It is meant for simply connected `G`, where `X*(T_{K^s})` is
the weight lattice and the fundamental weight exists. The definition
itself has no such hypothesis.

Points are taken over all `K^s`-schemes `U`, not only over `K^s`. In
characteristic 2 the kernel `μ₂` of `Spin_{2n} → SO_{2n}` is
infinitesimal, so its only `K^s`-point is the identity. A test on
`K^s`-points alone would then be vacuous.

## Intended use

Mathematical background, not proved in Lean: let `G` be simply connected
of type `D_n`, `n ≥ 4`, and `π` a spin cover, i.e. a central isogeny onto
an orthogonal group `O(q)⁰` composed with its inclusion. Over `K^s` the
kernel is the `μ₂` in the centre of `Spin_{2n}` that acts trivially on
the vector representation. The vector weight `ω_1` (one-based numbering)
is trivial on it. The two half-spin weights `ω_{n−1}`, `ω_n` are not:
the kernel acts by `−1` on the half-spin representations. For `n ≥ 5` the
end of the long arm is therefore the only end vertex for which a spin
cover satisfies the predicate. For `D₄` the three end vertices are
interchanged by triality, and the predicate at an end vertex says that
this vertex is the vector vertex of `π`.

This is KMRT's description of the Tits algebras of `Spin(A, σ, f)`.
There the character group of the centre is `{0, λ, λ₊, λ₋}`, and `λ`
(the restriction of `ω_1`) is the one that factors through
`O⁺(A, σ, f)`. In the split case the composite
`Spin(A, σ, f) → O⁺(A, σ, f) → GL₁(A)` is the representation of highest
weight `ω_1`.

## Sources and provenance

This is a derived definition. Fundamental weights, the kernel of a
central isogeny and the characters of the centre are standard. The
formulation through the Library's `TitsIndexData`, `latticePairing` and
the functor of points over `K^s` is internal.

- M.-A. Knus, A. Merkurjev, M. Rost, J.-P. Tignol, *The Book of
  Involutions* (1998), §27.B, "Type `D_n`, `n > 2`, `n ≠ 4`", printed
  p.379 / PDF p.402 (the characters `λ, λ₊, λ₋` of the centre, with `λ`
  factoring through `O⁺(A, σ, f)`, and the vector representation of
  highest weight `ω_1`). For `D₄`: §44.A, "Tits algebras", printed
  p.563 / PDF p.586. §44.A is in Chapter X, which assumes characteristic
  different from 2 (printed p.547 / PDF p.570). In every characteristic,
  the three end vertices of `D₄` are interchanged by diagram
  automorphisms of the split group (Theorem (25.16), printed p.360 /
  PDF p.383). Registered source
  `knus-merkurjev-rost-tignol-1998-book-of-involutions`, PDF SHA-256
  `e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`.

## Lean notes

The definition lives in namespace `Langlands.GroupScheme.TitsIndexData`
and uses `open scoped CategoryTheory.MonObj` for the group structure on
points. It needs no `DecidableEq` instance.
