# Closed subgroups underlying the closure of a group of rational points

Module `Langlands.GroupScheme.Absolute.RationalPointClosureStatement` contains one
definition and one proposition. It is a helper interface for the proof of
`NormalUnipotentBorelContainmentStatement`. It is proved by
`Langlands.GroupScheme.rationalPointClosureSubgroup` in
`Absolute.RationalPointClosureProof`.

## Definition

For a field `k`, a group scheme `G` over `Spec k`, and a set `Γ` of `k`-points
`Over.mk (𝟙 (Spec k)) ⟶ G.X`, `rationalPointImage G Γ` is the set of points of the
underlying space of `G.X` at which the elements of `Γ` are located. It is the image of
`Γ` under `x ↦ x.left (closedPoint k)`, the image of the unique point of `Spec k`.

## Statement

`RationalPointClosureSubgroupStatement.{u}` says the following. Let `k : Type u` be an
algebraically closed field and `H` a group scheme over `Spec k` with `IsAffineHom H.X.hom`
and `LocallyOfFiniteType H.X.hom`. For every subgroup `Γ` of the group of `k`-points of
`H`, there are a group scheme `Z` over `Spec k` and a homomorphism `ζ : Z ⟶ H` such that

- `ζ` is a closed subgroup (`IsClosedSubgroup ζ`: the underlying scheme map is a closed
  immersion);
- `Z` is smooth over `Spec k`;
- the set-theoretic image of the underlying scheme map of `ζ` is the Zariski closure of
  `rationalPointImage H Γ`.

## Source and comparison

J. S. Milne, *Algebraic Groups* (2017):

- Lemma 1.40, printed p. 18 (zero-based PDF page 33): the Zariski closure of an abstract
  subgroup `S` of `G(k)` is again a subgroup of `G(k)`.
- Theorem 1.45, printed p. 19 (zero-based PDF page 34): for a closed subgroup `S` of
  `G(k)` there is a unique reduced algebraic subgroup `H` of `G` with `S = H(k)`, and `H`
  is geometrically reduced. The proof takes the reduced closed subscheme with underlying
  set `S`.
- Proposition 1.26(b), printed p. 13 (zero-based PDF page 28): a geometrically reduced
  algebraic group is smooth.

Milne's "algebraic group over `k`" is a group scheme of finite type over `k`. Here `H` is
affine and locally of finite type over `k`, hence of finite type. Over an algebraically
closed field the `k`-points of `H` correspond to the closed points of its underlying
space. So the closure of `rationalPointImage H Γ` is the closed set whose `k`-points form
the closure of `Γ` in `H(k)`. Milne's `H` for `S := closure of Γ` then satisfies the three
conditions above.

The proposition claims less than Milne: it does not assert uniqueness, reducedness of
`Z`, or that the `k`-points of `Z` are exactly the closure of `Γ`. The proof of
`NormalUnipotentBorelContainmentStatement` needs only the closed immersion, smoothness,
and the description of the image.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
