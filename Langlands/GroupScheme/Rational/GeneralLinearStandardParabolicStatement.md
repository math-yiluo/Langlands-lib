# Standard parabolics of the general linear group

`GeneralLinearStandardParabolicStatement` is a proposition about every field `k`
and every natural number `N`, including zero and one. It uses the published
group scheme `GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)` and its
actual diagonal torus. The cocharacter `ν` belongs to that torus's published
cocharacter lattice. It is assumed generic in the published sense, and its
integer coordinate function is strictly decreasing in the standard order on
`Fin N`. There is no restriction on the field's characteristic or cardinality.

The first assertion identifies `simpleRelativeRoots i ν` with the range of
the actual adjacent characters `GeneralLinear.simpleRootCharacter k a`.
Their integer coordinate vectors are `e_a-e_(a+1)`, for `a : Fin (N-1)`.
Positivity and simplicity through the cocharacter are **derived formulations**
of the usual standard positive-root convention.

For every ordered positive block shape `B`, the subset
`GeneralLinear.blockSimpleRoots k B` consists of the adjacent characters at
edges inside its blocks. At that subset, the proposition identifies the
choice-free `standardParabolic`, `standardLevi` and `standardUnipotent`
with the published `blockShapeParabolic`, `blockShapeLevi` and
`blockShapeUnipotent` as equal subgroup functors. Equality of functors
means equality on every test scheme over `Spec k`. The standard functors
are the **derived**, choice-free intersections over all cocharacters with
the specified simple-root signs; no structural theorem is a parameter of
their definitions.

The next three equalities give the corresponding actual rational-point
subgroups. The local `pointMap` first applies the published
`GeneralLinear.pointsEquiv` at `Over.mk (𝟙 (Spec k))`, and then changes
matrix coefficients by the canonical `Scheme.ΓSpecIso` isomorphism
`Γ(Spec k, 𝒪) ≅ k`. The standard point subgroups are the inverse images
under this canonical homomorphism of the Library's `B.parabolic k`,
`B.leviSubgroup k` and `B.unipotentSubgroup k`. Thus the assertion compares
the categorical points and the existing invertible matrices, without
supplying an unrelated abstract group or an arbitrary comparison map.

Finally every subset of the simple relative roots is
`GeneralLinear.blockSimpleRoots k B` for exactly one block shape `B`.
This uses the actual internal edges of the block shape, rather than an
independent label for a parabolic. For zero or one coordinate the simple
root set is empty, and the statement retains the same quantifiers.

Sources:

- Conrad, Gabber and Prasad, *Pseudo-reductive groups*, second edition
  (2015), source `conrad-gabber-prasad-2015-pseudo-reductive`,
  Example 2.1.1, printed pp.45–47. The diagonal cocharacter's weight
  spaces give block upper triangular, block diagonal and block
  unipotent matrices.
- Renard, *Représentations des groupes réductifs p-adiques*, French
  version dated 9 July 2026, source
  `renard-2026-representations-groupes-reductifs-padiques`, V.3.8,
  printed p.111, for the convention of fixing a maximal split torus
  and a minimal parabolic and calling the parabolics containing the latter
  standard. Specializing this convention to the diagonal torus and upper
  triangular minimal parabolic of `GL_n` is derived.

Renard's setting is a nonarchimedean local field. The arbitrary-field
matrix construction is the one in CGP and the published dynamic GL
interfaces. The subgroup-functor form, the cocharacter positivity
convention and the comparison with the choice-free intersections are
derived formulations. This file states the comparison; it supplies no
proof of it or of the general Borel–Tits structure theorems.
