# Closed linear embeddings of affine algebraic groups over fields

Author: Worker 1107.

`Langlands.GroupScheme.AffineLinearEmbeddingStatement.{u}` asserts that,
for every field `k : Type u` and every actual group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` with affine, locally finite type
structure morphism, there exist `N : ℕ` and an actual representation

```text
ρ : MatrixRepresentation G (Fin N)
```

such that `IsClosedSubgroup ρ` holds.

## Exact meaning and hypotheses

The group scheme uses the existing `Grp (Over S)` architecture, with
`S = Spec k`. The representation is an actual morphism of group objects
from `G` into the published matrix-coordinate
`GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)`.
`IsClosedSubgroup ρ`, as defined in
[`Reductive.Basic`](Reductive/Basic.md), means
`IsClosedImmersion ρ.hom.hom.left` for the underlying morphism of schemes.
The conclusion therefore includes the scheme structure of the image.

`IsAffineHom G.X.hom` makes the source affine because the base is affine.
An affine morphism is quasi-compact; together with
`LocallyOfFiniteType G.X.hom`, this gives a finite type structure morphism.
Thus these two Lean hypotheses express an affine algebraic group over a
field in the source's sense. The field and its characteristic are arbitrary.
There is no smoothness, reducedness, connectedness, reductivity, splitting
or perfection assumption. The rank is an existential natural number, with
no extra positivity requirement.

The existing `MatrixRepresentation.pointMatrix` and `affineMatrix` attach
actual group homomorphisms on every test scheme and every test algebra to
any witness `ρ`. The present proposition does not weaken the closed
immersion conclusion to injectivity on one field's points.

## Source correspondence

The registered original is J. S. Milne, *Algebraic Groups: The Theory of
Group Schemes of Finite Type over a Field* (2017), §4.d, Theorem 4.9 and
Corollary 4.10, printed p. 87 (PDF p. 103). The preceding Proposition 4.7
and Corollary 4.8 are on printed p. 86 (PDF p. 102).
Theorem 4.9 produces a faithful finite-dimensional subrepresentation of
the regular representation. Its proof establishes surjectivity of the
coordinate-ring map, hence a closed immersion into the corresponding
general linear group. Corollary 4.10 chooses a basis to obtain a matrix
group of finite rank. The Lean conclusion is this closed immersion with
the chosen coordinate basis, expressed in the existing scheme model.

Source ID: `milne-2017-algebraic-groups`. Retained PDF:
`/home/taskhub/central-library/Milne--Algebraic groups, the theory of group schemes of finite type over a field (book)--2017.pdf`.
SHA256: `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Both cited PDF pages were read. No source-specific errata file was found
in the checked workspace, project or current Library notes.

## Proof boundary

This module defines a proposition; it proves no existence result and adds
no axiom. A separate exact-target proof must produce the representation
and its closed immersion for every stated field and group scheme.
Milne's route uses a finite-dimensional subcomodule containing algebra
generators of the coordinate ring. Formalizing that route requires actual
comodule and group-scheme comparisons; they are proof obligations rather
than hypotheses of this statement.
