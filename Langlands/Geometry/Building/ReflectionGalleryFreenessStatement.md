# Separation-system chamber-freeness target

This internal prerequisite isolates the group-theoretic part of the affine Weyl
chamber argument. It uses an arbitrary group `G` acting on a type `X`, at
independent universes. An element of `X` represents a chamber; the type does not
need any topology or geometry. A wall is labeled by the corresponding actual
reflection as an element of `G`, so different affine roots defining the same
reflection need not provide different labels.

All declarations are in
`Langlands.Geometry.Building.ReflectionGallery`. The parameters are
`G : Type uG`, `X : Type uX`, `[Group G]`, `[MulAction G X]`, `S : Set G`,
`C : X`, and `separates : G → X → X → Prop`.
`IsSeparationSystem S C separates` is a Prop-valued structure with exactly five
laws:

| Field | Exact law |
| --- | --- |
| `not_self` | For every label `t` and chamber `x`, `¬ separates t x x`. |
| `triangle` | For all `t, x, y, z`, `separates t x z` implies `separates t x y ∨ separates t y z`. |
| `covariance` | For all `t, g, x, y`, `separates t (g • x) (g • y) ↔ separates (g⁻¹ * t * g) x y`. |
| `involution` | For every `s ∈ S`, `s * s = 1`. |
| `adjacent` | For every `s ∈ S` and every label `t : G`, `separates t C (s • C) ↔ t = s`. |

In particular, the adjacent law asserts both separation by `s` and uniqueness
among all group elements used as labels. It does not require the separating
label `t` to belong to `S`. Transitivity, chamber freeness, a Coxeter
presentation, and geometric generation are not hypotheses of this interface.

`ReflectionGalleryFreenessStatement` universally quantifies over these data and
asserts
`IsSeparationSystem S C separates →
  ∀ w : G, w ∈ Subgroup.closure S → w • C = C → w = 1`.
Here `Subgroup.closure S` is the algebraically generated subgroup, with no
topological meaning. Thus the target is triviality of the stabilizer of the
distinguished chamber within this subgroup. It does not assert chamber
transitivity or that this subgroup is all of `G`.

This contribution defines the target proposition and supplies no proof of it.
The interface and target come from Worker 1622's internal finite-word
development, reused here with its five laws unchanged. The intended proof is
a finite-word deletion argument: a separating label cancels one letter, and a
returning word can be shortened by two letters. This is internal provenance;
no external formalization or source theorem is used to define the interface.
Application to affine Weyl chambers retains the obligations to verify all five
laws for the actual affine action and to identify the geometrically relevant
group with the generated subgroup. Chamber transitivity remains a separate
obligation for simple transitivity. These geometric assertions are not proved
by this statement unit.
