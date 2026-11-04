# Tori in the normal factor of an external semidirect product

This internal supporting unit constructs the actual scheme-theoretic
intersection of a commutative subgroup of an external semidirect product with
the original normal factor. It proves this intersection is a torus and is
fixed pointwise when the commutative subgroup is a torus containing the
external factor.

Over any base scheme `B` in universe `u`, let `a` act on `G` through `S`,
and let `j : M → a.semidirectProduct` have commutative source.
`semidirectTorusIntersection a j` is the existing
`commutativeSubgroupIntersection j a.semidirectInl`, with its actual maps into
`M` and `G`. The definition itself does not assume that `M` is a torus.
The two composites into the semidirect product agree.
The kernel of `j ≫ a.semidirectProjection` represents the same all-test
subgroup of `M` as the intersection's first projection. The kernel point
criterion and the exact normal-factor range criterion prove this equality.
When `S` is separated, the existing represented-intersection result and
uniqueness of representatives give an actual group-scheme isomorphism from
the intersection to this projection kernel.

Suppose a group-scheme map `f : S → M` satisfies `f ≫ j = a.semidirectInr`.
Then `f` is a section of `j ≫ a.semidirectProjection`. For every test scheme,
the image of an external point and the image of an intersection point both
come from `M`, so they commute. The semidirect conjugation identity and
monicity of `a.semidirectInl` imply that the original action fixes the image
of every intersection point. This is an all-test equality and includes
nonreduced test schemes.

Over any field, assume both `S` and `G` are affine and `j` is closed.
The intersection's map into `G` is closed, so the intersection is affine.
The closed embedding of `M` into the affine semidirect product makes `M`
affine, and its projection kernel is affine. If `M` is a torus, the sectioned
kernel theorem in `Torus.RetractionKernel` proves that kernel is a torus.
Transport through the actual isomorphism proves the intersection is a torus.
No algebraic closedness, connectedness or solvability premise is needed here.

Finally, if the external `S` is a split torus and `G` is smooth affine,
the existing finite-type maximal-torus extension theorem puts the closed
external factor into a maximal torus `M` of the actual semidirect product.
The preceding construction gives a closed affine torus in `G`, smooth and
connected, fixed pointwise by the original external action. The maximality
assertion concerns `M` in the semidirect product. This unit does not assert
that its intersection is a maximal torus of `G`, provide a unipotent
complement, or prove the full semigroup ordered-product proposition.

The provenance is internal: existing actual subgroup intersections, kernel
point equivalences, uniqueness of subgroup representatives, the sectioned
torus-kernel theorem, semidirect conjugation and the existing finite-type
maximal-torus containment theorem.
