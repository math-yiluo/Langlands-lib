# Finite completed residues over base-field-valued points

This internal module proves finite-dimensionality of the completed residue field
at a source point of a locally finite analytic map over a full base-field-valued
target point. It uses a complete ultrametric normed field `K` and allows
independent universes for the field, atlas space, and chart indices.

## Base-field characters

For a spectrum point `x` of a normed `K`-algebra `A`, suppose a
`K`-algebra character `g : A →ₐ[K] K` realizes its norm:
`‖g a‖ = x a` for every `a`.

`completedResidueBaseFieldEquiv` identifies the actual completed residue
field of `x` with `K` by a bounded algebra equivalence. Its forward map
is the published canonical `completedResidueLift K x g hg`, which is an
isometry. This map is surjective because it sends each scalar from `K`
to itself. The inverse is bounded with bound one, by the isometry and
the inverse identities. `completedResidueBaseFieldEquiv_map` records its
value on the canonical image of each element of `A`.

`finite_completedResidue_of_baseFieldCharacter` transfers the
finite-dimensionality of `K` over itself along this equivalence.

## Finite maps

For a bounded map `f : A → B` whose underlying ring map is finite, and
a point `y` of the spectrum of `B`, suppose the restricted point is
realized by a base-field character on `A`.
`finite_completedResidue_of_finite_over_baseFieldCharacter` proves
`Module.Finite K (CompletedResidueField K y)`.

The published `finite_completedResidueComap` makes the source-point
completed residue field finite over the target-point completed residue
field through the canonical comap. The preceding equivalence makes the
target residue finite over `K`. Compatibility of the canonical comap
with scalars supplies the scalar tower, and `Module.Finite.trans` proves
the assertion.

## Locally finite atlas maps

`IsFiniteAt.exists_finiteResidue_pair_over_baseFieldPoint` starts with
a strong map between saturated presentations, finite at a prescribed
ordinary source point `y`. Its supplied full base-field-valued target
point is on the full-recognition target presentation and projects to
the image of `y`.

The published pointed finite-pair theorem chooses recognized source
and target charts and a source spectrum point `s` mapping to `y`,
with an actual finite Banach pullback map between the chart algebras.
The target field point supplies a character on the selected target
chart. Injectivity of that chart identifies its spectrum point with
the restriction of `s`. The finite-map theorem then proves that the
completed residue field of `s` is finite over `K`.

The result retains the selected charts, their image containment, the
source-point equation, and the finite Banach condition. It does not
prove separability, construct a finite Galois closure or an algebraic
point, or prove any Galois-invariance or algebraic-space descent
assertion.

## Provenance

This is an internal deduction from the published canonical
completed-residue lift and its isometry, the finite completed-residue
comap theorem, and the pointed finite full-recognition chart-pair
theorem. No additional geometric statement or unpublished result is
assumed.
