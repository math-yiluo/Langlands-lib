# Actual field sections of arbitrary smooth dimension pieces

This is derived host content for Brian Conrad, *Weil and Grothendieck approaches
to adelic points*, December 31, 2011, printed p.15, Proposition 5.4, and the
manifold construction on printed p.16. The source's complete-field smooth-space
assertion allows dimensions to vary between components. It does not separately
state the algebraic dimension decomposition or this section equivalence. These
constructions supply an algebraic bridge toward that assertion.

Let `K` be any field, let `X` be an actual algebraic space over `Spec K`, and let
`hX : SmoothOverBase X`. Let `L` be any field with a `K`-algebra structure.
There is no compactness, finite-range, finite-type, separatedness, completeness,
or valuation hypothesis in this unit. Every natural number indexes a piece,
including empty pieces.

The namespace is
`Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionPieces`.
`pointDimension`, from `SmoothSourcePointDimension`, supplies the intrinsic
numerical dimension on the actual quotient `Points X.presheaf`. The module
`SmoothSourceDimensionPieces` constructs `space hX n` as
`PointOpenSubspace.space` for the open dimension level `subset hX n`, with its
actual inclusion `inclusion hX n`.

`fieldPointDimension hX x` evaluates that intrinsic dimension at the ordinary
point of an actual `x : RingPoints K X L`, using the unique point of `Spec L`.
`RingPoints` means sections over the actual relative spectrum, as defined in
`AlgebraicSpace/RingPoints`; it is not replaced by the ordinary point quotient.

`fieldPointFactor hX x` retains the original section `x` and proves membership
in the dimension-piece subfunctor at every point of its scheme test. Each point
of `Spec L` equals its closed point, so the dimension condition holds everywhere.
This is the direct method of
`SmoothTargetPointDimensions.fieldPointFactor` in `SmoothDimensionFieldPoints`,
applied to all natural-number structural dimension pieces.

The factorization uses the actual represented-open construction, not an
inference of scheme factorization from ordinary support alone.
`PointOpenSubspace.subfunctor` defines membership by the whole point image of
each scheme test; `PointOpenSubspace.range_chartInclusion` identifies its
pullback on every test with the range of the actual open subscheme inclusion,
using `OpenSubfunctorLifting.factors_through_open_iff`.
`PointOpenSubspace.isOpenImmersion_subfunctor` then proves that this subfunctor
is a representable open immersion. The piece's presheaf is this subfunctor.
Thus the subtype element constructed here is an actual section through the
genuine algebraic open subspace. Its composite with the inclusion is the
original section, by `fieldPointFactor_map`.

Evaluating any section of the dimension-`n` piece at the field's unique point
proves `fieldPointDimension_map_inclusion`. This gives uniqueness of the index
in `existsUnique_fieldPointFactor`. Inclusion is injective on actual sections
because it forgets only the membership proof. Consequently the map
`fieldPointAssembly`, which applies each piece's actual inclusion, is injective
on the dependent sum: equality of assembled sections first identifies their
dimensions, and then their sections.

`fieldPointEquiv` sends a section to its selected dimension and its actual
factorization. Its inverse is exactly `fieldPointAssembly`, as specified by
`fieldPointEquiv_symm_apply`. The first inverse law is definitional; the second
uses the proved injectivity of assembly. Both laws are also exported as
`fieldPointEquiv_left_inv` and `fieldPointEquiv_right_inv`. The equivalence is
between actual `RingPoints K X L` and
`Σ n : ℕ, RingPoints K (space hX n) L`, without any finite-index interface.

This unit ends with algebraic section maps and their inverse laws. It proves
no homeomorphism for the étale-chart rational-point topology. Functorial
analytic assembly across target dimension pieces, étale dimension preservation,
local analytic isomorphisms and uniqueness of a varying-dimensional analytic
structure remain subsequent statement and proof work. The full manifold
assertion is not claimed here.
