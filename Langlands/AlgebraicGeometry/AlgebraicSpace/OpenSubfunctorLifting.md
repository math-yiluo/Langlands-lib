# Open-family lifting across arbitrary thickenings

Worker 336 proves `OpenSubfunctorLifting.openFamilyLifting`, with exact type
the published `OpenFamilyLiftingStatement.{u}`. For every base scheme and
every unrestricted thickening of actual algebraic spaces, a locally covering
family of represented open charts lifts to actual open algebraic spaces
with the same index set. Each chart has an actual morphism to its lifted
space, that morphism is an unrestricted thickening, the prescribed square
is a genuine presheaf pullback, and the lifted inclusions are locally
surjective for the slice fppf topology. No affineness, separation, finite
order, or prior target-representation hypothesis is used.
The private `openMorphism` is an abbreviation of the published
`SchemeLocalGeometry.IsOpenImmersion` definition, whose full Lean name is
`Langlands.AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion`.

The source is Stacks Project Lemma 76.9.3, Tag 05ZP, in the retained section
`05ZJ.html` and its text reading aid, registered as
`stacks-algebraic-space-thickenings-2026-11-01`, directory SHA-256
`ccb6ba86c00dce19994e249af819e4ed6aa7958b0fff47061565d127630d29da`.
The retained directory is
`/home/taskhub/pilot/literature/Stacks Project - Closed immersions and thickenings of schemes and algebraic spaces (HTML snapshot 2026-11-01)`.
The full section was read in previous conversations. Its single-open
lifting result motivates the theorem; the family interface and explicit
covering proof are derived content. The implementation below takes a
direct subfunctor and scheme-test route instead of the source's etale
equivalence route. It does not assume that equivalence.

For a natural transformation `i : F ⟶ G` and a subfunctor `A` of `F`,
`universalImage i A` consists of sections of `G` such that every restriction
coming from a section of `F` comes from a section in `A`.
`universalImage_le_iff` proves the right-adjoint relationship with inverse
image. Its inverse image is contained in `A`, and equals `A` when `i` is
monic. Evaluating a genuine pullback gives compatible lifts of sections,
which proves `universalImage_preimage_of_isPullback`. Two further elementary
lemmas compute a pullback projection's range and recognize a pullback square
into a subfunctor from its range and monomorphism. These constructions are
internal category theory using Mathlib's actual subfunctors and pullbacks.

`universalImage_isSheaf` uses the local-membership criterion for a subfunctor
of a sheaf: it pulls a covering sieve back to every test section and uses
the source subsheaf's local-membership criterion. Thus the constructed
universal image has an actual sheaf proof.

The scheme section first proves open-immersion factorization in `Over S`,
retaining the base map. For a surjective closed immersion `p : R ⟶ T`
and an open immersion `q : W ⟶ R`, `mem_universalImage_scheme` identifies
universal-image membership of a test map with containment of its point
image in `p.left '' Set.range q.left`. The forward direction pulls back
`p`, lifts points using geometric surjectivity, and factors through `q`.
The reverse direction uses injectivity of the closed embedding to get
the range containment required by the actual open-immersion lifting
property.

A surjective closed embedding is a homeomorphism, so that transported
image is open in `T`. `liftedScheme` is the actual restriction of `T`
to this open, with its structure map to `S`, and `liftedMap` is its
open inclusion. `universalImage_scheme_eq_range` identifies its
lifted-Yoneda range with the required universal image. Applying this
construction to every represented scheme test proves `universalImage_open`.

An unrestricted thickening is monic because represented closed immersions
are monic. A representable open subsheaf of an algebraic space has a
representable diagonal: maps from schemes to the ambient space are
representable, and their maps to the subfunctor are recovered by pullback.
Its atlas is the represented pullback of the ambient atlas. Applying
these facts gives `liftedSpace` and its actual inclusion. The monic
inverse-image identity identifies `liftedChart_isPullback`; base change
of the relative closed-immersion and surjectivity properties proves
`liftedChart_thickening`.

The family proof explicitly retains coverage. `family_pullback_cover`
decomposes an evaluated presheaf coproduct section into a chart component
and uses its represented pullback to show that the pulled-back chart
sieve is fppf covering. `points_covered_of_fppf_cover` forgets the
flat finite-presentation condition, refines the resulting jointly
surjective covering sieve by an actual scheme cover, and lifts each
point into one of the original family members. This step uses the
top morphism property, so it needs no separate multiplicativity
instance for the flat finite-presentation property.

`lifted_maps_cover` transports this point coverage along the thickening
and uses `Scheme.Cover.mkOfCovers` to form an actual open cover of the
target scheme. Zariski coverage implies fppf coverage. For each target
section, `universalImage_family_locallySurjective` constructs this
cover on its representing scheme test. Universal-image pullback
compatibility shows that every covering arrow lifts to a section of
the corresponding lifted subfunctor. Its coproduct inclusion then
puts the covering sieve inside the required image sieve. This proves
local surjectivity and completes `openFamilyLifting`.

The module imports the published family-lifting statement directly and has no
dependency on the final schemeness assembly. `OpenFamilyLiftingProof` exposes
the theorem as `Langlands.AlgebraicGeometry.AlgebraicSpace.openFamilyLifting`
with the exact published proposition as its type. The conditional parent
assembly is a separate private module and is not part of this proof unit.

The implementation and its direct universal-image proof are by Worker 336;
Worker 133 contributed to the interface and the parent proof decomposition.
The helper `SliceOpenGluing` supplies the lifted-Yoneda monomorphism facts;
its paired Markdown and Lean header retain the external Anthropic/NYLL
attribution. This module supplies no finite-surjective affine-descent proof.
Development compilation does not establish independent acceptance or
publication.
