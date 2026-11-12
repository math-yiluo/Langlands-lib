# Model-level openness from the exact uniform estimate

Author: Worker 109.

This internal assembly gives actual cofinite local-factor lifts and open
maps of fixed adelic model levels for global fields of both characteristics.
It assumes the exact `SpaceUniformLangWeilStatement.{u}` and fixed-dimensional
model hypotheses; it does not prove the uniform estimate or the final
unconditional spread theorem. The proof composes published local openness,
residue and topological reductions with the actual original-base estimate
adapter. No additional external literature assertion is claimed as proved.

For function fields the data are an arbitrary global function field `F`
over a finite field `k`, and a finite set `S` of actual curve places. For
number fields they are an arbitrary number field `K` and a finite set `S`
of finite places. In both sections, the original ring of `S`-integers is
supplied as an algebra over `ULift.{u} ℤ`, and its structure map on spectra
is assumed locally of finite type. These base-algebra and finite-type
hypotheses remain explicit. All universes are arbitrary `u`.

The two `...Factor_eventually_surjective_of_uniformLangWeil` theorems take
an actual morphism `f : X ⟶ Y` of models over the original ring of
`S`-integers. The target is quasi-separated and satisfies
`FiniteTypeOverRing`; a supplied etale chart square has a surjective source
chart and a scheme map smooth of a single specified relative dimension
`d : ℕ`. The morphism is separated, quasi-compact, point-surjective and has
geometrically connected fibres. The original-base adapter gives one
positive bound constant for every finite field and every original
coefficient action. The chart also proves original smoothness of `f`.

For curve-place integral factors, finiteness of the native residue field
is obtained from finite dimension of the original place residue field over
`k` and the actual completion residue-field equivalence. For number-field
integral factors, the native adic residue-field finiteness instance is
used. The bound therefore applies directly to those actual residue fibres,
with the original `S`-integer actions. The published
`...eventually_surjective_of_residue_bound` theorems then give surjectivity
on cofinitely many actual full-level factors by Henselian lifting and the
finite-small-residue result.

Both conclusions use the full factor index. The number-field index retains
all infinite places, as well as the finite field factors at `S` and integral
factors away from `S`. The finitely many infinite and supported field
factors may be in the exceptional set. The two
`...SpacePointLifts_of_uniformLangWeil` definitions package these conclusions
using `cofiniteSpacePointLifts`: they return a finite exceptional index set
and an actual original-coefficient source point above every target at every
remaining index, together with its exact fibre equation.

The two `...Level_isOpenMap_of_uniformLangWeil` theorems additionally require
both models to be separated and satisfy `FiniteTypeOverRing`. The
function-field theorem requires `S.Nonempty`. Target quasi-separatedness
follows from separatedness. They apply the published
`completeFieldSmoothSpacePointOpen` theorem (original proof author Worker
3519) to the existing smooth-local reduction, and supply the cofinite
surjectivity conclusion just proved. Thus their conclusions use exactly the
actual `curvePlaceSpaceLevelTopology` and `numberFieldSpaceLevelTopology`
on the model level-ring point sets. Local smooth openness is supplied by a
proved theorem, with no local-openness premise left in these declarations.

The explicit uniform-estimate premise, locally finite type integer-base
map, fixed relative dimension and model geometric hypotheses remain to be
provided in a final application. These results concern a fixed model
level. They do not assert stage coverage, model independence, existence of
the required spread morphism, or openness for arbitrary generic-fibre
models. The unchanged unconditional adelic smooth-openness target remains
unproved here.
