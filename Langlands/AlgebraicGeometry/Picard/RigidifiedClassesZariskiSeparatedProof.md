# Zariski separatedness of actual rigidified abelian-scheme classes

`Langlands.AbelianScheme.rigidifiedClassesZariskiSeparated` proves exactly
`Langlands.AbelianScheme.RigidifiedClassesZariskiSeparatedStatement.{u}`,
imported unchanged from
[`RigidifiedClassesZariskiSeparatedStatement`](RigidifiedClassesZariskiSeparatedStatement.md).
For every scheme `S : Scheme.{u}`, abelian scheme `A` over `S`, test scheme
`T : Over S`, cover `𝒰 : T.left.OpenCover.{u}`, and actual rigidified classes
`q r : RigidifiedClasses A T`, equality of their `classesPullback` images
on every cover member implies `q = r`. There are no additional hypotheses.

The proof uses the actual rigidified line bundles, their compatible module
isomorphisms, the published class quotient, and the actual relative
pullback functors. It discharges the two main inputs with the published
theorems `Langlands.AbelianScheme.rigidifiedIsoUniqueness` and
`Langlands.Scheme.Modules.OpenCoverHomGluing.openCoverHomGluing`. The first
already proves rigidity using line-bundle endomorphisms as global scalars
and `Langlands.AbelianScheme.universalGlobalFunctions`; the second proves
unique gluing of actual module maps over arbitrary scheme open covers.
Neither input remains a hypothesis of the final theorem.

## Comparing local witnesses on overlaps

Equality of local classes supplies local rigidified isomorphisms, with no
initial compatibility. The proof establishes compatibility as follows.

`relativePullbackCompTo` compares iterated relative rigidified pullback
with pullback along a chosen equal composite in `Over S`. It substitutes
that composite and applies the published `relativePullbackComp` using
`RigidifiedModule.pullbackCoherence`.
`relativePullbackCompTo_hom_val`, with `pullbackCongr_hom_val`, identifies
the underlying module map with the published comparison `compHom`.

For two cover maps, work first on their pullback in `Over S`.
`rigidified_common_map` conjugates each pulled-back local isomorphism by
these composition comparisons, producing two rigidified isomorphisms
between the same relative line bundles on the base overlap. The supplied
uniqueness proposition identifies them. Their common underlying module
map satisfies both comparison equations.

The relative total-space functor is `Over.pullback` followed by
`Over.forget`. The instance `relativeSpace_preservesPullbacks` follows
from the imported preservation results for these functors. Thus
`PreservesPullback.iso` identifies the relative total space of the base
overlap with the actual scheme pullback of the two total-space maps.
`pullback_map_injective_of_iso` shows that pullback along this isomorphism
detects equality of module maps: pulling back once more along its inverse
and using the composition and identity comparisons recovers the original
maps.

`squarePullbackIso_comp_to` specializes the published square-comparison
coherence to chosen equal composites. In
`square_compatible_of_common_map`, pull back along the overlap isomorphism,
cancel the invertible composition comparisons, and use the published
`compHom_naturality` to substitute the common map. This gives precisely
the `squarePullbackIso` compatibility equation of the module-map gluing
statement. `rigidified_overlap_compatible` applies this argument to the
two actual local rigidified isomorphisms.

## Gluing and rigidification

`relativeSpace_openCover_map` identifies the image of a base-cover map
under the relative-space functor with the corresponding member of
Mathlib's `Scheme.Pullback.openCoverOfLeft`.
`relativeOpenCover` copies that cover so that its members and maps are
expressed using the actual relative-space functor. Its domains are
therefore exactly the total spaces of the base-cover members.

`rigidified_iso_of_local_isos` forgets the local rigidified isomorphisms
to module isomorphisms. It uses the overlap compatibility just proved and
the published `openCoverIsoGluing_of_homGluing` to obtain a global module
isomorphism with those prescribed local forward maps. This corollary
glues forward and inverse maps and proves the inverse identities using
uniqueness of module-map gluing.

The remaining condition is preservation of the rigidification.
`hom_ext_of_openCover` derives equality detection for module maps from
unique gluing; `squarePullbackIso_naturality` supplies the compatibility
of the restrictions of a global map. Apply this equality detection on
the original base cover to the desired rigidification equation.
`rigidification_compatibility_of_pullback` cancels the canonical unit and
square comparisons, translating the compatibility equation for each
pulled-back rigidified object into the pullback of the desired global
equation. The prescribed local witness satisfies it, and the glued map
restricts to that witness. The global equation follows, and
`RigidifiedLineBundle.isoMk` gives a global rigidified isomorphism.

## Passing to classes and provenance

The final theorem uses quotient induction on both classes. For chosen
representatives `L` and `M`, `Quotient.exact` turns each equality of local
classes into `Nonempty` of the actual relative rigidified isomorphism
type. Classical choice selects these local witnesses. The preceding
gluing argument, instantiated with the two published unconditional
proofs, gives a global rigidified isomorphism. `Quotient.sound` then
proves equality of the original classes.

This is an internal assembly proof of the published derived statement.
Its source context and Zariski specialization of the rigidified-class
descent principle are recorded in the statement's paired Markdown; this
module makes no additional literature assertion. Its proof follows the
rigidity, overlap comparison, and gluing route described there. The
scheme and cover universes are those of the target throughout. No
affineness, finiteness, reducedness, quasi-separatedness, representability,
dual scheme, universal family, or geometric Picard-zero assumption is
introduced. The result asserts determination of existing global classes
from their restrictions; it does not construct descent of local objects
or prove an fppf sheaf property.
