# Compatible continuous families as natural descent data

Worker 56 constructs the presheaf of compatible continuous families on the
chosen-index finite full-domain cover category of a fixed represented domain.
The published actual family transport along a bounded ambient equivalence is
natural in every refinement. Its square also commutes for the inverse
refinement equivalences, which descend a finer family by actual continuous
gluing and then restrict to the coarser cover.

All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover`;
the component comparison lemmas are in its `Refinement` namespace.

## Inputs and provenance

The coefficient field `K : Type u` is complete and ultrametric. The algebras
`A` and `B` are actual `PresentedAffinoidAlgebra K` objects, built from finite
positive-polyradius Tate algebras modulo closed ideals with their quotient
norms. The input `V : Domain K A` retains its representing algebra, bounded
structural map, closed locus in the bounded multiplicative-seminorm spectrum,
exact spectrum image, and universal factorization against every presented
affinoid test algebra. The target `Y : Type v` has only a topological-space
structure, with `v` independent of `u`.

The published `DomainCoverDescent` supplies compatible families, actual
refinement pullback, its identity and composition laws, and a constructed
`pullbackEquiv`. Its inverse glues on the finer cover through the quotient
map from the finite disjoint union of actual representing spectra, and
restricts the resulting global continuous map to the coarser cover.
The published `DomainCoverRefinementTransport` supplies the actual cover
transport functor along `e : BoundedAlgEquiv K A B`; it retains all component
indices, quotient algebras and bounded restrictions. The published
`DomainCoverGluingTransport` constructs the componentwise compatible-family
equivalence through the actual spectrum-induced locus homeomorphisms and
proves its global restriction and gluing equations.

The original domain notion is Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), registered source
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
Definition 2.2.1, printed/PDF p.9; Definition 2.2.7 on p.10 gives the domain
embedding context. The functors, natural isomorphisms and comparison
equations here are internal consequences of the published constructions.
They are not separately named results in the source.

## Refinement and transport equations

For a refinement `r : Refinement d c`,
`Refinement.spectrumFamilyMap_pullbackFamily` identifies the continuous map
assembled on the finer component spectra with the coarser assembly
precomposed by `r.spectrumMap`. At a component spectrum point the equality
is exactly `Inclusion.spectrumToLocus_naturality`, followed by the selected
component map of the family. Compatibility of the family is not required.

`Refinement.transportBaseFamily_pullbackFamily` proves the square for every
family: pulling back through `r` and then transporting through the finer
component homeomorphisms equals transporting the coarser family and then
pulling back through `r.transportBase e`. Function and continuous-map
extensionality reduce the equation to the published naturality of the
actual component locus homeomorphisms with the bounded restrictions.
Every chosen refinement index is retained.

`Refinement.transportBaseFamilyEquiv_pullback` lifts this equality to the
compatible-family subtypes by subtype extensionality.
`Refinement.pullbackEquiv_trans_transportBaseFamilyEquiv` proves equality
of the two composite equivalences themselves, by evaluating them on each
compatible family and using that square.

`Refinement.transportBaseFamilyEquiv_pullbackEquiv_symm` proves the square
for the inverse refinement equivalences. Its proof applies the injective
transported refinement equivalence to both sides, uses the forward square,
and cancels each equivalence against its inverse. Thus this equation concerns
the already constructed finer gluing and coarser restriction inverse; no
inverse descent map is assumed.

`Refinement.transportBase_spectrumFamilyMap_pullbackFamily` proves that
assembly after transported refinement pullback is the original coarser
assembly precomposed by the original actual refinement spectrum map.
The quotient algebras and indices are retained, so the source disjoint
unions agree definitionally. The proof combines the raw-family transport
square, the published equality of spectrum assembly under base transport,
and the first assembly equation. It also requires no compatibility
hypothesis.

## Presheaf and natural isomorphisms

`compatibleFamilyPresheaf V Y` is a functor from `(FiniteCover V)ᵒᵖ` to
`Type (max u v)`. On an opposite cover object it is the actual
`CompatibleFamily` subtype. On an opposite refinement it applies the
published `Refinement.pullback`, wrapped as a morphism in Mathlib's
category of types. Concrete function extensionality and the published
pullback identity and composition laws prove the functor laws. The
underlying cover category still retains its chosen index functions.

`gluingNatIso V Y` identifies the constant functor on `C(V.locus, Y)` with
this presheaf. Its component is the published `gluingEquiv`, converted
from a type equivalence to an isomorphism in the category of types.
Its forward map restricts a global continuous map, and its inverse is
the actual quotient-lift gluing construction. The published equation
`Refinement.pullback_gluingEquiv` proves naturality in every refinement.

The entry `transportBaseFamilyNatIso e V Y` is the natural isomorphism
from this presheaf to the compatible-family presheaf on
`Domain.transportBase e V`, precomposed with
`(FiniteCover.transportBaseFunctor e).op`. Each component is the
published constructed `transportBaseFamilyEquiv`. The proved compatible
refinement square supplies naturality. Mathlib's `NatIso.ofComponents`
constructs the inverse natural transformation from those component
isomorphisms; neither a natural isomorphism nor its naturality is an input.

`transportBaseFamilyNatIso_hom_app` and
`transportBaseFamilyNatIso_inv_app` expose its component maps as the
actual family equivalence and its inverse. The equation
`transportBaseFamilyNatIso_gluing` identifies the categorical components
with the published global restriction/gluing square: applying the family
transport component to the original global restriction equals restricting
the global continuous map precomposed with the target locus homeomorphism.
It follows directly from
`transportBaseFamilyEquiv_gluingEquiv`.

These constructions allow empty covers, empty loci, zero quotient algebras,
arbitrary finite positive polyradii and trivial valuation. They require a
supplied full-domain cover and a genuine bounded equivalence of ambient
algebras. They concern continuous maps on represented loci, with no separation
or compactness requirement on `Y`. Algebra-section descent, general analytic
pullbacks, rational-domain existence, analytic structure sheaves, atlas
completion and analytic etale sites remain separate construction obligations.
