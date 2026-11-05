# Compact action on actual coherent smooth orbit sections

Worker 200. This derived construction uses the actual normalized product-induced
fibers and the coherent finite scalar-smooth section space from Waldspurger VI.1
(printed pp.295–296, PDF pp.61–62). The original proof of Proposition VI.4.1 (printed p.306,
PDF p.72) uses the induced product-group action and a common open stabilizer.
The inverse-degree forms are those of V.2 (printed p.293, PDF p.59).
Source: `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

## Actual objects and hypotheses

The group `G`, character-index type `I`, inducing-carrier universe and
torus-coordinate type `J` have independent universes. Initially `G` is a locally
compact nonarchimedean topological group, `P`, `M`, `U` are actual subgroups with
the supplied semidirect decomposition `P = M U`, and `U` is closed. The object
`π` is an irreducible admissible object of the canonical complex `SmoothRep`
category for `M`; `ν` is a family of positive characters of `M`.

For the compact picture, `K` is compact open, `P` is closed, the positive
characters and the Levi projection are continuous, and every element of `G`
has the displayed factorization `p k`. A group equivalence `e` identifies the
unitary unramified character group with the finite torus `J → Circle`.
Continuity of `e` is not needed for compact stability or common open stabilizers.
There is no topology or norm assumed on the inducing or coefficient carrier.

The section space throughout is the existing
`productInducedSmoothOrbitSections`. Its values are the actual normalized
product-induced vectors at **every** inducing representative in the unitary
twist orbit. Coherence quantifies over every actual inducing equivalence.
Smoothness means that parameter pullback and actual compact restriction lie in
`finiteSmoothFamilies`: finite sums of smooth scalar functions times fixed
compact coefficient vectors. The coefficient self-twist action in this space is
the existing genuine diagonal action.

## Pointwise action and compact stability

`productInducedOrbitRepresentation` defines the action of `G × G` on all raw
sections by applying the existing product-induced representation in each actual
fiber. Its representation laws follow pointwise from the fiber laws.
`productInducedOrbitRepresentation_coherent` applies the existing equivariance
of every inducing-equivalence transport. Restriction therefore gives
`coherentProductInducedOrbitRepresentation`, an action of the full product group
on coherent sections.

`productInducedOrbitRepresentation_restriction` applies the intertwining
property of the existing `productInducedCompactEquiv`. For `k ∈ K × K`, the
restricted family is acted on by the single operator
`productInducedCompactRepresentation h K π.obj k`, independently of the
character parameter. Applying this fixed linear operator to the constant
coefficient vectors of a finite scalar-smooth expansion preserves that
expansion condition. Combining this fact with coherence proves
`productInducedOrbitRepresentation_smooth_mem`.

`productInducedSmoothOrbitCompactRepresentation` is the resulting compact action
on exactly the existing smooth-section submodule. Its application lemma retains
the original fiber action. Its evaluation lemma is literal right translation:
the translated normalized induced function at `x` has the old value at `x k`.
`productInducedSmoothOrbitCompactRestriction` is the actual parameter pullback
followed by compact restriction. It is injective by the existing actual
section-to-family equivalence and the compact-picture equivalence.

## One stabilizer for the entire section

The private fixed-compact family representation acts pointwise on all parameter
families. For a generator `z ↦ f(z) • v` of `finiteSmoothFamilies`, smoothness
of the compact induced representation supplies one open subgroup fixing `v`;
linearity makes it fix the entire generator for every `z`. The existing
`smoothVectors` submodule and span closure then prove the same assertion for
every finite scalar-smooth family. This is a finite common-stabilizer argument,
not an intersection over arbitrarily many parameters.

The restriction identity and its injectivity transfer that stabilizer to the
whole actual section. This proves
`productInducedSmoothOrbitCompactRepresentation_isSmooth` and gives the
canonical `productInducedSmoothOrbitCompactObject : SmoothRep ℂ (K.prod K)`.
The image of an open subgroup of `K × K` is open in `G × G`, so
`productInducedSmoothOrbitSections_isSmoothVector` also proves that each such
section is a smooth vector for the raw full-group action.

`productInducedSmoothOrbitSections_exists_product_stabilizer` refines the result
to the shape used in the proof of Proposition VI.4.1: there is a compact open `H ≤ K` such that `H × H`
fixes the entire section at every actual representative. The proof pulls an
ambient open stabilizer back along the two coordinate inclusions, intersects
those subgroups with `K`, and uses subgroup multiplication. The resulting open
subgroup is closed in the compact group `K`, hence compact.

## The original positive orbit-integral form

The form part adds second countability and the Borel structure on `G`, local
compactness of `P`, unimodularity of `G`, and the full identity identifying the
modulus of `P` with its conjugation modulus on `U`. It retains compact-open
cofinality on `M`, one normal central subgroup `C`, a Borel inversion-invariant
Haar measure `μ` on `M ⧸ C`, and square integrability of `π` modulo that same
central subgroup. These are the explicit hypotheses of the imported canonical
inverse-formal-degree fiber forms; an inducing positive form or induced
irreducibility is not supplied as an input.

`unitaryOrbitProductPairing_compact_action` proves equality of the descended
scalar pairing at every actual discrete-series class. Surjectivity of the
representative-to-class map reduces it to any actual representative, where the
existing `unitaryOrbitProductPairing_representative` identifies both sides
with the canonical fiber form. Its full `G × G` invariance supplies the equality
for the compact action. This pointwise result requires neither finite actual
stabilizers nor continuity of `e` nor a character measure.

For the core, the explicit finiteness of `M ⧸ (commonNormKernel ν ⊔ C)` derives
finiteness of the actual class stabilizer through the existing construction.
The forward coordinate map `e` is continuous, and the supplied character
measure `η` is finite and positive on every nonempty open set.
`productInducedSmoothOrbitCore_compact_action` rewrites both existing core
pairings by `productInducedSmoothOrbitCore_inner_integral` and integrates the
pointwise equality over the same actual orbit measure. The imported convergence
theorem establishes integrability under these hypotheses.

`productInducedSmoothOrbitCompactForm` packages this result as an
`InvariantPositiveForm` for the compact action. Its `toInnerProductCore` is
definitionally the previously constructed `productInducedSmoothOrbitCore`, as
the final comparison lemma records. It preserves the whole Hermitian pairing
for all pairs of sections. The character-measure scale, inverse actual
stabilizer-cardinality factor, central quotient Haar measure and formal degrees
are unchanged. Left invariance of `η` is not required for action invariance;
when supplied, the existing orbit-measure theorem gives the source's VI.3
local-measure-preservation convention.

## Provenance and remaining scope

V.2 supplies the invariant inverse-degree form on the actual product induction.
VI.1 supplies coherent actual sections and their fixed compact smooth model.
The proof of Proposition VI.4.1 uses the pointwise product action and a common compact open product
stabilizer. The constructions here are derived consequences of those objects,
using the existing transport, restriction and integral-core theorems. They do
not purport to prove the analytic assertion of Proposition VI.4.1.

Full `G × G` stability of the parameter-smooth section submodule is not proved
here: ambient smoothness of each section does not supply that stability.
The bundled invariant form and smooth object in this module concern `K × K`.
Rational-point realization of the displayed premises, arbitrary abstract
coordinate independence, the density-weighted global spectral form, wave
packets, inversion and the main Plancherel theorem remain separate obligations.
