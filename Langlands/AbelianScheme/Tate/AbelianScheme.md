# Integral Tate groups of bundled abelian schemes

Author: Worker 143.

This module specializes the published construction in
`Langlands/AbelianScheme/Tate/Integral.lean` to the published `AbelianScheme`
bundle. Every declaration is in `Langlands.AbelianScheme.Tate`. The input is an
actual abelian scheme `A` over `S`, and the construction uses its underlying
commutative group object `A.toGrp`. Its morphisms are actual abelian-scheme
homomorphisms, passed to the construction by `AbelianScheme.groupHom`.
No additional family of groups, transition maps, or inverse limits is supplied.

## Provenance and scope

This is an internal specialization of the published integral construction,
not a new geometric theorem. Its mathematical source correspondence is the
one documented in `Integral.md`, based on these originals read directly:

- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
  (2001), Chapter I, printed p.18 / PDF p.26, registered
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`:
  full Tate groups over positive integers and restriction away from a finite
  set of primes. Here `Away` gives the singleton-prime version when `p` is prime.
- Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft built
  2012-02-08, Chapter X (10.1)–(10.5), printed pp.141–143 / PDF pp.145–147,
  registered `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`:
  multiplication-by-ℓ transitions on ℓ-power torsion, compatible sequences with
  coordinatewise addition, and the induced coordinatewise homomorphisms.

The general divisor transition formula, arbitrary test schemes, topology, and
universal property are internal constructions of `Integral.lean`; neither
source is claimed to display that entire generalized construction. The cited
pages concern abelian varieties over fields. Here the scheme input and its
fibres are supplied by the published bundle and kernel construction. The bundle
includes explicit commutativity alongside smoothness, properness, and geometric
connectedness, with the source-definition equivalence kept separate as
documented in `Basic.md`. This specialization uses only its group structure and
commutativity. No source-specific errata note was present in the available
Library.

## Levels, limits, and topology

`Level A T n` is definitionally `GroupScheme.Tate.Level A.toGrp T n`, the
additive form of the subgroup of sections killed by the actual multiplication
morphism. `kernelLevelEquiv` is the imported additive equivalence from points of
the actual scheme kernel. `transition A T h` for `h : n ∣ m` is the imported
multiplication-by-`m/n` map on those sections. `transition_self` and
`transition_comp` instantiate the existing identity and composition proofs;
the identity requires `0 < n`.

`Integral A T P` is definitionally the subgroup of coherent families over
`GroupScheme.Tate.Index P = {n : ℕ // 0 < n ∧ P n}`. `Full` selects every
positive integer, and `Away p` selects the integers coprime to `p`. The formula
for `Away` is defined for any natural `p`; primality is needed only for its
usual single-prime interpretation.

These are abbreviations of the existing types, so their abelian-group
structures, discrete level topologies, product-subspace limit topologies, and
topological additive-group instances are inherited without transport or a new
choice. `evaluation`, `lift`, and `restrictAway` likewise reuse the existing
homomorphisms. Their displayed compatibility, projection, uniqueness, and
continuity laws instantiate the published laws; `evaluation_lift` is
definitionally true. Thus the universal property of the coherent-family limit
is retained. No finiteness, compactness, profiniteness, rank, finite étaleness,
scalar action, or rationalization assertion is made.

## Homomorphisms and actual fibres

`levelMap T f n` postcomposes a torsion section with the actual group-scheme
homomorphism `AbelianScheme.groupHom f`. `levelMap_transition` gives transition
compatibility. `map T P f` is the continuous coordinatewise additive
homomorphism on the limits, and `evaluation_map` records its coordinates.

`map_id` and `map_comp` instantiate the published functoriality laws: the
underlying-group accessor preserves identities and composition definitionally.
`map_add` instantiates `GroupScheme.Tate.map_mul`, because addition of
abelian-scheme morphisms is, by the published additive Hom convention,
pointwise multiplication of the underlying group-object morphisms.
It concerns addition of morphisms, not endomorphism composition.
`continuous_map` reuses the coordinatewise continuity proof. Taking `P` to be
`True` or coprimality gives these laws for both `Full` and `Away`.

`fibreLevelEquiv A s n`, for `s : U ⟶ S`, identifies `Level A (Over.mk s) n`
with sections over `U` of the actual pullback of
`kernel (multiplication A.toGrp n)` along `s`. It directly specializes the
published equivalence, whose construction uses the over-category
map/pullback adjunction followed by the scheme kernel's universal property.
The kernel and fibre are not reconstructed or replaced by an abstract group.

`FullAt A s` and `AwayAt A s p` take `T = Over.mk s` for
`s : Spec Ω ⟶ S`. The definitions work for any field Ω; choosing Ω
algebraically closed gives the geometric-point convention. The preceding
equivalence identifies every level with actual Ω-valued torsion-fibre points.
Induced maps at such a point are `map (Over.mk s) P f`, with all the displayed
laws and continuity results applying directly.
