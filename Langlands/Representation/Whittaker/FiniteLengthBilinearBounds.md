# Finite-length assembly of bilinear bounds

This internal adapter constructs actual composition filtrations from finite
length over the group algebra, and applies the functional-factor bilinear bound
to their smooth irreducible quotients. The two representation carriers retain
independent universes. The finite-length assumptions and the pairwise rigidity
hypothesis are explicit; this module does not prove them for a mirabolic group.

`ObjectRepFiltration.ofFiniteLength` chooses a group-module composition series
using Mathlib's finite-length criterion. The published length-criterion adapter
turns it into a zero-to-full filtration by actual invariant subspaces with simple
successive quotients. The result records its length, filtration, and simplicity
proof. This is a noncomputable choice, not a new existence assumption.

`ObjectRepFiltration.isSmooth_gradedRepresentation` pulls smoothness back along
the inclusion of the upper step and then pushes it through the surjective graded
projection. Both maps are actual intertwiners.

`InvariantBilinear.exists_exception_length_le_one_of_finiteLength` assumes smooth
representations of finite group-algebra length, linear equivalences of their
full character-functional spaces with the complex numbers, compact containment
for the two character subgroups, and local constancy of their scalar characters.
For each pair of smooth irreducible representations it assumes a finite
exceptional set, outside which a nonzero bilinear-space length forces both
character functionals to exist, and those functionals imply length at most one.

The proof selects two actual composition filtrations, verifies smoothness and
irreducibility of every factor, and applies the pairwise premise to each factor
pair. The published finite-union adapter chooses a single exceptional set before
the spectral parameter and bounds the full bilinear-space length by one outside
it. Length is the extended-natural scalar-module length, so infinite-dimensional
form spaces are not mistaken for zero-dimensional spaces. No irreducible
admissibility premise is introduced.

The provenance is internal: this is a composition of the published finite-length
criterion, smoothness transfer, functional exactness, and bilinear filtration
bounds. It supplies bookkeeping for the parent JPSS proof but neither establishes
its representation-theoretic prerequisites nor proves trilinear uniqueness.
