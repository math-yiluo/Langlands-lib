# Integral images of witnessed relative global pairs

This derived construction forms actual integral submodules from the published
relative Weil group and actual cuspidal automorphic form realizations. Its index
retains all local expansion witnesses. It is conditional on those witnesses and
is explicitly a finite relative level construction.

## Provenance and inputs

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
p-adique* (2000), sections 2.4–2.5, printed pages 445–446 (PDF pages 7–8), defines
the two local generator maps of an associated absolute global pair using the
full local Weil representation and the sum of its associated automorphic
component's unitary supercuspidal factors. The subgroups are their integral
generated images. The registered source is `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

This module derives a witnessed relative-level construction from that pattern.
It does not implement the source's absolute group or assert the source's global
unitary automorphic hypothesis. The actual cuspidal object and genuine weak
association are retained, while the required unitary support at the chosen
place is supplied explicitly. The relative association uses the published
nonvacuous cofinite unramified matching predicate, rather than an arbitrary
family of lattice elements or a presumed local correspondence.

The published `RelativeWeilGroup.AssociatedSupercuspidalInductionStatement`
already states the relative form of Henniart's Theorem 2.4. This module neither
restates nor proves it. An actual unitary support is retained as a witness, so
that statement is not needed to define the spans or prove their degree laws.

Let `F` and `E` be number fields in universe `uF`, with the supplied algebra and
Galois instances. Fix an actual fundamental-class family `c`, a finite place `v`
of `F`, and the existing compactness instance for its additive adele quotient.
No arithmetic normalization or existence theorem for `c` is assumed here:
the construction uses the actual class extension at the supplied family.
The relative Weil representation carrier has independent universe `uW`, and the
presentation's model local factors have independent universe `uP`. The embedded
automorphic local component and the supercuspidal support data use universe
`uF`, the universe of the actual form-space carrier. There is no carrier resizing
or finite-dimensionality requirement on automorphic factors.

Complex representations use their existing ordinary complex topology and
continuity convention. All generated modules have integer coefficients. Local
fields, local Weil groups, topologies, geometric Frobenius and normalized
parabolic induction are the published actual constructions.

## Full local classes and witnessed generators

`localExactClass` takes a continuous representation of the actual relative Weil
group and a continuous local map and forms the genuine exact Grothendieck class
of the full restriction on the original carrier. Its degree is that carrier's
dimension. It neither discards summands nor presumes local irreducibility.

`WitnessedGenerator` retains a positive rank `rankIndex + 1`, an actual
irreducible unitary global relative Weil representation, an actual full cuspidal
operator realization, its genuine spectral presentation, and their weak
association. It also retains a place above `v`, a reciprocity candidate and a
continuous local map satisfying `IsLocalRelativeWeilMap`.

The Weil element is an effective integral combination in the actual local
unitary irreducible lattice, with an explicit exact-expansion equality after
inclusion into the full irreducible lattice. That equality is to the exact class
of the **full** local restriction, not to a selected irreducible constituent.
The automorphic element has actual `IsUnitaryLatticeSupport` of the embedded
local form component, placed in the canonical p-adic category by the published
`padicObject` adapter. Its local irreducibility and admissibility are explicit
inputs. The support retains the genuine normalized-induction subquotient
witness and all multiset multiplicities.

`associatedClass` recovers the published association with the actual full
cuspidal isomorphism class. `weil_degree` applies degree to the exact expansion,
uses unchanged restriction rank, and then uses the association's rank equality.
`automorphic_degree` uses the actual support's group-rank degree law.
`degrees_eq` therefore identifies the two degrees, and
`automorphic_effective` recovers nonnegative support coefficients.

## Actual generated images

`pairedLattice` is the integral span of the pairs from **all** witnessed
generators at the fixed relative level and place. `weilImage` and
`automorphicImage` are the two integral generated spans. These specialize the
published `generatedPairs` and `generated` constructions with the actual
witnessed-object index. The three generator membership lemmas follow directly
from membership in integral span.

`weilProjection` and `automorphicProjection` reuse the published projections
into those generated spans. For each span element, integral-span induction
constructs a partner in the paired lattice; generators, zero, sums and integer
multiples supply the four cases. The two projection surjectivity theorems
therefore identify the named images as the projection images of the paired
lattice. This surjectivity is onto these generated submodules.

`degrees_eq_of_mem` extends equality of generator degrees to every signed
integral pair by the same span induction and linearity. It does not assert that
arbitrary signed elements remain effective.

## Scope

No generator, presentation, local map, unitary exact expansion or unitary
supercuspidal support is asserted to exist. The construction makes no choice
among witnesses, and it does not prove that different expansions, local maps or
factor families give the same lattice element. The index includes all supplied
witnesses. The full local factors can be reducible on the Weil side and
nonsupercuspidal on the automorphic side.

Absolute global Weil groups, finite/absolute comparisons, global automorphic
unitarity, local support existence and uniqueness, expansion existence and
uniqueness, isometry, injectivity of either projection, spanning of either
ambient lattice and a correspondence between them remain separate obligations.
In particular, this contribution does not complete the absolute-global scope
of Henniart's section 2.5.
