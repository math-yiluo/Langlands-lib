# Proper coherent cohomology from actual alternating Čech complexes

`properCoherentCohomologyFinite` proves the complete proposition
`ProperCoherentCohomologyFiniteStatement` over every noetherian commutative
ring in the stated universe.

Properness makes the source quasi-compact and separated over the affine base.
Choose its finite ordered affine cover `𝒰`. The presheaf
`OModulePresheaf.ofModules f M` has the actual sections of `M`, with the
`R` action induced by `f`. The finite-affine-section hypothesis gives its
`IsCoherent` condition. Mathlib quasi-coherence gives its localization
condition: sections on a basic open lift after multiplying by a power of the
defining function, and a section restricting to zero is killed by such a
power. The proof rewrites restriction of that power using `map_pow`.

The published `OModulePresheaf.cechFinite_of_isProper` gives finite zeroth
Čech cocycles and finite positive-degree Čech cohomology. For each positive
degree, the private comparison `cechHomologySuccEquiv` identifies the actual
cochain-complex homology with that quotient of cocycles by coboundaries. It
uses an explicit short complex of module linear maps and the range of a
codomain-restricted differential. In degree zero, the concrete homology is
a quotient of the finite zeroth cocycle module and is therefore finite.
The published `CechResolution.cechCohomologyIso` transports finiteness to
the actual right-derived relative cohomology.

For eventual vanishing, use the cardinality of the finite cover as a bound.
At degree `n` at least that cardinality there is no strictly increasing map
`Fin (n+1) → 𝒰.ι`, so the alternating cochain module is zero. Its homology
is zero, and the same comparison transports this to actual cohomology.

This is derived content from the published proper Čech finiteness theorem,
the actual Čech-to-derived comparison, and elementary homology of modules.
The finite-generation conclusion agrees with Stacks Project Lemma 30.19.2
(tag [02O6](https://stacks.math.columbia.edu/tag/02O6)); the statement's
paired Markdown gives its retained source locator. No geometric numerical
degree formula is used or asserted.
