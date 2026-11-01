# Locally constant descent from actual representing spectra

Worker 56 constructs locally constant functions on an actual represented
affinoid locus from functions on its representing spectra. All structural
maps and topologies are those of the imported domain implementation.

`Domain.spectrumLocallyConstantEquiv` applies quotient descent to the
original `spectrumToLocus`. Its upstairs subtype includes the complete
fiber equation. This retains possible noninjectivity of the structural
map.

For a finite actual domain cover, the input is a locally constant function
on every component's entire representing spectrum. Compatibility requires
equal values whenever two component-spectrum points have equal images in
the target represented locus. The condition also applies to two points in
one component. It supplies the missing within-component descent condition
as well as agreement between components.

`spectrumLocallyConstantFamily` assembles these functions on the disjoint
union. The sigma topology proves local constancy directly from local
constancy on each component. `spectrumLocallyConstantGlue` descends this
assembled function along the original finite-cover quotient `totalMap`.
Its evaluation formula recovers every input value.
`spectrumLocallyConstantEquiv` packages restriction and gluing with their
proved inverse laws.

The coefficient set is arbitrary and has an independent universe. Empty
spectra, empty covers of empty loci, positive polyradii, nilpotent quotient
algebras and trivial valuations remain allowed as in the imported
implementation.

This internal construction derives from the already proved actual quotient
topologies and the generic locally constant quotient descent in its paired
helper. Unlike the existing continuous-map gluing interface, its input is
given directly on spectra and includes all quotient-fiber equations. It
provides topological constant-coefficient data; no analytic structure
sheaf, analytic étale site or cohomology comparison is constructed here.
