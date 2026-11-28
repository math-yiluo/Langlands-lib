# Reducing a geometric trace expansion to one rational class

`SingleOrbitGeometricTraceStatement` considers a finite list of
distinct rational twisted classes in a geometric trace expansion
with a left-invariant ambient group measure.
The list covers all rational orbits with a nonzero test value. The
support hypothesis forces every such orbit into one specified
rational class. The expansion applies to every choice of compatible
measures for the listed terms, with finite rational centralizer
covolumes. Compatible measures for the specified representative
are supplied.

The theorem identifies the trace with the covolume times the
orbital integral at the specified representative. If that orbital
integral is nonzero, the specified covolume is finite. The proof
uses left invariance to transport the chosen measures to a listed
representative of the same rational class. Every other weighted term vanishes by the
support hypothesis. If the specified orbital integral vanishes,
all listed weighted terms vanish. If it is nonzero, the coverage
property supplies the representative and the distinctness condition
makes it unique.

An auxiliary theorem constructs both compatible measures for
a closed commutative twisted centralizer and a discrete rational
subgroup. It uses the given two-sided ambient Haar, Haar measure on
the centralizer, and counting measure on the rational intersection.

This internal step implements the finite sum reduction in
Arthur–Clozel, Chapter 1, p. 46, and Henniart–Lemaire, I.6.8,
pp. 49–50 (PDF pp. 57–58), and works with the ordinary or twisted
geometric expansion in the Library.

`exists_twistedOrbit_ne_zero_of_twistedOrbitalIntegral_ne_zero` gives an orbit representative where the test is nonzero.
