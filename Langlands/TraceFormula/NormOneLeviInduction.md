# Normalized induction from the discrete spectrum of a coordinate Levi

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989), II §9, printed pp. 131–132, defines the induced space
`ρ_{Q,t}` in (9.2) using the discrete automorphic spectrum of the norm-one Levi
and the norm of the imaginary part of the induced infinitesimal character.
The same slice is used in III (4.1)–(4.2), printed p. 203.

`NormOneLeviInduction.Model` uses the actual coordinate block parabolic and
Levi and the compact picture of `AdelicSpectralTransformSpaces`. Its measure
uses a compact Haar probability, the Levi Haar measure compatible with Iwasawa
integration, and a nonnegative cutoff of integral one in the split-component
coordinates. `leviDiscrete` takes the discrete part of the actual right
regular representation on the quotient by the positive split component and
the rational points of the Levi. A normalized restriction has the
inverse half modulus multiplying `φ(mg)`. `IsSectionWithSupport` requires
that restriction to represent a vector in the specified Levi subspace for
every `g`, along with the square-integrable automorphic section conditions.

`HasImaginaryInfinitesimalNorm` requires the same scalar action of the
enveloping centre on each smooth archimedean slice of the actual induced
section. The Harish-Chandra parameter of the highest-weight character is
the weight plus the upper triangular half sum of roots. Subtracting the
mean removes the positive split-centre line on the imaginary part. The
squared norm is averaged over the complex embeddings, counting both
embeddings at a complex place. This makes the diagonal repetition of
embeddings under field extension isometric. The centre action uses the
existing archimedean differential operators on smooth functions.

`hilbertSliceWithSupport` closes the span of represented sections of the
given support and norm. `hilbertSlice` uses the entire actual discrete
Levi spectrum. The same ambient Hilbert space is used for the Library's
imaginary intertwining operators. The Hilbert models here use the field
universe of the existing canonical `L²` construction.
