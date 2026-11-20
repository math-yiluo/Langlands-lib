# Hopf spectrum points for the Cartier pairing

For a relative spectrum over `Spec R`, the relative spectrum adjunction
identifies morphisms into it with `R`-algebra maps into the actual
global sections of the test scheme. The adjunction supplies the
compatibility with pullback of a test and with postcomposition by a
map of spectra. `sectionsSpec` identifies the relative global sections
of a spectrum with its coordinate algebra via `ΓSpecIso`. The
commutation with the scalar action follows from naturality for the
structure map.

For a Hopf spectrum, `specPoints` is the multiplicative equivalence
between its points and convolution algebra maps. The inverse is given
by first mapping to the spectrum of the test scheme's relative global
sections and then using the affine comparison `Spec.mapMulEquiv`.
Precomposition by the adjunction unit preserves multiplication.

`specGroup` packages the spectrum of a cocommutative Hopf algebra as
a commutative group scheme. Conversely, for an actual commutative
affine group scheme, the two tensor inclusions determine commuting
points. The affine coordinate isomorphism and the tensor-inclusion
criterion then give cocommutativity of its coordinate Hopf algebra.

These are internal comparisons for applying the algebraic Cartier
pairing to actual scheme points. The use of affine Hopf coordinates
follows the construction in Demazure and Gabriel, *Groupes algébriques*,
Tome I (1970), Chapter II, §1, no. 2, 2.10(a), printed pp. 156–157.
