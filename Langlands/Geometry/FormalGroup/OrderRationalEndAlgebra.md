# Actual rational full-order endomorphism algebra and its units

This internal construction uses the existing ring of actual rational formal
endomorphisms commuting with a specified order action. It gives that ring its
rational scalar algebra structure and identifies its units with the existing
actual full-order quasi-isogenies from the module to itself.

Let `O` be a commutative ring, `D` an `O`-algebra, `R` a commutative
`O`-algebra, `M` a finite-coordinate formal `O`-module over `R`, and `E` an
actual `D`-action on `M`. Let `F` be a field with an `O`-algebra structure.
`RationalHom F E E` is the existing submodule of the actual tensor formal Hom
whose maps commute with every acting order element. Its existing ring product
is actual functional composition.

The `Algebra F` instance is constructed from its existing `F`-module and ring
structures using bilinearity of actual rational composition. The two
bilinearity equations show that scalar multiplication commutes with both
composition arguments. `algebraMap_eq_smul_id` identifies the scalar map with
`a ↦ a • id E`; these are actual scalar tensor endomorphisms.

`RationalHom.mapEnd` packages the existing actual coefficient-extension map as
an `F`-algebra homomorphism for an arbitrary supplied coefficient algebra map.
The ring laws are the existing preservation of identity and composition, and
compatibility with the scalar map follows by linearity and preservation of the
actual identity.

For the quasi-isogeny constructions, `O` is a domain and `F` its fraction field.
`QuasiIsogeny.ofUnit` retains the actual forward and inverse rational maps of a
unit of this endomorphism ring. The unit equations give the two original
quasi-isogeny inverse equations. `toUnit` reverses this construction.
`unitEquiv` proves that these constructions are inverse, using unit
extensionality and uniqueness of the actual quasi-isogeny inverse.

`ofUnit_mul` exposes the composition convention: the unit product `a*b` first
applies `b`, then `a`, so it corresponds to `(ofUnit b).trans (ofUnit a)`.
The identity and inverse lemmas retain the specified actual maps. `ofUnit_map`
shows that extending both rational inverse maps agrees with mapping the unit
through the actual coefficient algebra homomorphism.

The provenance is internal algebraic infrastructure for using a chosen matrix
identification of an actual formal frame's rational endomorphisms. No matrix
identification or existence theorem, determinant/height formula, Frobenius
comparison, or action on height-zero framed representatives is claimed here.
