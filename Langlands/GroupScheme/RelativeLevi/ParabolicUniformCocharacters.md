# One finite exponent family of standard cocharacters on every field fibre

This internal existence lemma supplies finitely many fixed integer exponent
vectors for a coordinate split torus in a reductive group over a ring. It assumes
fibrewise maximality, a fibrewise full coordinate root datum, and one reference
field algebra. The finite index type and exponent vectors are chosen before
quantifying over all further field algebras.

On the reference fibre, the proof chooses a generic cocharacter and one standard
cocharacter for each subset of its simple relative roots, using the published
field existence theorem `standardCocharacter`. Finiteness of the simple roots
gives finiteness of the index type. Each chosen cocharacter is recorded by its
full integral coordinate vector.

On any other field fibre, `fibreParabolicRootLatticeComparison` transports the
generic cocharacter, identifies every simple-root subset, and preserves the
standard-cocharacter conditions. Its coordinate identity identifies the
transported chosen cocharacters with the same fixed exponent vectors. The
generic cocharacter and the face equivalence may depend on the field; the finite
family of vectors does not. This is derived from published field structure and
the supplied fibrewise data, and does not assume a relative parabolic moduli
scheme.

`UniformStandardCocharacterFamily` packages the finite index type, its `Fintype`,
the fixed exponent vectors, and the complete fieldwise standard-face
specification. `uniformStandardCocharacterFamily` chooses such a record from the
existence lemma. The record retains the quantifier order: the vectors are fixed
before any further field algebra is supplied. This internal data construction
is used to build actual dynamic parabolic models over the base ring.
