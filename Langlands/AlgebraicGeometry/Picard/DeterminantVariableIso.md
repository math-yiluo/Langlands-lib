# Variable-rank determinant maps under module-sheaf isomorphisms

This derived construction transports actual finite local frames along an
isomorphism of module sheaves on an arbitrary scheme. Each frame retains its
supplied finite rank, and ranks may vary within and between the source and
target covering families. The scheme and cover index types share universe u.

`mixedUnit_map` proves invariance of the mixed finite-basis determinant under a
linear equivalence. It applies coordinate compatibility for the identity ring
map. The actual section bases of `mapFrames` are the images of the original
bases under the linear equivalence induced on sections by the sheaf
isomorphism. Thus their determinant cocycle is unchanged.

`mapFramesIso` identifies the determinant sheaf with its transported-frame
presentation and preserves the local determinant generators. Composing it
with the variable-rank cover comparison gives `isoMap`, an actual isomorphism
of determinant sheaves for the two supplied covering frame systems.

On any open contained in a source and a target chart, the source generator
maps to `isoUnit` times the target generator. This unit is the mixed
determinant expressing the transported source basis in the target basis.
The mixed determinant composition law, together with invariance under
transport of bases, proves multiplication of these coefficients under
composition of module-sheaf isomorphisms. Unequal ranks on an overlap force
the section ring to be trivial, as in the imported mixed determinant API.

Identity and composition of `isoMap` hold as equalities of actual sheaf
isomorphisms. Identity follows on the chart generators. Composition follows
on the triple-intersection cover using local scalar generation, linearity
and multiplication of the mixed determinant units. `lineBundleIsoMap` lifts
the construction and both laws to the full subcategory of actual locally
free rank-one sheaves.

The proof adapts the imported fixed-rank determinant-map construction using
actual local section bases and mixed finite-basis determinants. The frame
systems and their covering property are inputs. Existence of finite frames,
pullback comparisons, a parabolic Lie polarization and its ampleness remain
separate obligations.
